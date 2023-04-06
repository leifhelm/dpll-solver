const std = @import("std");
const Allocator = std.mem.Allocator;
const ArenaAllocator = std.heap.ArenaAllocator;
const ArrayList = std.ArrayList;
const math = std.math;

pub const Error = error{ InvalidLiteral, TooManyVariables };

const not = Literal.not;

pub const Literal = struct {
    const Self = @This();

    val: isize,

    pub fn not(self: Self) Self {
        return Self{ .val = -self.val };
    }

    pub fn variable(self: Self) Variable {
        return Variable{
            .val = @intCast(usize, math.absInt(self.val) catch unreachable),
        };
    }

    fn index(self: Self) usize {
        return self.variable().val - 1;
    }

    fn isValid(self: Self, variables: usize) bool {
        if (self.val > variables) return false;
        if (self.val < -@intCast(isize, variables)) return false;
        if (self.val == 0) return false;
        return true;
    }

    pub fn isSameVariable(a: Self, b: Self) bool {
        return a.variable().eql(b.variable());
    }

    pub fn isPos(self: Self) bool {
        return self.val > 0;
    }

    pub fn isNeg(self: Self) bool {
        return self.val < 0;
    }

    pub fn eql(a: Self, b: Self) bool {
        return a.val == b.val;
    }

    pub fn format(
        self: Self,
        comptime fmt: []const u8,
        options: std.fmt.FormatOptions,
        writer: anytype,
    ) !void {
        _ = fmt;
        _ = options;

        if (self.isPos()) {
            try writer.print(" {}", .{self.val});
        } else {
            try writer.print("¬{}", .{-self.val});
        }
    }
};

pub const Variable = struct {
    const Self = @This();

    val: usize,

    pub fn fromIndex(idx: usize) Self {
        return Self{ .val = idx + 1 };
    }

    pub fn index(self: Self) usize {
        return self.val - 1;
    }

    pub fn eql(a: Self, b: Self) bool {
        return a.val == b.val;
    }

    pub fn pos(self: Self) Literal {
        return Literal{ .val = @intCast(isize, self.val) };
    }
    pub fn neg(self: Self) Literal {
        return not(self.pos());
    }
};

pub const ConstClause = []const Literal;

pub const Clause = struct {
    const Self = @This();

    literals: []Literal,

    pub fn initEmpty(allocator: Allocator, size: usize) error{OutOfMemory}!Self {
        return Self{
            .literals = try allocator.alloc(Literal, size),
        };
    }

    pub fn fromSlice(allocator: Allocator, variables: usize, const_clause: ConstClause) (Error || error{OutOfMemory})!Self {
        if (variables > math.maxInt(isize)) return Error.TooManyVariables;
        for (const_clause) |literal| {
            if (!literal.isValid(variables)) return Error.InvalidLiteral;
        }
        return Self.fromSliceUnchecked(allocator, const_clause);
    }

    pub fn fromSliceUnchecked(allocator: Allocator, const_clause: ConstClause) error{OutOfMemory}!Self {
        return Self{
            .literals = try allocator.dupe(Literal, const_clause),
        };
    }

    fn unit(self: Self) ?Literal {
        if (self.literals.len == 1) {
            return self.literals[0];
        } else {
            return null;
        }
    }

    fn eliminateLiteral(self: Self, literal: Literal, allocator: Allocator) error{OutOfMemory}!?Self {
        std.debug.assert(literal.val != 0);

        var size: usize = 0;
        for (self.literals) |other_literal| {
            if (!literal.isSameVariable(other_literal)) {
                size += 1;
            } else if (other_literal.eql(literal)) {
                return null;
            }
        }

        var new = try allocator.alloc(Literal, size);
        errdefer allocator.free(new);

        var index: usize = 0;
        for (self.literals) |other_literal| {
            if (!literal.isSameVariable(other_literal)) {
                new[index] = other_literal;
                index += 1;
            }
        }
        return Self{
            .literals = new,
        };
    }
};

const LiteralState = enum { None, Pos, Neg, Both };

const Step = struct {
    const Self = @This();

    clauses: ArrayList(Clause),
    decision_level: usize,
    freely_chosen: bool,
    decision: ?Literal,
    arena: ArenaAllocator,

    pub fn init(constraints: Constraints) Self {
        return Self{
            .clauses = constraints.clauses,
            .decision_level = 0,
            .decision = null,
            .freely_chosen = false,
            .arena = constraints.arena,
        };
    }

    pub fn deinit(self: Self) void {
        self.clauses.deinit();
        self.arena.deinit();
    }

    fn unitPropagation(self: Self) ?Literal {
        // std.debug.print("unit propagation\n", .{});
        for (self.clauses.items) |clause| {
            if (clause.unit()) |unit| {
                return unit;
            }
        }
        return null;
    }

    fn pureLiteral(self: Self, pure_literal_state: []LiteralState) ?Literal {
        // std.debug.print("pure literal\n", .{});
        for (pure_literal_state) |*literal_state| {
            literal_state.* = .None;
        }
        for (self.clauses.items) |clause| {
            for (clause.literals) |literal| {
                const literal_state = &pure_literal_state[literal.index()];
                const new_state = if (literal.isPos()) LiteralState.Pos else LiteralState.Neg;
                if (literal_state.* == .None) {
                    literal_state.* = new_state;
                } else if (new_state != literal_state.*) {
                    literal_state.* = .Both;
                }
            }
        }
        for (pure_literal_state) |literal_state, index| {
            const variable = Variable.fromIndex(index);
            if (literal_state == .Pos) {
                return variable.pos();
            } else if (literal_state == .Neg) {
                return variable.neg();
            }
        }
        return null;
    }

    fn isSat(self: Self) ?Result {
        if (self.clauses.items.len == 0) return .Sat;
        for (self.clauses.items) |clause| {
            if (clause.literals.len == 0) return .Unsat;
        }
        return null;
    }

    fn eliminateLiteral(self: Self, literal: Literal, freely_chosen: bool) error{OutOfMemory}!Self {
        // std.debug.print("eliminate: {}, freely_chosen: {}\n", .{ literal, freely_chosen });
        var clauses = ArrayList(Clause).init(self.clauses.allocator);
        errdefer clauses.deinit();
        var arena = ArenaAllocator.init(self.clauses.allocator);
        errdefer arena.deinit();

        for (self.clauses.items) |clause| {
            if (try clause.eliminateLiteral(literal, arena.allocator())) |new_clause| {
                try clauses.append(new_clause);
            }
        }
        return Self{
            .clauses = clauses,
            .decision = literal,
            .decision_level = if (freely_chosen) self.decision_level + 1 else self.decision_level,
            .freely_chosen = freely_chosen,
            .arena = arena,
        };
    }
};

pub const Result = enum { Sat, Unsat };

pub const Constraints = struct {
    const Self = @This();
    clauses: ArrayList(Clause),
    variables: usize,
    arena: ArenaAllocator,

    pub fn init(allocator: Allocator) Self {
        return Self{
            .clauses = ArrayList(Clause).init(allocator),
            .variables = 0,
            .arena = ArenaAllocator.init(allocator),
        };
    }

    pub fn fromSlice(allocator: Allocator, variables: usize, clauses: []const []const isize) (Error || error{OutOfMemory})!Self {
        var self = Self.init(allocator);
        errdefer self.deinit();
        try self.clauses.ensureTotalCapacityPrecise(clauses.len);
        self.variables = variables;

        for (clauses) |clause| {
            try self.add(@ptrCast([]const Literal, clause));
        }
        return self;
    }

    pub fn deinit(self: Self) void {
        self.clauses.deinit();
        self.arena.deinit();
    }

    pub fn add(self: *Self, const_clause: []const Literal) (Error || error{OutOfMemory})!void {
        const clause = try Clause.fromSlice(self.arena.allocator(), self.variables, const_clause);
        try self.clauses.append(clause);
    }

    pub fn addClause(self: *Self, clause: Clause) error{OutOfMemory}!void {
        try self.clauses.append(clause);
    }

    pub fn newLiteral(self: *Self) Literal {
        self.variables += 1;
        return (Variable{ .val = self.variables }).pos();
    }
};

pub const DpllSolver = struct {
    const Self = @This();

    steps: ArrayList(Step),
    variables: usize,
    used_variables: ArrayList(bool),
    pure_literal_state: ArrayList(LiteralState),

    pub fn init(allocator: Allocator, constraints: Constraints) (error{OutOfMemory})!Self {
        errdefer constraints.deinit();

        var steps = ArrayList(Step).init(allocator);
        errdefer steps.deinit();

        const step = Step.init(constraints);
        errdefer step.deinit();
        try steps.append(step);

        var pure_literal_state = ArrayList(LiteralState).init(allocator);
        errdefer pure_literal_state.deinit();
        try pure_literal_state.appendNTimes(.None, constraints.variables);

        var used_variables = ArrayList(bool).init(allocator);
        errdefer used_variables.deinit();
        try used_variables.appendNTimes(false, constraints.variables);

        return Self{
            .steps = steps,
            .variables = constraints.variables,
            .used_variables = used_variables,
            .pure_literal_state = pure_literal_state,
        };
    }

    pub fn deinit(self: Self) void {
        for (self.steps.items) |step| {
            step.deinit();
        }
        self.steps.deinit();
        self.pure_literal_state.deinit();
        self.used_variables.deinit();
    }

    pub fn solve(self: *Self) error{OutOfMemory}!ModelResult {
        while (self.steps.items.len > 0) {
            const last_step = self.lastStep();

            // std.debug.print("decision level: {}\n", .{last_step.decision_level});

            // for (self.steps.items) |step| {
            //     if (step.decision) |literal| {
            // std.debug.print("{} ", .{literal});
            //     }
            // }
            // std.debug.print("\n", .{});
            // for (last_step.clauses.items) |clause| {
            // std.debug.print("{any}\n", .{clause.literals.items});
            // }
            // std.debug.print("\n", .{});

            if (last_step.isSat()) |result| {
                if (result == .Sat) {
                    return .{ .Sat = try Model.fromSteps(
                        self.steps.allocator,
                        self.variables,
                        self.steps.items,
                    ) };
                } else if (result == .Unsat and last_step.decision_level == 0) {
                    return .Unsat;
                }
                try self.backtrack();
                continue;
            }
            if (last_step.unitPropagation()) |literal| {
                try self.steps.append(try last_step.eliminateLiteral(literal, false));
            } else if (last_step.pureLiteral(self.pure_literal_state.items)) |literal| {
                try self.steps.append(try last_step.eliminateLiteral(literal, false));
            } else {
                const literal = self.chooseLiteral();
                try self.steps.append(try last_step.eliminateLiteral(literal, true));
            }
        }
        return .Unsat;
    }

    // pub fn add(self: *Self, clause: [] const ConstClause) void {
    // self.steps[0].
    // }

    fn chooseLiteral(self: *Self) Literal {
        for (self.used_variables.items) |*used| {
            used.* = false;
        }
        for (self.steps.items) |step| {
            if (step.decision) |literal| {
                self.used_variables.items[literal.index()] = true;
            }
        }
        for (self.used_variables.items) |used, index| {
            if (!used) {
                return Variable.fromIndex(index).pos();
            }
        }
        unreachable;
    }

    fn backtrack(self: *Self) error{OutOfMemory}!void {
        while (self.steps.popOrNull()) |last_step| {
            defer last_step.deinit();
            if (last_step.freely_chosen and last_step.decision.?.isPos()) {
                try self.steps.append(try self.lastStep().eliminateLiteral(not(last_step.decision.?), true));
                return;
            }
        }
    }

    fn lastStep(self: Self) Step {
        return self.steps.items[self.steps.items.len - 1];
    }
};

pub const Model = struct {
    const Self = @This();

    assignments: ArrayList(bool),

    fn fromSteps(allocator: Allocator, variables: usize, steps: []const Step) error{OutOfMemory}!Self {
        var assignments = ArrayList(bool).init(allocator);
        errdefer assignments.deinit();
        try assignments.appendNTimes(false, variables);
        for (steps) |step| {
            if (step.decision) |literal| {
                assignments.items[literal.index()] = literal.isPos();
            }
        }
        return Self{ .assignments = assignments };
    }

    pub fn deinit(self: Self) void {
        self.assignments.deinit();
    }

    pub fn getAssignment(self: Self, variable: Variable) bool {
        return self.assignments.items[variable.index()];
    }
};

pub const ModelResult = union(Result) {
    const Self = @This();

    Sat: Model,
    Unsat,

    pub fn deinit(self: Self) void {
        switch (self) {
            .Unsat => {},
            .Sat => |model| model.deinit(),
        }
    }
};

const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const test_allocator = std.testing.allocator;

test "isSameVariable" {
    const a = Literal{ .val = 1 };
    const not_a = Literal{ .val = -1 };
    try expect(a.isSameVariable(not_a));
    try expect(a.isSameVariable(a));
    try expect(not_a.isSameVariable(a));
}

test "init deinit" {
    const constraints = try Constraints.fromSlice(test_allocator, 5, &[_][]const isize{
        &[_]isize{ -1, 2 },
        &[_]isize{ -2, 3 },
        &[_]isize{ -3, 4 },
        &[_]isize{ -4, 5 },
        &[_]isize{ -5, -1 },
    });
    var solver = try DpllSolver.init(test_allocator, constraints);
    defer solver.deinit();
}

test "simple sat" {
    const constraints = try Constraints.fromSlice(test_allocator, 5, &[_][]const isize{
        &[_]isize{ -1, 2 },
        &[_]isize{ -2, 3 },
        &[_]isize{ -3, 4 },
        &[_]isize{ -4, 5 },
        &[_]isize{ -5, -1 },
    });
    var solver = try DpllSolver.init(test_allocator, constraints);
    defer solver.deinit();
    const model_result = try solver.solve();
    defer model_result.deinit();
    try expectEqual(Result.Sat, model_result);
}

test "simple unsat" {
    const constraints = blk: {
        var constraints = Constraints.init(test_allocator);
        errdefer constraints.deinit();

        const a = constraints.newLiteral();
        const b = constraints.newLiteral();
        const c = constraints.newLiteral();
        const d = constraints.newLiteral();
        const e = constraints.newLiteral();

        try constraints.add(&[_]Literal{ not(a), not(b) });
        try constraints.add(&[_]Literal{ a, c });
        try constraints.add(&[_]Literal{ b, not(c) });
        try constraints.add(&[_]Literal{ not(b), d });
        try constraints.add(&[_]Literal{ not(c), not(d) });
        try constraints.add(&[_]Literal{ c, e });
        try constraints.add(&[_]Literal{ c, not(e) });

        break :blk constraints;
    };
    var solver = try DpllSolver.init(test_allocator, constraints);
    defer solver.deinit();
    const model_result = try solver.solve();
    defer model_result.deinit();
    try expectEqual(Result.Unsat, model_result);
}
