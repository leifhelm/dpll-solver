const std = @import("std");
const Allocator = std.mem.Allocator;
const ArenaAllocator = std.heap.ArenaAllocator;

const dpll = @import("dpll.zig");
const not = dpll.Literal.not;
const Result = dpll.Result;

pub const Error = error{ InvalidRange, InvalidSort, InvalidConstant };

pub const Var = *const Variable;

pub const Variable = struct {
    const Self = @This();

    values: []const dpll.Literal,
    offset: isize,
};

pub const ConstraintSolver = struct {
    const Self = @This();

    constraints: dpll.Constraints,
    variable_arena: ArenaAllocator,

    pub fn init(allocator: Allocator) Self {
        return Self{
            .constraints = dpll.Constraints.init(allocator),
            .variable_arena = ArenaAllocator.init(allocator),
        };
    }

    pub fn deinit(self: Self) void {
        self.constraints.deinit();
        self.variable_arena.deinit();
    }

    pub fn newVariable(self: *Self, from: isize, to: isize) (Error || dpll.Error || error{OutOfMemory})!*Variable {
        if (from > to) return Error.InvalidRange;
        const allocator = self.variable_arena.allocator();
        const size: usize = @intCast(usize, to - from + 1);
        var values = try allocator.alloc(dpll.Literal, size);
        for (values) |*value| {
            value.* = self.constraints.newLiteral();
        }
        var at_least_one_clause = try dpll.Clause.initEmpty(allocator, size);
        for (values) |value, index| {
            at_least_one_clause.literals[index] = value;
        }
        try self.constraints.addClause(at_least_one_clause);
        for (values) |a, index| {
            for (values[index + 1 ..]) |b| {
                try self.constraints.add(&[_]dpll.Literal{ not(a), not(b) });
            }
        }

        var variable = try allocator.create(Variable);
        variable.values = values;
        variable.offset = from;
        return variable;
    }

    pub fn distinct(self: *Self, variables: []Var) (Error || dpll.Error || error{OutOfMemory})!void {
        if (variables.len == 0) return;
        for (variables[1..]) |variable| {
            if (variable.offset != variables[0].offset or variable.values.len != variables[0].values.len) {
                return Error.InvalidSort;
            }
        }
        for (variables[0].values) |_, value_index| {
            for (variables) |a, index| {
                for (variables[index + 1 ..]) |b| {
                    try self.constraints.add(&[_]dpll.Literal{
                        not(a.values[value_index]), not(b.values[value_index]),
                    });
                }
            }
        }
    }

    pub fn equalToConstant(self: *Self, variable: Var, value: isize) (Error || dpll.Error || error{OutOfMemory})!void {
        if (value < variable.offset or value > variable.offset + @intCast(isize, variable.values.len)) {
            return Error.InvalidConstant;
        }
        const index: usize = @intCast(usize, value - variable.offset);
        try self.constraints.add(&[_]dpll.Literal{variable.values[index]});
    }

    pub fn solve(self: *Self) error{OutOfMemory}!ModelResult {
        const allocator = self.constraints.clauses.allocator;
        defer self.constraints = dpll.Constraints.init(self.constraints.clauses.allocator);
        var solver = try dpll.DpllSolver.init(allocator, self.constraints);
        defer solver.deinit();
        return switch (try solver.solve()) {
            .Unsat => .Unsat,
            .Sat => |model| .{ .Sat = Model{ .model = model } },
        };
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

pub const Model = struct {
    const Self = @This();

    model: dpll.Model,

    pub fn deinit(self: Self) void {
        self.model.deinit();
    }

    pub fn getValue(self: Self, variable: Var) isize {
        const index = blk: for (variable.values) |value, index| {
            if (self.model.getAssignment(value.variable())) {
                break :blk index;
            }
        } else unreachable;
        for (variable.values[index + 1 ..]) |value| {
            std.debug.assert(!self.model.getAssignment(value.variable()));
        }

        return variable.offset + @intCast(isize, index);
    }
};

const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;
const test_allocator = std.testing.allocator;

test "variable" {
    var solver = ConstraintSolver.init(test_allocator);
    defer solver.deinit();

    var a = try solver.newVariable(0, 1);
    const model = (try solver.solve()).Sat;
    defer model.deinit();
    try expectEqual(@as(isize, 0), model.getValue(a));
}

test "distinct sat" {
    var solver = ConstraintSolver.init(test_allocator);
    defer solver.deinit();
    const a = try solver.newVariable(0, 3);
    const b = try solver.newVariable(0, 3);
    const c = try solver.newVariable(0, 3);
    const d = try solver.newVariable(0, 3);
    try solver.distinct(&[_]Var{ a, b, c, d });
    const model = (try solver.solve()).Sat;
    defer model.deinit();
    try expect(model.getValue(a) != model.getValue(b));
    try expect(model.getValue(a) != model.getValue(c));
    try expect(model.getValue(a) != model.getValue(d));
    try expect(model.getValue(b) != model.getValue(c));
    try expect(model.getValue(b) != model.getValue(d));
    try expect(model.getValue(c) != model.getValue(d));
}

test "distinct unsat" {
    var solver = ConstraintSolver.init(test_allocator);
    defer solver.deinit();
    const a = try solver.newVariable(0, 3);
    const b = try solver.newVariable(0, 3);
    const c = try solver.newVariable(0, 3);
    const d = try solver.newVariable(0, 3);
    const e = try solver.newVariable(0, 3);
    try solver.distinct(&[_]Var{ a, b, c, d, e });
    const result = try solver.solve();
    defer result.deinit();
    try expectEqual(Result.Unsat, result);
}
