const std = @import("std");
const Allocator = std.mem.Allocator;
const ArenaAllocator = std.heap.ArenaAllocator;

const dpll = @import("dpll");

pub const Error = error{InvalidRange};

pub const Variable = struct {
    const Self = @This();

    values: [] const dpll.Literal,
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

    pub fn newVariable(self: *Self, from: isize, to: isize) (Error||error{OutOfMemory})!*Variable {
        if(from > to) return Error.InvalidRange;
        const allocator = self.variable_arena.allocator();
        var variable = Variable{
            .values = try allocator.alloc(dpll.Literal, to - from),
            .offset = from,
        };
        // TODO: One hot encoding.

        return try allocator.create(variable);
    }

    pub fn distinct()
};
