const std = @import("std");
const Allocator = std.mem.Allocator;
const exit = std.os.exit;

const constraint_solver = @import("solver").constraint_solver;
const ConstraintSolver = constraint_solver.ConstraintSolver;
const Var = constraint_solver.Var;
const Model = constraint_solver.Model;

pub fn main() !void {
    var stderr = std.io.getStdErr().writer();
    var gpa = std.heap.GeneralPurposeAllocator(.{}){};
    const allocator = gpa.allocator();
    defer {
        const leaked = gpa.deinit();
        if (leaked) {
            stderr.writeAll("LEAKED MEMORY\n") catch {};
            exit(199);
        }
    }

    var stdin_br = std.io.bufferedReader(std.io.getStdIn().reader());
    const reader = stdin_br.reader();
    const sudoku = parseSudoku(reader) catch {
        try stderr.writeAll("Could not parse Sudoku.\n");
        exit(65);
    };
    try solveSudoku(allocator, sudoku);
}

const Sudoku = [9][9]?u4;

const SudokuVars = [9][9]Var;

fn parseSudoku(reader: anytype) !Sudoku {
    var sudoku: Sudoku = undefined;
    var y: usize = 0;
    while (y < 9) : (y += 1) {
        var x: usize = 0;
        while (x < 9) : (x += 1) {
            const char = try reader.readByte();
            if (char >= '1' and char <= '9') {
                sudoku[y][x] = @intCast(u4, char - '0');
            } else if (char == '.') {
                sudoku[y][x] = null;
            } else {
                std.debug.print("x: {}, y: {}\n", .{ x, y });
                return error.InvalidChar;
            }
        }
        if (try reader.readByte() != '\n') {
            return error.InvalidChar;
        }
    }
    return sudoku;
}

fn solveSudoku(allocator: Allocator, sudoku: Sudoku) !void {
    var solver = ConstraintSolver.init(allocator);
    defer solver.deinit();
    const vars = try createSudokuVariables(&solver);
    _ = sudoku;
    // var y: usize = 0;
    // while (y < 9) : (y += 1) {
    //     var x: usize = 0;
    //     while (x < 9) : (x += 1) {
    //         if (sudoku[y][x]) |value| {
    //             try solver.equalToConstant(vars[y][x], value);
    //         }
    //     }
    // }

    std.debug.print("{} constraints\n", .{solver.constraints.clauses.items.len});
    const model_result = try solver.solve();
    defer model_result.deinit();
    var stdout_bw = std.io.bufferedWriter(std.io.getStdOut().writer());
    const stdout = stdout_bw.writer();
    defer stdout_bw.flush() catch {};
    switch (model_result) {
        .Unsat => {
            try stdout.writeAll("Unsolveable\n");
            exit(1);
        },
        .Sat => |model| try printSolution(model, vars, stdout),
    }
}

fn createSudokuVariables(solver: *ConstraintSolver) !SudokuVars {
    var vars: SudokuVars = undefined;
    var y: usize = 0;
    while (y < 9) : (y += 1) {
        var x: usize = 0;
        while (x < 9) : (x += 1) {
            vars[y][x] = try solver.newVariable(1, 9);
        }
    }

    y = 0;
    while (y < 9) : (y += 1) {
        try solver.distinct(&vars[y]);
    }

    var x: usize = 0;
    while (x < 9) : (x += 1) {
        try solver.distinct(&[_]Var{
            vars[0][x],
            vars[1][x],
            vars[2][x],
            vars[3][x],
            vars[4][x],
            vars[5][x],
            vars[6][x],
            vars[7][x],
            vars[8][x],
        });
    }

    y = 0;
    while (y < 9) : (y += 3) {
        x = 0;
        while (x < 9) : (x += 3) {
            try solver.distinct(&[_]Var{
                vars[y + 0][x + 0],
                vars[y + 0][x + 1],
                vars[y + 0][x + 2],
                vars[y + 1][x + 0],
                vars[y + 1][x + 1],
                vars[y + 1][x + 2],
                vars[y + 2][x + 0],
                vars[y + 2][x + 1],
                vars[y + 2][x + 2],
            });
        }
    }

    return vars;
}

fn printSolution(model: Model, vars: SudokuVars, writer: anytype) !void {
    var y: usize = 0;
    while (y < 9) : (y += 1) {
        var x: usize = 0;
        while (x < 9) : (x += 1) {
            try writer.print("{}", .{model.getValue(vars[y][x])});
        }
        try writer.writeAll("\n");
    }
}
