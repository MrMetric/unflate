const std = @import("std");

fn git(b: *std.Build, args: []const []const u8) ?[]const u8
{
	const argv = std.mem.concat(b.allocator, []const u8, &.{
		&.{ "git", "-C", b.pathFromRoot(".") }, args,
	}) catch @panic("OOM");
	var code: u8 = undefined;
	const output = b.runAllowFail(argv, &code, .ignore) catch return null;
	return std.mem.trim(u8, output, "\r\n");
}

fn identity(b: *std.Build) []const u8
{
	// A source archive inside another checkout must not borrow its identity.
	const prefix = git(b, &.{ "rev-parse", "--show-prefix" }) orelse
		return "unknown (checkout unavailable)";
	if (prefix.len != 0) return "unknown (checkout unavailable)";
	const commit = git(b, &.{ "rev-parse", "--verify", "HEAD" }) orelse "unknown";
	const status = git(b, &.{ "status", "--porcelain", "--untracked-files=normal" }) orelse
		return b.fmt("{s} (checkout state unknown)", .{commit});
	return b.fmt("{s} ({s})", .{ commit, if (status.len == 0) "clean" else "dirty" });
}

pub fn build(b: *std.Build) void
{
	const target = b.standardTargetOptions(.{});
	const optimize = b.option(std.builtin.OptimizeMode, "optimize", "Optimization mode") orelse .ReleaseFast;
	const info = b.addOptions();
	info.addOption([]const u8, "identity", identity(b));

	const module = b.createModule(.{
		.root_source_file = b.path("src/main.zig"),
		.target = target,
		.optimize = optimize,
		.strip = optimize == .ReleaseFast or optimize == .ReleaseSmall,
	});
	module.addOptions("build_info", info);
	b.installArtifact(b.addExecutable(.{ .name = "unflate", .root_module = module }));

	const tests = b.step("test", "Run native contract tests");
	for([_][]const u8{ "src/cli_args.zig", "src/containers.zig" }) |source|
	{
		const test_module = b.createModule(.{
			.root_source_file = b.path(source),
			.target           = target        ,
			.optimize         = .ReleaseSafe  ,
		});
		test_module.addOptions("build_info", info);
		tests.dependOn(&b.addRunArtifact(b.addTest(.{ .root_module = test_module })).step);
	}
}
