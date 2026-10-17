//! Small argv cursor for the native CLIs. Callers keep their option policy;
//! this handles spelling, attached values and checked consumption in one place.
const std = @import("std");

pub const Args = struct {
	argv: []const [*:0]const u8,
	current: []const u8 = "",
	options: bool = true,

	pub fn next(self: *Args) ?[]const u8 {
		if (self.argv.len == 0) return null;
		self.current = std.mem.span(self.argv[0]);
		self.argv = self.argv[1..];
		if (self.flag("--")) {
			self.options = false;
			return self.next();
		}
		return self.current;
	}

	pub fn flag(self: Args, name: []const u8) bool {
		return self.options and std.mem.eql(u8, self.current, name);
	}

	/// Match either name, accepting --long=value and -sVALUE as well as a
	/// separate value. An empty short name means there is no short alias.
	pub fn option(self: *Args, long: []const u8, short: []const u8) !?[]const u8 {
		if (!self.options) return null;
		for ([_][]const u8{ long, short }) |name| {
			if (name.len == 0) continue;
			if (self.flag(name)) {
				if (self.argv.len == 0) return error.MissingValue;
				const value = std.mem.span(self.argv[0]);
				self.argv = self.argv[1..];
				return value;
			}
			if (!std.mem.startsWith(u8, self.current, name)) continue;
			const tail = self.current[name.len..];
			if (tail.len == 0) continue;
			if (std.mem.startsWith(u8, name, "--")) {
				if (tail[0] == '=') return tail[1..];
			} else if (name.len == 2 and name[0] == '-') {
				return tail;
			}
		}
		return null;
	}
};

test "values, option boundaries, aliases and positional escape" {
	var args = Args{ .argv = &.{ "--threads=0", "-j4", "-j", "2", "--threadsmith", "--", "-j8" } };
	_ = args.next();
	try std.testing.expectEqualStrings("0", (try args.option("--threads", "-j")).?);
	_ = args.next();
	try std.testing.expectEqualStrings("4", (try args.option("--threads", "-j")).?);
	_ = args.next();
	try std.testing.expectEqualStrings("2", (try args.option("--threads", "-j")).?);
	_ = args.next();
	try std.testing.expectEqual(null, try args.option("--threads", "-j"));
	try std.testing.expectEqualStrings("-j8", args.next().?);
	try std.testing.expectEqual(null, try args.option("--threads", "-j"));
	try std.testing.expectEqual(null, args.next());
	args = .{ .argv = &.{"--threads"} };
	_ = args.next();
	try std.testing.expectError(error.MissingValue, args.option("--threads", "-j"));
}
