//! C ABI over the optimizer entry points for fuzz/driver.c. The driver owns
//! input selection and the independent output checks; this file only calls
//! the optimizer. Safety checks and assertions stay on (ReleaseSafe), so an
//! internal invariant failure panics and aborts the process.
const std = @import("std");
const containers = @import("containers");
const deflate = containers.deflate;
var options: deflate.Options = .{};

fn rejected(err: anyerror) i64 {
	return switch (err) {
		error.VerificationFailed => @panic("BUG: DEFLATE verification failed"),
		else => -1,
	};
}

export fn unflate_fuzz_configure(fast: c_int, min_dist_codes: c_int) void {
	options.reparse = fast == 0;
	options.min_dist_codes = @intCast(min_dist_codes);
}

/// Optimize a raw DEFLATE stream. Returns the output length, -1 when the
/// optimizer rejects the input, or -2 when the output exceeds `cap`.
export fn unflate_fuzz_deflate(in: [*]const u8, len: usize, out: [*]u8, cap: usize) i64 {
	var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer arena.deinit();
	var buf: std.ArrayList(u8) = .empty;
	buf.ensureTotalCapacity(arena.allocator(), len) catch return -1;
	_ = deflate.optimize(arena.allocator(), &buf, in[0..len], options, .none) catch |err| return rejected(err);
	const result = buf.items;
	if (result.len > cap) return -2;
	@memcpy(out[0..result.len], result);
	return @intCast(result.len);
}

/// Optimize a container: 1 gzip, 2 PNG, 3 ZIP. Returns the optimizer's own
/// result: the output length, or negative on rejection. A length above `cap`
/// means the output was not copied.
export fn unflate_fuzz_container(kind: c_int, in: [*]const u8, len: usize, out: [*]u8, cap: usize) i64 {
	var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer arena.deinit();
	const format: containers.Format = switch (kind) {
		1 => .gzip, 2 => .png, 3 => .zip,
		else => @panic("unknown container kind"),
	};
	const result = containers.optimize(arena.allocator(), format, in[0..len], .{ .stream = options }) catch |err| return rejected(err);
	if (result.len <= cap) @memcpy(out[0..result.len], result);
	return @intCast(result.len);
}
