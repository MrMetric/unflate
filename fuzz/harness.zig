//! C ABI over the optimizer entry points for fuzz/driver.c. The driver owns
//! input selection and the independent output checks; this file only calls
//! the optimizer. Safety checks and assertions stay on (ReleaseSafe), so an
//! internal invariant failure panics and aborts the process.
const std = @import("std");
const deflopt = @import("deflopt");

export fn unflate_fuzz_configure(fast: c_int, min_dist_codes: c_int) void {
	_ = deflopt.swapReparse(fast == 0);
	_ = deflopt.swapMinDistCodes(@intCast(min_dist_codes));
}

/// Optimize a raw DEFLATE stream. Returns the output length, -1 when the
/// optimizer rejects the input, or -2 when the output exceeds `cap`.
export fn unflate_fuzz_deflate(in: [*]const u8, len: usize, out: [*]u8, cap: usize) i64 {
	var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer arena.deinit();
	const result = deflopt.optimizeDeflateBytes(arena.allocator(), in[0..len]) catch return -1;
	if (result.len > cap) return -2;
	@memcpy(out[0..result.len], result);
	return @intCast(result.len);
}

/// Optimize a container: 1 gzip, 2 PNG, 3 ZIP. Returns the optimizer's own
/// result: the output length, or negative on rejection. A length above `cap`
/// means the output was not copied.
export fn unflate_fuzz_container(kind: c_int, in: [*]const u8, len: usize, out: [*]u8, cap: usize) i64 {
	const data = in[0..len];
	const dest = out[0..cap];
	return switch (kind) {
		1 => deflopt.optimizeGzip(data, dest),
		2 => deflopt.optimizePng(data, dest),
		3 => deflopt.optimizeZip(data, dest),
		else => @panic("unknown container kind"),
	};
}
