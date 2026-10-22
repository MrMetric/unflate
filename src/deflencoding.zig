//! Complete dynamic encodings from token parses and explicit construction choices.
//! Search order, polishing and acceptance belong to callers.
const std = @import("std");
const common = @import("deflcommon.zig");
const deflasm = @import("deflasm.zig");
const A = std.mem.Allocator;
const Block = deflasm.Block;
const Huff = deflasm.Huff;
const Token = deflasm.Token;
const ClEntry = deflasm.ClEntry;
const lenCodeTable = common.lenCodeTable;
const distCodeTable = common.distCodeTable;
const HCLEN_ORDER = common.HCLEN_ORDER;

/// Search estimates omit package-merge; crossing also considers CL repeats
/// across the literal/distance boundary. These choices can change search paths.
pub const Header = enum { greedy, search, full, crossing };
pub const TieOrder = enum { occurrence, symbol };
pub const Length258 = enum { standard, alternate, alternate_unit };
pub const Trees = union(enum) {
	fresh: Length258,
	merge: struct { previous: Huff, order: TieOrder = .occurrence },
};
pub const Request = struct {
	trees: Trees = .{ .fresh = .standard },
	header: Header = .full,
};

/// Configuration and optional exact-result cache, borrowed for the call.
/// Supply an arena for trees and intermediate headers; tokens are borrowed.
pub const Builder = struct {
	floor: u8 = 2,
	extra_seeds: bool = false,
	memo: ?*Memo = null,

	pub fn header(self: Builder, a: A, ll: []const u8, dist: []const u8, mode: Header) !BuiltCl {
		return if (mode == .greedy) buildClGreedy(a, ll, dist)
			else buildClImpl(self, a, ll, dist, mode);
	}
	pub fn empty(self: Builder, a: A, ll: []const u8, mode: Header) !DistanceHeader {
		std.debug.assert(self.floor <= 2);
		return emptyDistCl(self, a, ll, mode);
	}
	fn finishDistance(self: Builder, a: A, ll: []const u8, dist: *[30]u8, mode: Header) !DistanceHeader {
		std.debug.assert(self.floor <= 2);
		if (trim(dist, 0).len == 0) return self.empty(a, ll, mode);
		applyFloor(dist, self.floor);
		const lengths = trim(dist, 1);
		return .{ .dist = lengths, .built = try self.header(a, ll, lengths, mode) };
	}
	pub fn costFromFreqs(self: Builder, a: A, ll: []const u32, dist: []const u32, extra: i64, mode: Header) !i64 {
		return dynCostFromFreqs(self, a, ll, dist, extra, mode);
	}

	/// Reconstruct one dynamic block. Original spelling metadata is not inherited.
	pub fn complete(self: Builder, a: A, tokens: []const Token, last: bool, request: Request) !Block {
		std.debug.assert(self.floor <= 2);
		var ll: [286]u8 = undefined;
		var dist: [30]u8 = @splat(0);
		switch (request.trees) {
			.fresh => |length258| {
				var c = counts(tokens, &common.fixed_ll_lengths);
				if (length258 != .standard) {
					const n = c.ll[285];
					c.ll[285] = 0;
					c.ll[284] += if (length258 == .alternate_unit) 1 else n;
				}
				freqToLengths(&c.ll, 15, &ll);
				freqToLengths(&c.dist, 15, &dist);
			},
			.merge => |m| {
				var ll_symbols: [286]u16 = undefined;
				var dist_symbols: [30]u16 = undefined;
				var ll_order: std.ArrayList(u16) = .initBuffer(&ll_symbols);
				var dist_order: std.ArrayList(u16) = .initBuffer(&dist_symbols);
				const c = if (m.order == .occurrence)
					countUses(tokens, m.previous.ll_lengths, &ll_order, &dist_order)
				else blk: {
					const c = counts(tokens, m.previous.ll_lengths);
					for (c.ll, 0..) |f, sym| if (f != 0) { ll_order.appendAssumeCapacity(@intCast(sym)); };
					for (c.dist, 0..) |f, sym| if (f != 0) { dist_order.appendAssumeCapacity(@intCast(sym)); };
					break :blk c;
				};
				mergeTree(m.previous.ll_lengths, &c.ll, ll_order.items, &ll);
				if (dist_order.items.len != 0) mergeTree(m.previous.dist_lengths, &c.dist, dist_order.items, &dist);
			},
		}
		const ll_lengths = try a.dupe(u8, trim(&ll, common.EOB + 1));
		const selected = try self.finishDistance(a, ll_lengths, &dist, request.header);
		return .{ .is_last = last, .body = .{ .huff = .{
			.is_fixed = false, .tokens = tokens, .ll_lengths = ll_lengths,
			.dist_lengths = try a.dupe(u8, selected.dist),
			.cl_entries = selected.built.entries.items, .cl_lengths = selected.built.cl_lengths,
		} } };
	}
};


// Huffman ties use (frequency, creation index), including internal nodes.
const HuffmanNode = struct {
	freq: u64,
	id: u32,

	fn lessThan(_: void, a: HuffmanNode, b: HuffmanNode) bool {
		return a.freq < b.freq or (a.freq == b.freq and a.id < b.id);
	}
};
const MAX_LEAVES = 286;
const MAX_NODES = 2 * MAX_LEAVES;

/// Sort leaves once, then merge two queues: leaves and newly created nodes.
/// Internal frequencies are nondecreasing; leaves win ties against internal
/// nodes because their creation indices are smaller. No heap or tree walk.
fn huffmanDepths(lf: []const u64, depth_out: []u32) void {
	const n = lf.len;
	std.debug.assert(n >= 2 and n <= MAX_LEAVES);
	var nodes: [MAX_NODES]HuffmanNode = undefined;
	var parents: [MAX_NODES]u32 = undefined;
	for (lf, 0..) |freq, i| nodes[i] = .{ .freq = freq, .id = @intCast(i) };
	std.mem.sort(HuffmanNode, nodes[0..n], {}, HuffmanNode.lessThan);
	var leaf: usize = 0;
	var internal: usize = n;
	const root = 2 * n - 2;
	for (n..root + 1) |id| {
		var sum: u64 = 0;
		for (0..2) |_| {
			const take_leaf = leaf < n and (internal == id or nodes[leaf].freq <= nodes[internal].freq);
			const child = if (take_leaf) nodes[leaf] else nodes[internal];
			if (take_leaf) leaf += 1 else internal += 1;
			parents[child.id] = @intCast(id);
			sum += child.freq;
		}
		nodes[id] = .{ .freq = sum, .id = @intCast(id) };
	}
	// Parents have larger creation indices. In reverse order, replace each
	// parent link with its depth after the parent's depth is already known.
	parents[root] = 0;
	var child = root;
	while (child > 0) {
		child -= 1;
		parents[child] = parents[parents[child]] + 1;
	}
	@memcpy(depth_out, parents[0..n]);
}

test "Huffman depths preserve frequency and creation-order ties" {
	var prng = std.Random.DefaultPrng.init(0x68756666);
	const random = prng.random();
	for (0..1024) |trial| {
		const n = 2 + trial % (MAX_LEAVES - 1);
		var freq: [MAX_LEAVES]u64 = undefined;
		for (freq[0..n], 0..) |*f, i| f.* = switch (trial % 4) {
			0 => 1,
			1 => random.intRangeAtMost(u64, 1, 7),
			2 => @as(u64, 1) << @intCast(i % 32),
			else => random.intRangeAtMost(u64, 1, std.math.maxInt(u32)),
		};
		// Independent quadratic oracle: scan live nodes for each minimum,
		// with the lower creation index winning equal-frequency ties.
		var weights: [MAX_NODES]u64 = @splat(std.math.maxInt(u64));
		var parents: [MAX_NODES]usize = undefined;
		@memcpy(weights[0..n], freq[0..n]);
		for (n..2 * n - 1) |parent| {
			var sum: u64 = 0;
			for (0..2) |_| {
				var best: usize = 0;
				for (0..parent) |j| {
					if (weights[j] < weights[best]) best = j;
				}
				sum += weights[best];
				parents[best] = parent;
				weights[best] = std.math.maxInt(u64);
			}
			weights[parent] = sum;
		}
		var actual: [MAX_LEAVES]u32 = undefined;
		huffmanDepths(freq[0..n], actual[0..n]);
		for (actual[0..n], 0..) |depth, leaf| {
			var expected: u32 = 0;
			var node = leaf;
			while (node != 2 * n - 2) : (node = parents[node]) expected += 1;
			try std.testing.expectEqual(expected, depth);
		}
	}
}

/// Static round cap for freqToLengths' length-limiting loop. Release builds use
/// this constant; a debug assert (std.debug.assert, compiled out in ReleaseFast)
/// checks the tight per-call bound each call. Rounds are bounded by
/// 1 + n*(bitlen(fmax)+1); worst DEFLATE case n=286, u32 fmax => <= 9439 << cap.
const FREQ_LIMIT_ROUNDS: u32 = 16384;

/// Direct-mapped memo with full key comparison; collisions are misses.
const FreqMemoEntry = struct {
	alphabet: u16,
	max_bits: u8,
	freq: [MAX_LEAVES]u32,
	out: [MAX_LEAVES]u8,
};
threadlocal var freq_memo_used: [512]bool = @splat(false);
threadlocal var freq_memo: [512]FreqMemoEntry = undefined;

pub fn freqToLengths(freq: []const u32, max_bits: u32, out: []u8) void {
	var h = std.hash.Wyhash.init(0);
	h.update(std.mem.sliceAsBytes(freq));
	h.update(std.mem.asBytes(&max_bits));
	const slot: usize = @intCast(h.final() & 511);
	const m = &freq_memo[slot];
	if (freq_memo_used[slot] and m.alphabet == freq.len and m.max_bits == max_bits and
		std.mem.eql(u32, m.freq[0..freq.len], freq))
	{
		@memcpy(out, m.out[0..freq.len]);
		return;
	}
	freqToLengthsCompute(freq, max_bits, out);
	m.alphabet = @intCast(freq.len);
	m.max_bits = @intCast(max_bits);
	@memcpy(m.freq[0..freq.len], freq);
	@memcpy(m.out[0..freq.len], out);
	freq_memo_used[slot] = true;
}

/// Code lengths from symbol frequencies, length-limited to max_bits via the
/// frequency-doubling loop. freq[sym] is a count (0 = absent). Writes out[0..
/// alphabet]; out has length == freq.len == alphabet.
/// Allocation-free (MAX_LEAVES-bounded stack buffers) — this is the hottest
/// leaf of every cost evaluation.
fn freqToLengthsCompute(freq: []const u32, max_bits: u32, out: []u8) void {
	@memset(out, 0);
	const alphabet = freq.len;
	std.debug.assert(alphabet <= MAX_LEAVES);

	// Present symbols in ascending order (array iteration => sorted by symbol).
	var n: usize = 0;
	for (freq) |f| {
		if (f > 0) n += 1;
	}
	if (n == 0) return;
	if (n == 1) {
		for (freq, 0..) |f, s| {
			if (f > 0) {
				out[s] = 1;
				return;
			}
		}
	}

	var syms_buf: [MAX_LEAVES]u16 = undefined;
	var lf_buf: [MAX_LEAVES]u64 = undefined;
	const syms = syms_buf[0..n];
	const lf = lf_buf[0..n];
	{
		var k: usize = 0;
		var s: usize = 0;
		while (s < alphabet) : (s += 1) {
			if (freq[s] > 0) {
				syms[k] = @intCast(s);
				lf[k] = freq[s];
				k += 1;
			}
		}
	}

	// Length-limit to max_bits: an over-deep
	// leaf always has freq < fmax, so doubling never grows the maximum frequency
	// (fmax is invariant) and rounds <= 1 + n*(bitlen(fmax)+1). Release uses the
	// static FREQ_LIMIT_ROUNDS cap; debug asserts the tight per-call bound.
	var fmax0: u64 = 0;
	for (lf) |f| fmax0 = @max(fmax0, f);
	const fbits: u64 = @as(u64, std.math.log2_int(u64, fmax0)) + 1; // bit length (fmax0 >= 1)
	const derived_cap: u64 = 1 + @as(u64, n) * (fbits + 1);

	var depth_buf: [MAX_LEAVES]u32 = undefined;
	const depth = depth_buf[0..n];
	var round: u32 = 0;
	while (round < FREQ_LIMIT_ROUNDS) : (round += 1) {
		huffmanDepths(lf, depth);
		var any_over = false;
		for (depth) |d| {
			if (d > max_bits) {
				any_over = true;
				break;
			}
		}
		if (!any_over) break;
		for (depth, 0..) |d, j| {
			if (d > max_bits) lf[j] *= 2;
		}
	} else {
		// Exceeding the cap violates the length-limiting termination invariant.
		// This is an optimizer bug, not a catchable malformed-input error.
		@panic("freqToLengths: exceeded static round cap (length-limiting termination invariant violated)");
	}
	// Debug-mode invariant: convergence stayed within the proven per-call bound
	// (compiled out in ReleaseFast; live in Debug/ReleaseSafe).
	std.debug.assert(round <= derived_cap);

	for (syms, depth) |s, d| {
		out[s] = @intCast(@min(d, max_bits));
	}
}

// ── CL RLE encoder ─────────────────────────────

/// Generate CL RLE entries for `lengths`, appending to `entries`.
fn genClEntries(
	alloc: std.mem.Allocator,
	lengths: []const u8,
	entries: *std.ArrayList(ClEntry),
) !void {
	var i: usize = 0;
	const len = lengths.len;
	while (i < len) {
		const v = lengths[i];
		if (v == 0) {
			var j = i;
			while (j < len and lengths[j] == 0) j += 1;
			var count: usize = j - i;
			while (count > 0) {
				if (count >= 11) {
					const run = @min(count, 138);
					try entries.append(alloc, .{ .kind = .rep18, .val = @intCast(run) });
					count -= run;
				} else if (count >= 3) {
					const run = @min(count, 10);
					try entries.append(alloc, .{ .kind = .rep17, .val = @intCast(run) });
					count -= run;
				} else {
					try entries.append(alloc, .{ .kind = .lit, .val = 0 });
					count -= 1;
				}
			}
			i = j;
		} else {
			try entries.append(alloc, .{ .kind = .lit, .val = v });
			i += 1;
			var j = i;
			while (j < len and lengths[j] == v and j - i < 6) j += 1;
			var run: usize = j - i;
			while (run >= 3) {
				const r = @min(run, 6);
				try entries.append(alloc, .{ .kind = .rep16, .val = @intCast(r) });
				run -= r;
				i += r;
			}
		}
	}
}


fn clEntriesBits(cl_enc: *const common.HuffEnc(19), entries: []const ClEntry) i64 {
	var bits: i64 = 0;
	for (entries) |e| {
		switch (e.kind) {
			.lit => bits += cl_enc.len[e.val],
			.rep16 => bits += @as(i64, cl_enc.len[16]) + 2,
			.rep17 => bits += @as(i64, cl_enc.len[17]) + 3,
			.rep18 => bits += @as(i64, cl_enc.len[18]) + 7,
			.sep => {},
		}
	}
	return bits;
}

pub fn hclenOf(cl_lengths: []const u8) usize {
	var hclen: usize = 19;
	while (hclen > 4 and cl_lengths[HCLEN_ORDER[hclen - 1]] == 0) hclen -= 1;
	return hclen;
}

fn clFreqOf(entries: []const ClEntry) [19]u32 {
	var cl_freq = [_]u32{0} ** 19;
	for (entries) |e| switch (e.kind) {
		.lit => cl_freq[e.val] += 1,
		.rep16 => cl_freq[16] += 1,
		.rep17 => cl_freq[17] += 1,
		.rep18 => cl_freq[18] += 1,
		.sep => {},
	};
	return cl_freq;
}

pub fn clHeaderBits(cl_lengths: *const [19]u8, entries: []const ClEntry) !i64 {
	const cl_enc = common.HuffEnc(19).build(cl_lengths) orelse return error.Malformed;
	return @as(i64, @intCast(17 + hclenOf(cl_lengths) * 3)) + clEntriesBits(&cl_enc, entries);
}

// Cost charged in dpClSection for a CL symbol absent from the current tree.
const CL_UNUSED_COST: i64 = 7;

/// Minimum-cost CL RLE encoding with deterministic ties: literal, rep16,
/// rep17, rep18, then ascending repeat length. The largest section is the
/// combined literal/length and distance sequence (286 + 30 lengths).
pub const MAX_CL_SEQ = MAX_LEAVES + 30;

/// Direct-mapped memo for the pure (costs, sequence) DP. Header construction
/// and polishing revisit these inputs; full key comparison makes collisions misses.
const DpMemoEntry = struct {
	costs: [19]u8,
	seq_len: u16,
	n_entries: u16,
	seq: [MAX_CL_SEQ]u8,
	entries: [MAX_CL_SEQ]ClEntry,
};
threadlocal var dp_memo_used: [1024]bool = @splat(false);
threadlocal var dp_memo: [1024]DpMemoEntry = undefined;

fn dpMemoSlot(seq: []const u8, costs: *const [19]u8) usize {
	var h = std.hash.Wyhash.init(0);
	h.update(costs);
	h.update(seq);
	return @intCast(h.final() & 1023);
}

fn dpClSection(
	alloc: std.mem.Allocator,
	seq: []const u8,
	costs: *const [19]u8,
	entries: *std.ArrayList(ClEntry),
) !void {
	const slot = dpMemoSlot(seq, costs);
	const m = &dp_memo[slot];
	if (dp_memo_used[slot] and m.seq_len == seq.len and
		std.mem.eql(u8, &m.costs, costs) and
		std.mem.eql(u8, m.seq[0..seq.len], seq))
	{
		try entries.appendSlice(alloc, m.entries[0..m.n_entries]);
		return;
	}
	const start = entries.items.len;
	try dpClSectionCompute(alloc, seq, costs, entries);
	const produced = entries.items[start..];
	m.costs = costs.*;
	m.seq_len = @intCast(seq.len);
	@memcpy(m.seq[0..seq.len], seq);
	m.n_entries = @intCast(produced.len);
	@memcpy(m.entries[0..produced.len], produced);
	dp_memo_used[slot] = true;
}

/// Reconstruct the same fixed-price DP optimum one maximal run at a time.
/// Tables retain the original literal/16/17/18 and ascending-count tie order.
fn dpClSectionCompute(alloc: std.mem.Allocator, seq: []const u8, costs: *const [19]u8, entries: *std.ArrayList(ClEntry)) !void {
	std.debug.assert(seq.len <= MAX_CL_SEQ);
	var price: [19]u8 = undefined;
	for (costs, &price) |c, *p| p.* = if (c != 0) c else @intCast(CL_UNUSED_COST);
	var rev: [MAX_CL_SEQ]ClEntry = undefined;
	var nr: usize = 0;
	var end = seq.len;
	while (end > 0) {
		const v = seq[end - 1];
		var start = end - 1;
		while (start > 0 and seq[start - 1] == v) start -= 1;
		const table = if (v == 0) zeroRunTable(price[0], price[16], price[17], price[18])
			else &nonzero_run_tables[price[v]][price[16]];
		var n = end - start;
		while (n > 0) {
			const step = table.steps[n];
			rev[nr] = .{ .kind = step.kind, .val = if (step.kind == .lit) v else step.count };
			nr += 1;
			n -= step.count;
		}
		end = start;
	}
	try entries.ensureUnusedCapacity(alloc, nr);
	while (nr > 0) {
		nr -= 1;
		entries.appendAssumeCapacity(rev[nr]);
	}
}

test "CL run reconstruction: exact entries and tie order match sequence DP" {
	const Check = struct {
		fn run(seq: []const u8, costs: *const [19]u8, left: *std.ArrayList(ClEntry), right: *std.ArrayList(ClEntry)) !void {
			left.clearRetainingCapacity();
			right.clearRetainingCapacity();
			// Builders append to a prior section; preserve its prefix too.
			try left.append(std.testing.allocator, .{ .kind = .sep, .val = 0 });
			try right.append(std.testing.allocator, .{ .kind = .sep, .val = 0 });
			try dpClSectionReference(std.testing.allocator, seq, costs, left);
			try dpClSectionCompute(std.testing.allocator, seq, costs, right);
			try std.testing.expectEqualDeep(left.items, right.items);
		}
	};
	var left: std.ArrayList(ClEntry) = .empty;
	defer left.deinit(std.testing.allocator);
	var right: std.ArrayList(ClEntry) = .empty;
	defer right.deinit(std.testing.allocator);
	var seq: [MAX_CL_SEQ]u8 = @splat(0);
	var costs = [_]u8{0} ** 19;
	const boundaries = [_]usize{ 0, 1, 2, 3, 4, 6, 7, 10, 11, 12, 137, 138, 139, 140, 275, 276, 277, MAX_CL_SEQ };
	// Include absent symbols: CL construction prices them at 7, whereas
	// polish's internal guide prices them at 8. Do not conflate the two.
	for (0..8) |literal| for (0..8) |r16| for (0..8) |r17| for (0..8) |r18| {
		costs[0] = @intCast(literal);
		costs[16] = @intCast(r16);
		costs[17] = @intCast(r17);
		costs[18] = @intCast(r18);
		for (boundaries) |n| try Check.run(seq[0..n], &costs, &left, &right);
	};
	for (1..16) |v| {
		@memset(&seq, @intCast(v));
		for (0..8) |literal| for (0..8) |r16| {
			costs[v] = @intCast(literal);
			costs[16] = @intCast(r16);
			for (boundaries) |n| try Check.run(seq[0..n], &costs, &left, &right);
		};
	}
	for (0..4) |profile| {
		for (&costs, 0..) |*v, i| v.* = @intCast((i * 3 + profile * (i + 1)) % 8);
		var count: usize = 1;
		for (0..9) |n| {
			for (0..count) |code| {
				var rest = code;
				for (seq[0..n]) |*v| { v.* = @intCast(rest % 3); rest /= 3; }
				try Check.run(seq[0..n], &costs, &left, &right);
			}
			count *= 3;
		}
	}
}

// Previous sequence-wide DP retained as an independent test oracle.
fn dpClSectionReference(
	alloc: std.mem.Allocator,
	seq: []const u8,
	costs: *const [19]u8,
	entries: *std.ArrayList(ClEntry),
) !void {
	var cost: [19]i64 = undefined;
	for (costs, 0..) |c, s| cost[s] = if (c != 0) c else CL_UNUSED_COST;
	const c16 = cost[16] + 2;
	const c17 = cost[17] + 3;
	const c18 = cost[18] + 7;
	const n = seq.len;
	std.debug.assert(n <= MAX_CL_SEQ);
	var f_buf: [MAX_CL_SEQ + 1]i64 = undefined;
	var ch_kind_buf: [MAX_CL_SEQ + 1]deflasm.ClKind = undefined;
	var ch_k_buf: [MAX_CL_SEQ + 1]u16 = undefined;
	var run_buf: [MAX_CL_SEQ + 1]u32 = undefined;
	var zrun_buf: [MAX_CL_SEQ + 1]u32 = undefined;
	const f = f_buf[0 .. n + 1];
	const ch_kind = ch_kind_buf[0 .. n + 1];
	const ch_k = ch_k_buf[0 .. n + 1];
	const run = run_buf[0 .. n + 1];
	const zrun = zrun_buf[0 .. n + 1];
	f[0] = 0;
	run[0] = 0;
	zrun[0] = 0;
	for (1..n + 1) |i| {
		const v = seq[i - 1];
		run[i] = if (i > 1 and seq[i - 2] == v) run[i - 1] + 1 else 1;
		zrun[i] = if (v == 0) zrun[i - 1] + 1 else 0;
	}
	// rep18 sliding-window minimum (the profile's dominant term was this
	// branch's naive k-loop: up to 128 f[i-k] probes per position inside long
	// zero runs). c18 is constant over k, so the k=11..min(138,zrun) candidate
	// scan is a pure window minimum over f[j], j in [i-min(138,zrun), i-11] —
	// a monotone deque gives it in O(1) amortized. Tie behavior preserved
	// exactly: the naive loop's ascending-k strict < keeps the SMALLEST k =
	// LARGEST j on equal f, and the deque pops >= from the back, so among
	// equal minima only the newest (largest) j survives. The deque lives per
	// zero run (zrun resets empty it); within a run the window's lower bound
	// is monotone, so front pops are sound.
	var dq: [MAX_CL_SEQ + 1]u32 = undefined; // j values, f[dq] strictly increasing
	var dq_head: usize = 0;
	var dq_tail: usize = 0;
	for (1..n + 1) |i| {
		const v = seq[i - 1];
		if (v != 0) {
			dq_head = 0; // zero run broken: window dead until the next run
			dq_tail = 0;
		}
		var best = f[i - 1] + cost[v];
		var kind: deflasm.ClKind = .lit;
		var kk: u16 = v;
		// rep16: elements i-k..i-1 must equal seq[i-k-1] → run spans >= k+1.
		// (<= 4 candidates; run-constrained window, not worth a deque)
		const kmax16: usize = @min(6, if (run[i] > 0) run[i] - 1 else 0);
		var k: usize = 3;
		while (k <= kmax16) : (k += 1) {
			const c = f[i - k] + c16;
			if (c < best) {
				best = c;
				kind = .rep16;
				kk = @intCast(k);
			}
		}
		if (zrun[i] > 0) {
			const kmax17: usize = @min(10, zrun[i]);
			k = 3;
			while (k <= kmax17) : (k += 1) {
				const c = f[i - k] + c17;
				if (c < best) {
					best = c;
					kind = .rep17;
					kk = @intCast(k);
				}
			}
			if (zrun[i] >= 11) {
				// k=11 newly valid here: push its j = i-11 (one new candidate
				// per position; consecutive positions push consecutive j's).
				const j_new: u32 = @intCast(i - 11);
				while (dq_tail > dq_head and f[dq[dq_tail - 1]] >= f[j_new]) dq_tail -= 1;
				dq[dq_tail] = j_new;
				dq_tail += 1;
				// Window lower bound: j >= i - min(138, zrun). Never empties
				// the deque: the just-pushed j_new = i-11 >= j_lo always.
				const j_lo = i - @min(138, zrun[i]);
				while (dq[dq_head] < j_lo) dq_head += 1;
				const jmin = dq[dq_head];
				const c = f[jmin] + c18;
				if (c < best) {
					best = c;
					kind = .rep18;
					kk = @intCast(i - jmin);
				}
			}
		}
		f[i] = best;
		ch_kind[i] = kind;
		ch_k[i] = kk;
	}
	// Reconstruct (reversed), then append in order.
	var rev: [MAX_CL_SEQ]ClEntry = undefined;
	var nrev: usize = 0;
	var i: usize = n;
	while (i > 0) {
		const kind = ch_kind[i];
		rev[nrev] = .{ .kind = kind, .val = ch_k[i] };
		nrev += 1;
		i -= if (kind == .lit) 1 else ch_k[i];
	}
	try entries.ensureUnusedCapacity(alloc, nrev);
	var j: usize = nrev;
	while (j > 0) {
		j -= 1;
		entries.appendAssumeCapacity(rev[j]);
	}
}

pub const BuiltCl = struct {
	entries: std.ArrayList(ClEntry),
	cl_lengths: [19]u8,
	header_bits: i64,
};


fn buildClGreedy(alloc: std.mem.Allocator, ll_lengths: []const u8, dist_lengths: []const u8) !BuiltCl {
	var entries: std.ArrayList(ClEntry) = .empty;
	try genClEntries(alloc, ll_lengths, &entries);
	try entries.append(alloc, .{ .kind = .sep, .val = 0 });
	try genClEntries(alloc, dist_lengths, &entries);
	var freq = clFreqOf(entries.items);
	var cl_lengths = [_]u8{0} ** 19;
	freqToLengths(&freq, 7, &cl_lengths);
	return .{
		.entries = entries,
		.cl_lengths = cl_lengths,
		.header_bits = try clHeaderBits(&cl_lengths, entries.items),
	};
}

/// Encode nonzero lengths literally and zero runs with rep17/18.
/// This gives buildCl a seed without rep16.
fn genClNorep16(
	alloc: std.mem.Allocator,
	lengths: []const u8,
	entries: *std.ArrayList(ClEntry),
) !void {
	var i: usize = 0;
	const len = lengths.len;
	while (i < len) {
		const v = lengths[i];
		if (v == 0) {
			var j = i;
			while (j < len and lengths[j] == 0) j += 1;
			var count: usize = j - i;
			while (count > 0) {
				if (count >= 11) {
					const run = @min(count, 138);
					try entries.append(alloc, .{ .kind = .rep18, .val = @intCast(run) });
					count -= run;
				} else if (count >= 3) {
					const run = @min(count, 10);
					try entries.append(alloc, .{ .kind = .rep17, .val = @intCast(run) });
					count -= run;
				} else {
					try entries.append(alloc, .{ .kind = .lit, .val = 0 });
					count -= 1;
				}
			}
			i = j;
		} else {
			try entries.append(alloc, .{ .kind = .lit, .val = v });
			i += 1;
		}
	}
}

/// Encode every length literally, including zeros. A sparse tree can then
/// assign CL symbol 0 a one-bit code, reaching a fixed point that seeds
/// using rep17/18 cannot reach.
fn genClAllLiteral(
	alloc: std.mem.Allocator,
	lengths: []const u8,
	entries: *std.ArrayList(ClEntry),
) !void {
	for (lengths) |v| {
		try entries.append(alloc, .{ .kind = .lit, .val = v });
	}
}

/// Encode runs using rep16 only, including runs of zero lengths. Together
/// with the other seeds this covers rep16 on/off and rep17/18 on/off.
fn genClNorep1718(
	alloc: std.mem.Allocator,
	lengths: []const u8,
	entries: *std.ArrayList(ClEntry),
) !void {
	var i: usize = 0;
	const len = lengths.len;
	while (i < len) {
		const v = lengths[i];
		try entries.append(alloc, .{ .kind = .lit, .val = v });
		i += 1;
		var j = i;
		while (j < len and lengths[j] == v and j - i < 6) j += 1;
		var run: usize = j - i;
		while (run >= 3) {
			const r = @min(run, 6);
			try entries.append(alloc, .{ .kind = .rep16, .val = @intCast(r) });
			run -= r;
			i += r;
		}
	}
}


const HeaderSeed = enum {
	greedy, no_rep16, literal, no_rep1718,

	fn append(self: HeaderSeed, a: A, lengths: []const u8, entries: *std.ArrayList(ClEntry)) !void {
		return switch (self) {
			.greedy => genClEntries(a, lengths, entries),
			.no_rep16 => genClNorep16(a, lengths, entries),
			.literal => genClAllLiteral(a, lengths, entries),
			.no_rep1718 => genClNorep1718(a, lengths, entries),
		};
	}
};

fn buildClImpl(builder: Builder, alloc: std.mem.Allocator, ll_lengths: []const u8, dist_lengths: []const u8, mode: Header) !BuiltCl {
	if (builder.memo) |memo| {
		// These bounds cover fixed and dynamic DEFLATE alphabets. Larger
		// internal/test inputs retain the uncached builder's behavior.
		if (ll_lengths.len <= 288 and dist_lengths.len <= 32) {
			const slot = memo.slot(ll_lengths, dist_lengths, mode, builder.extra_seeds);
			if (slot.valid and slot.ll_len == ll_lengths.len and slot.dist_len == dist_lengths.len and
				slot.mode == mode and slot.extra_seeds == builder.extra_seeds and
				std.mem.eql(u8, slot.lengths[0..ll_lengths.len], ll_lengths) and
				std.mem.eql(u8, slot.lengths[ll_lengths.len..][0..dist_lengths.len], dist_lengths))
			{
				memo.hits += 1;
				return .{ .entries = .fromOwnedSlice(try alloc.dupe(ClEntry, slot.entries[0..slot.entry_count])), .cl_lengths = slot.cl_lengths, .header_bits = slot.header_bits };
			}
			memo.misses += 1;
			const built = try buildClUncached(builder, alloc, ll_lengths, dist_lengths, mode);
			if (built.entries.items.len <= slot.entries.len) {
				if (slot.valid) memo.evictions += 1;
				slot.valid = true;
				slot.ll_len = @intCast(ll_lengths.len);
				slot.dist_len = @intCast(dist_lengths.len);
				slot.mode = mode;
				slot.extra_seeds = builder.extra_seeds;
				@memcpy(slot.lengths[0..ll_lengths.len], ll_lengths);
				@memcpy(slot.lengths[ll_lengths.len..][0..dist_lengths.len], dist_lengths);
				slot.entry_count = @intCast(built.entries.items.len);
				@memcpy(slot.entries[0..slot.entry_count], built.entries.items);
				slot.cl_lengths = built.cl_lengths;
				slot.header_bits = built.header_bits;
			}
			return built;
		}
	}
	return buildClUncached(builder, alloc, ll_lengths, dist_lengths, mode);
}

fn buildClUncached(builder: Builder, alloc: std.mem.Allocator, ll_lengths: []const u8, dist_lengths: []const u8, mode: Header) !BuiltCl {
	std.debug.assert(mode != .greedy);
	var best: ?BuiltCl = null;
	// Extra seeds participate in final construction, not cheap search estimates.
	const seeds = std.enums.values(HeaderSeed);
	const n_seeds: usize = if (mode != .search and builder.extra_seeds) seeds.len else 2;
	for (seeds[0..n_seeds]) |seed| {
		var entries: std.ArrayList(ClEntry) = .empty;
		try seed.append(alloc, ll_lengths, &entries);
		try entries.append(alloc, .{ .kind = .sep, .val = 0 });
		try seed.append(alloc, dist_lengths, &entries);
		var cur_freq = clFreqOf(entries.items);
		var cur_lengths = [_]u8{0} ** 19;
		freqToLengths(&cur_freq, 7, &cur_lengths);
		const seed_cost = try clHeaderBits(&cur_lengths, entries.items);
		if (best == null or seed_cost < best.?.header_bits) {
			best = .{ .entries = entries, .cl_lengths = cur_lengths, .header_bits = seed_cost };
		}
		for (0..2) |_| {
			var e2: std.ArrayList(ClEntry) = .empty;
			try dpClSection(alloc, ll_lengths, &cur_lengths, &e2);
			try e2.append(alloc, .{ .kind = .sep, .val = 0 });
			try dpClSection(alloc, dist_lengths, &cur_lengths, &e2);
			cur_freq = clFreqOf(e2.items);
			cur_lengths = [_]u8{0} ** 19;
			freqToLengths(&cur_freq, 7, &cur_lengths);
			const cost = try clHeaderBits(&cur_lengths, e2.items);
			if (cost < best.?.header_bits) {
				best = .{ .entries = e2, .cl_lengths = cur_lengths, .header_bits = cost };
			}
		}
	}
	// Package-merge chain: start with all lengths five, then rebuild from
	// DP usage counts until a fixed point.
	if (mode == .search) return best.?;
	{
		var cur_lengths = [_]u8{0} ** 19;
		for (ll_lengths) |v| cur_lengths[v] = 5;
		for (dist_lengths) |v| cur_lengths[v] = 5;
		cur_lengths[16] = 5;
		cur_lengths[17] = 5;
		cur_lengths[18] = 5;
		var prev = [_]u8{0} ** 19;
		var have_prev = false;
		for (0..6) |_| {
			var e2: std.ArrayList(ClEntry) = .empty;
			try dpClSection(alloc, ll_lengths, &cur_lengths, &e2);
			try e2.append(alloc, .{ .kind = .sep, .val = 0 });
			try dpClSection(alloc, dist_lengths, &cur_lengths, &e2);
			const cur_freq = clFreqOf(e2.items);
			cur_lengths = packageMergeCl(&cur_freq);
			const cost = try clHeaderBits(&cur_lengths, e2.items);
			if (cost < best.?.header_bits) {
				best = .{ .entries = e2, .cl_lengths = cur_lengths, .header_bits = cost };
			}
			if (have_prev and std.mem.eql(u8, &cur_lengths, &prev)) break;
			prev = cur_lengths;
			have_prev = true;
		}
	}
	// RFC 1951 section 3.2.7 permits repeats across the literal/distance
	// boundary. Assembly derives HLIT/HDIST from the length arrays.
	if (mode == .crossing) {
		const combined = try std.mem.concat(alloc, u8, &.{ ll_lengths, dist_lengths });
		for (seeds) |seed| {
			var entries: std.ArrayList(ClEntry) = .empty;
			try seed.append(alloc, combined, &entries);
			var cur_entries = entries;
			var cur_freq = clFreqOf(cur_entries.items);
			var cur_lengths = [_]u8{0} ** 19;
			freqToLengths(&cur_freq, 7, &cur_lengths);
			for (0..3) |_| {
				const cost = try clHeaderBits(&cur_lengths, cur_entries.items);
				if (cost < best.?.header_bits) {
					best = .{ .entries = cur_entries, .cl_lengths = cur_lengths, .header_bits = cost };
				}
				var e2: std.ArrayList(ClEntry) = .empty;
				try dpClSection(alloc, combined, &cur_lengths, &e2);
				if (clEntriesEql(cur_entries.items, e2.items)) break;
				cur_entries = e2;
				cur_freq = clFreqOf(cur_entries.items);
				cur_lengths = [_]u8{0} ** 19;
				freqToLengths(&cur_freq, 7, &cur_lengths);
			}
		}
	}
	return best.?;
}

fn clEntriesEql(a: []const ClEntry, b: []const ClEntry) bool {
	if (a.len != b.len) return false;
	for (a, b) |x, y| {
		if (x.kind != y.kind or x.val != y.val) return false;
	}
	return true;
}

/// Optimal length-limited CL lengths via package-merge. Order items by
/// (weight, id): leaves in (frequency, symbol) order, then packages in
/// creation order. Count each symbol's occurrences among the first 2n-2
/// items of the final pool to obtain its length.
fn packageMergeCl(freq: *const [19]u32) [19]u8 {
	var lengths = [_]u8{0} ** 19;
	var syms_buf: [19]u8 = undefined;
	var n: usize = 0;
	for (0..19) |s| {
		if (freq[s] > 0) {
			syms_buf[n] = @intCast(s);
			n += 1;
		}
	}
	if (n == 0) return lengths;
	if (n == 1) {
		lengths[syms_buf[0]] = 1;
		return lengths;
	}
	// sort leaves by (freq, sym) ascending
	var q: usize = 1;
	while (q < n) : (q += 1) {
		const s = syms_buf[q];
		var r = q;
		while (r > 0 and (freq[syms_buf[r - 1]] > freq[s] or
				(freq[syms_buf[r - 1]] == freq[s] and syms_buf[r - 1] > s))) : (r -= 1) {
			syms_buf[r] = syms_buf[r - 1];
		}
		syms_buf[r] = s;
	}
	const Item = struct { w: u64, id: u32, counts: [19]u8 };
	// capacities: leaves n<=19; packages per round <= (leaves+packages)/2;
	// bounded by 19 + 18 = 37 pool, 18 packages — round up generously.
	var leaves: [19]Item = undefined;
	for (0..n) |i| {
		var c = [_]u8{0} ** 19;
		c[syms_buf[i]] = 1;
		leaves[i] = .{ .w = freq[syms_buf[i]], .id = @intCast(i), .counts = c };
	}
	var next_id: u32 = @intCast(n);
	var packages: [40]Item = undefined;
	var npkg: usize = 0;
	var pool: [64]Item = undefined;
	for (0..6) |_| { // max_bits - 1 = 6 rounds
		var np: usize = 0;
		for (leaves[0..n]) |it| {
			pool[np] = it;
			np += 1;
		}
		for (packages[0..npkg]) |it| {
			pool[np] = it;
			np += 1;
		}
		// insertion sort by (w, id)
		var a: usize = 1;
		while (a < np) : (a += 1) {
			const it = pool[a];
			var b = a;
			while (b > 0 and (pool[b - 1].w > it.w or
					(pool[b - 1].w == it.w and pool[b - 1].id > it.id))) : (b -= 1) {
				pool[b] = pool[b - 1];
			}
			pool[b] = it;
		}
		npkg = 0;
		var i: usize = 0;
		while (i + 1 < np) : (i += 2) {
			var c = pool[i].counts;
			for (0..19) |s| c[s] += pool[i + 1].counts[s];
			packages[npkg] = .{ .w = pool[i].w + pool[i + 1].w, .id = next_id, .counts = c };
			next_id += 1;
			npkg += 1;
		}
	}
	var np: usize = 0;
	for (leaves[0..n]) |it| {
		pool[np] = it;
		np += 1;
	}
	for (packages[0..npkg]) |it| {
		pool[np] = it;
		np += 1;
	}
	var a: usize = 1;
	while (a < np) : (a += 1) {
		const it = pool[a];
		var b = a;
		while (b > 0 and (pool[b - 1].w > it.w or
				(pool[b - 1].w == it.w and pool[b - 1].id > it.id))) : (b -= 1) {
			pool[b] = pool[b - 1];
		}
		pool[b] = it;
	}
	for (pool[0 .. 2 * n - 2]) |it| {
		for (0..19) |s| lengths[s] += it.counts[s];
	}
	return lengths;
}

pub const DistanceHeader = struct {
	dist: []const u8, // Borrowed; copy before storing in a block.
	built: BuiltCl,
};

const EMPTY_DIST_ZERO = [_]u8{0};
const EMPTY_DIST_ONE = [_]u8{1};
const EMPTY_DIST_COMPLETE = [_]u8{ 1, 1 };

/// At floor 0, either RFC 1951 §3.2.7 dummy ([0] or [1]) may give a smaller
/// CL header. Floor 1 requires [1]; floor 2 requires the complete [1, 1] tree.
pub fn emptyDistCandidates(floor: u8) []const []const u8 {
	return switch (floor) {
		0 => &.{ &EMPTY_DIST_ZERO, &EMPTY_DIST_ONE },
		1 => &.{&EMPTY_DIST_ONE},
		else => &.{&EMPTY_DIST_COMPLETE},
	};
}

/// CL encoding for a matchless block. Evaluate every candidate distance tree
/// the floor allows, keep the cheaper header; tie prefers the earlier
/// candidate ([0] at level 0).
fn emptyDistCl(builder: Builder, alloc: std.mem.Allocator, ll_lengths: []const u8, cl_model: Header) !DistanceHeader {
	var best: ?DistanceHeader = null;
	for (emptyDistCandidates(builder.floor)) |dl| {
		const built = try builder.header(alloc, ll_lengths, dl, cl_model);
		if (best == null or built.header_bits < best.?.built.header_bits) {
			best = .{ .dist = dl, .built = built };
		}
	}
	return best.?;
}

/// Dynamic-block cost from frequency tables and precomputed extra bits.
/// ll_freq has 286 slots, dist_freq 30.

fn dynCostFromFreqs(
	builder: Builder,
	alloc: std.mem.Allocator,
	ll_freq: []const u32,
	dist_freq: []const u32,
	extra_bits: i64,
	cl_model: Header,
) !i64 {
	var ll_full = [_]u8{0} ** 286;
	freqToLengths(ll_freq, 15, &ll_full);
	const ll_lengths = trim(&ll_full, common.EOB + 1);
	var dist_full: [30]u8 = undefined;
	freqToLengths(dist_freq, 15, &dist_full);
	const selected = try builder.finishDistance(alloc, ll_lengths, &dist_full, cl_model);
	var bits = selected.built.header_bits;
	const dist_enc = common.HuffEnc(32).build(selected.dist) orelse return error.Malformed;
	for (dist_freq, 0..) |f, sym| {
		if (f > 0) bits += @as(i64, f) * dist_enc.len[sym];
	}

	const ll_enc = common.HuffEnc(288).build(ll_lengths) orelse return error.Malformed;
	for (ll_freq, 0..) |f, s| {
		if (f > 0) bits += @as(i64, f) * ll_enc.len[s];
	}
	return bits + extra_bits;
}

/// Cost of a built dynamic Huff block from its own stored lengths/entries/
/// tokens.
pub fn bitCost(h: Huff) !i64 {
	var bits: i64 = @intCast(17 + deflasm.encodingHclen(h) * 3);
	const cl_enc = common.HuffEnc(19).build(&h.cl_lengths) orelse return error.Malformed;
	bits += clEntriesBits(&cl_enc, h.cl_entries);

	const ll_enc = common.HuffEnc(288).build(h.ll_lengths) orelse return error.Malformed;
	const dist_enc = common.HuffEnc(32).build(h.dist_lengths) orelse return error.Malformed;
	if (ll_enc.len[common.EOB] == 0) return error.Malformed;

	for (h.tokens) |tok| {
		switch (tok) {
			.lit => |b| bits += ll_enc.len[b],
			.match => |m| {
				var lc: usize = lenCodeTable[m.length].code;
				var xn: i64 = lenCodeTable[m.length].extra;
				if (lc == 285 and (ll_enc.len[285] == 0 or
					(h.encoding != null and m.original_alt258 and ll_enc.len[284] > 0))) {
					lc = 284;
					xn = 5;
				}
				const dc = distCodeTable[m.distance].code;
				bits += @as(i64, ll_enc.len[lc]) + xn +
					@as(i64, dist_enc.len[dc]) + distCodeTable[m.distance].extra;
			},
		}
	}
	return bits + ll_enc.len[common.EOB];
}


const RunStep = struct { kind: deflasm.ClKind, count: u8 };
const RunTable = struct { costs: [MAX_CL_SEQ + 1]u16, steps: [MAX_CL_SEQ + 1]RunStep };

// A nonzero run starts with a literal; subsequent symbols can be literals
// or rep16 chunks of 3..6. Only two prices matter, both in the range 1..8
// before rep16's extra bits. Precompute every combination once at compile time.
const nonzero_run_tables = blk: {
	@setEvalBranchQuota(1000000);
	var table = std.mem.zeroes([9][9]RunTable);
	for (1..9) |literal| for (1..9) |r16| {
		const t = &table[literal][r16];
		const f = &t.costs;
		for (1..MAX_CL_SEQ + 1) |n| {
			var best = f[n - 1] + @as(u16, literal);
			var step: RunStep = .{ .kind = .lit, .count = 1 };
			var k: usize = 3;
			while (k <= @min(6, n - 1)) : (k += 1) {
				const cost = f[n - k] + @as(u16, r16 + 2);
				if (cost < best) { best = cost; step = .{ .kind = .rep16, .count = @intCast(k) }; }
			}
			f[n] = best;
			t.steps[n] = step;
		}
	};
	break :blk table;
};

const ZeroRunMemo = struct { key: u16, table: RunTable };
threadlocal var zero_run_used: [128]bool = @splat(false);
threadlocal var zero_run_memo: [128]ZeroRunMemo = undefined;

fn zeroRunTable(l0: u16, r16: u16, r17: u16, r18: u16) *const RunTable {
	std.debug.assert(l0 >= 1 and l0 <= 8 and r16 >= 1 and r16 <= 8 and r17 >= 1 and r17 <= 8 and r18 >= 1 and r18 <= 8);
	const c16 = r16 + 2;
	const c17 = r17 + 3;
	const c18 = r18 + 7;
	const key: u16 = (l0 - 1) | ((c16 - 3) << 3) | ((c17 - 4) << 6) | ((c18 - 8) << 9);
	const slot = (@as(u32, key) *% 2654435761) >> 25;
	const entry = &zero_run_memo[slot];
	if (zero_run_used[slot] and entry.key == key) return &entry.table;
	const f = &entry.table.costs;
	f[0] = 0;
	var deque: [MAX_CL_SEQ + 1]usize = undefined;
	var head: usize = 0;
	var tail: usize = 0;
	for (1..MAX_CL_SEQ + 1) |n| {
		var best = f[n - 1] + l0;
		var step: RunStep = .{ .kind = .lit, .count = 1 };
		var k: usize = 3;
		while (k <= @min(6, n - 1)) : (k += 1) {
			const cost = f[n - k] + c16;
			if (cost < best) { best = cost; step = .{ .kind = .rep16, .count = @intCast(k) }; }
		}
		k = 3;
		while (k <= @min(10, n)) : (k += 1) {
			const cost = f[n - k] + c17;
			if (cost < best) { best = cost; step = .{ .kind = .rep17, .count = @intCast(k) }; }
		}
		if (n >= 11) {
			const next = n - 11;
			while (tail > head and f[deque[tail - 1]] >= f[next]) tail -= 1;
			deque[tail] = next;
			tail += 1;
			const lo = n - @min(138, n);
			while (deque[head] < lo) head += 1;
			const cost = f[deque[head]] + c18;
			if (cost < best) { best = cost; step = .{ .kind = .rep18, .count = @intCast(n - deque[head]) }; }
		}
		f[n] = best;
		entry.table.steps[n] = step;
	}
	entry.key = key;
	zero_run_used[slot] = true;
	return &entry.table;
}


pub const Counts = struct {
	ll: [286]u32 = @splat(0),
	dist: [30]u32 = @splat(0),
};
pub fn counts(ts: []const Token, ll: []const u8) Counts {
	return countUses(ts, ll, null, null);
}
fn countSymbol(freq: []u32, sym: u16, order: ?*std.ArrayList(u16)) void {
	if (order) |o| {
		if (freq[sym] == 0) o.appendAssumeCapacity(sym);
	}
	freq[sym] += 1;
}
fn countUses(ts: []const Token, ll: []const u8, ll_order: ?*std.ArrayList(u16), dist_order: ?*std.ArrayList(u16)) Counts {
	var c: Counts = .{};
	countSymbol(&c.ll, common.EOB, ll_order);
	for (ts) |t| switch (t) {
		.lit => |b| countSymbol(&c.ll, b, ll_order),
		.match => |m| {
			const code = if (m.length == common.MAX_MATCH_LENGTH and (ll.len <= 285 or ll[285] == 0)) 284 else common.lenCodeTable[m.length].code;
			countSymbol(&c.ll, code, ll_order);
			countSymbol(&c.dist, common.distCodeTable[m.distance].code, dist_order);
		},
	};
	return c;
}
const KRAFT_FULL: u32 = 1 << 15; // Kraft sum in 2^-15 units

fn kraft(lens: []const u8) u32 {
	var sum: u32 = 0;
	for (lens) |l| if (l != 0) {
		std.debug.assert(l <= 15);
		sum += @as(u32, 1) << @intCast(15 - l);
	};
	return sum;
}
fn mergeTree(prev: []const u8, freq: []const u32, order: []const u16, out: []u8) void {
	freqToLengths(freq, 15, out);
	for (order) |sym| if (sym < prev.len and prev[sym] != 0) {
		out[sym] = prev[sym];
	};
	if (order.len == 1) {
		out[order[0]] = 1;
		return;
	}
	// Equal-frequency ties follow the supplied order.
	while (kraft(out) > KRAFT_FULL) {
		var selected: ?usize = null;
		for (order) |sym| if (out[sym] < 15) {
			if (selected == null or freq[sym] < freq[selected.?] or
				(freq[sym] == freq[selected.?] and out[sym] > out[selected.?])) selected = sym;
		};
		if (selected == null) @panic("tree completion has no legal adjustment");
		out[selected.?] += 1;
	}
	while (kraft(out) < KRAFT_FULL) {
		const deficit = KRAFT_FULL - kraft(out);
		var selected: ?usize = null;
		for (order) |sym| if (out[sym] > 1 and (@as(u32, 1) << @intCast(15 - out[sym])) <= deficit) {
			if (selected == null or freq[sym] > freq[selected.?] or
				(freq[sym] == freq[selected.?] and out[sym] < out[selected.?])) selected = sym;
		};
		if (selected == null) @panic("tree completion has no legal adjustment");
		out[selected.?] -= 1;
	}
	if (kraft(out) != KRAFT_FULL) @panic("tree completion did not fill the code space");
}
pub fn applyFloor(dist_full: *[30]u8, floor: u8) void {
	if (floor < 2) return;
	var used: ?usize = null;
	var n: usize = 0;
	for (dist_full, 0..) |l, i| {
		if (l != 0) {
			n += 1;
			used = i;
		}
	}
	if (n != 1) return;
	dist_full[used.?] = 1;
	dist_full[if (used.? == 0) 1 else 0] = 1;
}


pub fn trim(lengths: []const u8, floor: usize) []const u8 {
	std.debug.assert(floor <= lengths.len);
	var n = lengths.len;
	while (n > floor and lengths[n - 1] == 0) n -= 1;
	return lengths[0..n];
}
pub fn runCosts(value: u8, prices: *const [19]i64) *const [MAX_CL_SEQ + 1]u16 {
	return if (value == 0)
		&zeroRunTable(@intCast(prices[0]), @intCast(prices[16]), @intCast(prices[17]), @intCast(prices[18])).costs
	else &nonzero_run_tables[@intCast(prices[value])][@intCast(prices[16])].costs;
}

pub const Memo = struct {
	const Slot = struct {
		valid: bool = false,
		ll_len: u16 = 0,
		dist_len: u16 = 0,
		mode: Header = .full,
		extra_seeds: bool = false,
		lengths: [320]u8 = undefined,
		entries: [321]ClEntry = undefined,
		entry_count: u16 = 0,
		cl_lengths: [19]u8 = undefined,
		header_bits: i64 = 0,
	};
	allocator: A,
	slots: []Slot,
	hits: u64 = 0,
	misses: u64 = 0,
	evictions: u64 = 0,
	pub fn init(a: A, capacity: usize) !Memo {
		if (capacity == 0) return error.InvalidCapacity;
		const slots = try a.alloc(Slot, capacity);
		for (slots) |*entry| entry.valid = false;
		return .{ .allocator = a, .slots = slots };
	}
	pub fn deinit(self: *Memo) void {
		self.allocator.free(self.slots);
		self.* = undefined;
	}
	pub fn storageBytes(self: *const Memo) usize { return self.slots.len * @sizeOf(Slot); }
	fn slot(self: *Memo, ll: []const u8, dist: []const u8, mode: Header, extra_seeds: bool) *Slot {
		var hash = std.hash.Wyhash.init(0);
		hash.update(&.{ @intCast(ll.len & 255), @intCast(ll.len >> 8), @intCast(dist.len), @intFromEnum(mode), @intFromBool(extra_seeds) });
		hash.update(ll);
		hash.update(dist);
		return &self.slots[hash.final() % self.slots.len];
	}

};
test "encoding memo: exact keys, collisions and result ownership" {
	const a = std.testing.allocator;
	var arena = std.heap.ArenaAllocator.init(a);
	defer arena.deinit();
	const scratch = arena.allocator();
	// One slot forces eviction on every distinct key.
	var memo = try Memo.init(a, 1);
	defer memo.deinit();
	var builder = Builder{ .memo = &memo };
	var ll = [_]u8{0} ** (common.EOB + 1);
	ll[65] = 1;
	ll[common.EOB] = 1;
	const dist = [_]u8{1};
	for ([_]bool{ false, true }) |t24| {
		builder.extra_seeds = t24;
		for ([_]Header{ .search, .full, .crossing }) |mode| {
			const expected = try buildClUncached(builder, scratch, &ll, &dist, mode);
			const misses = memo.misses;
			var first = try builder.header(scratch, &ll, &dist, mode);
			try std.testing.expectEqual(misses + 1, memo.misses);
			// A caller may mutate its materialized result; this must not
			// corrupt the memo's owned copy or a later returned copy.
			first.entries.items[0].val +%= 1;
			const hits = memo.hits;
			const second = try builder.header(scratch, &ll, &dist, mode);
			try std.testing.expectEqual(hits + 1, memo.hits);
			try std.testing.expectEqualDeep(expected.entries.items, second.entries.items);
			try std.testing.expectEqual(expected.cl_lengths, second.cl_lengths);
			try std.testing.expectEqual(expected.header_bits, second.header_bits);
		}
	}
	// Same concatenated bytes but different section boundaries must miss.
	const joined = [_]u8{ 1, 1, 1 };
	_ = try builder.header(scratch, joined[0..2], joined[2..], .full);
	const misses = memo.misses;
	_ = try builder.header(scratch, joined[0..1], joined[1..], .full);
	try std.testing.expectEqual(misses + 1, memo.misses);
	try std.testing.expect(memo.evictions > 0);
	builder.memo = null;
	_ = try builder.header(scratch, &ll, &dist, .full);
	try std.testing.expectEqual(misses + 1, memo.misses);
}

test "tree completion exposes occurrence and symbol tie orders" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	const tokens = [_]Token{ .{ .lit = 2 }, .{ .lit = 0 }, .{ .lit = 3 }, .{ .lit = 1 } };
	const builder = Builder{};
	var previous = (try builder.complete(a, &tokens, true, .{})).body.huff;
	@memset(previous.ll_lengths, 0);
	for ([_]usize{ 0, 1, 2, 3, common.EOB }) |sym| previous.ll_lengths[sym] = 3;
	const occurrence = try builder.complete(a, &tokens, true, .{ .trees = .{ .merge = .{ .previous = previous } } });
	const symbol = try builder.complete(a, &tokens, true, .{ .trees = .{ .merge = .{ .previous = previous, .order = .symbol } } });
	try std.testing.expectEqual(@as(u8, 1), occurrence.body.huff.ll_lengths[common.EOB]);
	try std.testing.expectEqual(@as(u8, 1), symbol.body.huff.ll_lengths[0]);
}

test "completed encodings agree with assembly across construction choices" {
	const tokens = [_]Token{ .{ .lit = 65 }, .{ .match = .{ .length = 258, .distance = 1 } }, .{ .lit = 66 }, .{ .match = .{ .length = 17, .distance = 2 } } };
	for ([_][]const Token{ &.{}, tokens[0..1], &tokens }) |ts| {
		for (0..3) |floor| for ([_]bool{ false, true }) |extra| {
			var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
			defer arena.deinit();
			const a = arena.allocator();
			const builder = Builder{ .floor = @intCast(floor), .extra_seeds = extra };
			var prior = (try builder.complete(a, ts, true, .{})).body.huff;
			prior.encoding = .{};
			for ([_]Header{ .greedy, .search, .full, .crossing }) |header_mode| {
				for ([_]Trees{ .{ .fresh = .standard }, .{ .fresh = .alternate }, .{ .fresh = .alternate_unit },
					.{ .merge = .{ .previous = prior } }, .{ .merge = .{ .previous = prior, .order = .symbol } } }) |trees| {
					const block = try builder.complete(a, ts, true, .{ .trees = trees, .header = header_mode });
					const h = block.body.huff;
					try std.testing.expect(h.encoding == null);
					try std.testing.expect(h.tokens.ptr == ts.ptr);
					var used: usize = 0;
					for (h.dist_lengths) |l| { if (l != 0) used += 1; }
					try std.testing.expect(used >= floor);
					var bytes: std.ArrayList(u8) = .empty;
					var w = common.BitWriter.init(&bytes, a);
					try deflasm.assembleBlock(&w, block);
					try std.testing.expectEqual(@as(i64, @intCast(w.totalBits())), try bitCost(h));
					try w.alignByte();
					var reader = common.BitReader{ .data = bytes.items };
					const parsed = try deflasm.parseBlock(&reader, a);
					try std.testing.expectEqual(ts.len, parsed.body.huff.tokens.len);
					for (ts, parsed.body.huff.tokens) |want, got| {
						try std.testing.expectEqual(std.meta.activeTag(want), std.meta.activeTag(got));
						switch (want) {
							.lit => |v| try std.testing.expectEqual(v, got.lit),
							.match => |m| {
								try std.testing.expectEqual(m.length, got.match.length);
								try std.testing.expectEqual(m.distance, got.match.distance);
							},
						}
					}
				}
			}
		};
	}
}
