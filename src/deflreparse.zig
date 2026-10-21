//! Shared bounded LZ77 reparse primitives. The caller owns search/acceptance policy.
const std = @import("std");
const opt = @import("deflopt.zig");
const deflasm = @import("deflasm.zig");
const ir = @import("deflir.zig");
const common = @import("deflcommon.zig");
const A = std.mem.Allocator;
const Token = deflasm.Token;
fn ensure(ok: bool) void {
	if (!ok) @panic("reparse invariant violated");
}
pub fn trim(lens: []const u8, floor: usize) []const u8 {
	var n = lens.len;
	while (n > floor and lens[n - 1] == 0) n -= 1;
	return lens[0..n];
}
pub const Edge = ir.Edge;
pub const Edges = ir.Graph;
fn matchLengthFrom(raw: []const u8, src: usize, pos: usize, limit: usize, known: usize) u16 {
	var n = known;
	// Both operands stay inside `raw`: n + 32 <= limit <= raw.len - pos and src < pos.
	const W = 32;
	while (n + W <= limit) : (n += W) {
		const a: @Vector(W, u8) = raw[src + n ..][0..W].*;
		const b: @Vector(W, u8) = raw[pos + n ..][0..W].*;
		const differing: u32 = @bitCast(a != b);
		if (differing != 0) return @intCast(n + @ctz(differing));
	}
	while (n + 8 <= limit) : (n += 8) {
		const different = std.mem.readInt(u64, raw[src + n ..][0..8], .little) ^ std.mem.readInt(u64, raw[pos + n ..][0..8], .little);
		if (different != 0) return @intCast(n + @ctz(different) / 8);
	}
	while (n < limit and raw[src + n] == raw[pos + n]) : (n += 1) {}
	return @intCast(n);
}
fn matchLength(raw: []const u8, src: usize, pos: usize, limit: usize) u16 {
	return matchLengthFrom(raw, src, pos, limit, 3);
}
// Prefix occurrences are grouped in position order. This exposes the same
// nearest 1024/window-limited source set as the reference hash chain, while
// allowing a saturated distance class to skip its remaining occurrences.
fn lowerPosition(positions: []const u32, from: usize, until: usize, value: usize) usize {
	var lo = from;
	var hi = until;
	while (lo < hi) {
		const mid = lo + (hi - lo) / 2;
		if (positions[mid] < value) lo = mid + 1 else hi = mid;
	}
	return lo;
}
fn prefix(raw: []const u8, i: usize) u32 {
	return @as(u32, raw[i]) | (@as(u32, raw[i + 1]) << 8) | (@as(u32, raw[i + 2]) << 16);
}
pub fn candidates(a: A, raw: []const u8) !Edges {
	return candidatesWithHistory(a, raw, &.{});
}

/// Three-byte-prefix occurrences grouped in position order, with the cursor
/// of each group advanced past the history so a block position's eligible
/// sources are exactly the occurrences before it.
const PrefixIndex = struct {
	const Group = struct { start: usize = 0, count: usize = 0, cursor: usize = 0 };
	joined: []const u8,
	count: usize,
	positions: []u32,
	groups: std.AutoHashMapUnmanaged(u32, Group),

	fn build(sa: A, program: ir.Program) !PrefixIndex {
		const joined = program.bytes;
		const count = joined.len - @min(joined.len, 2);
		const positions = try sa.alloc(u32, count);
		var groups: std.AutoHashMapUnmanaged(u32, Group) = .empty;
		for (0..count) |i| {
			const entry = try groups.getOrPut(sa, prefix(joined, i));
			if (!entry.found_existing) entry.value_ptr.* = .{};
			entry.value_ptr.count += 1;
		}
		var start: usize = 0;
		var group_it = groups.valueIterator();
		while (group_it.next()) |group| {
			group.start = start;
			start += group.count;
		}
		ensure(start == count);
		for (0..count) |i| {
			const group = groups.getPtr(prefix(joined, i)).?;
			positions[group.start + group.cursor] = @intCast(i);
			group.cursor += 1;
		}
		group_it = groups.valueIterator();
		while (group_it.next()) |group| group.cursor = 0;
		// Include sources whose three-byte prefix straddles the block boundary;
		// overlapping DEFLATE copies may legally read their own produced bytes.
		for (0..@min(program.history, count)) |i| groups.getPtr(prefix(joined, i)).?.cursor += 1;
		return .{ .joined = joined, .count = count, .positions = positions, .groups = groups };
	}

	const Range = struct { lower: usize, rank: usize, cut: bool };

	/// Eligible source indices for position `i`: the nearest `cap` prefix
	/// occurrences, then those inside the 32768-byte window. Advances the cursor.
	fn eligible(self: *PrefixIndex, i: usize, raw_len: usize) Range {
		const group = self.groups.getPtr(prefix(self.joined, i)).?;
		const rank = group.start + group.cursor;
		const cap = if (raw_len > 3000) @min(group.cursor, 1024) else group.cursor;
		var lower = rank - cap;
		const window_start = i - @min(i, common.WINDOW_SIZE);
		const cut = lower > group.start and self.positions[lower - 1] >= window_start;
		if (lower < rank and self.positions[lower] < window_start) lower = lowerPosition(self.positions, lower, rank, window_start);
		group.cursor += 1;
		return .{ .lower = lower, .rank = rank, .cut = cut };
	}
};

pub fn candidatesWithHistory(a: A, raw: []const u8, prior: []const u8) !Edges {
	return candidatesForProgram(a, try ir.Program.init(a, raw, prior));
}

pub fn candidatesForProgram(a: A, program: ir.Program) !Edges {
	const raw = program.raw();
	const prior = program.prior();
	ensure(prior.len <= common.WINDOW_SIZE);
	ensure(raw.len <= std.math.maxInt(u32) - prior.len);
	var scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer scratch.deinit();
	const sa = scratch.allocator();
	var index = try PrefixIndex.build(sa, program);
	const joined = index.joined;
	const positions = index.positions;
	const offsets = try a.alloc(usize, raw.len + 1);
	var items: std.ArrayList(Edge) = .empty;
	defer items.deinit(std.heap.page_allocator);
	var cut: usize = 0;
	for (0..raw.len) |pos| {
		const i = prior.len + pos;
		offsets[pos] = items.items.len;
		if (i >= index.count) continue;
		const range = index.eligible(i, raw.len);
		if (range.cut) cut += 1;
		var best = [_]Edge{.{ .distance = 0, .length = 0 }} ** 30;
		const limit = @min(@as(usize, common.MAX_MATCH_LENGTH), raw.len - pos);
		// Read only where a source can need it: old >= 8 implies limit > 8.
		const head: u64 = if (limit >= 8) std.mem.readInt(u64, joined[i..][0..8], .little) else 0;
		// Sources arrive nearest first, so the distance symbol only grows.
		var dc: usize = 0;
		var class_end: usize = 1;
		var j = range.rank;
		while (j > range.lower) {
			j -= 1;
			const src: usize = positions[j];
			const d = i - src;
			while (d > class_end) {
				dc += 1;
				class_end = @as(usize, common.DIST_BASE[dc]) + (@as(usize, 1) << common.DIST_EXTRA[dc]) - 1;
			}
			std.debug.assert(common.distCodeTable[d].code == dc);
			const old = best[dc].length;
			ensure(old < limit); // Saturated classes are skipped as a unit.
			var n: usize = undefined;
			if (old >= 8) {
				// An improving source must match the first eight bytes and
				// the last eight of the known prefix, including the first
				// byte beyond it. Both checks are required; the head first
				// rejects short matches with one load.
				if (std.mem.readInt(u64, joined[src..][0..8], .little) != head) continue;
				const tail = old - 7;
				if (std.mem.readInt(u64, joined[src + tail ..][0..8], .little) != std.mem.readInt(u64, joined[i + tail ..][0..8], .little)) continue;
				n = matchLengthFrom(joined, src, i, limit, 8);
			} else {
				if (old >= 3 and joined[src + old] != joined[i + old]) continue;
				n = matchLengthFrom(joined, src, i, limit, 3);
			}
			if (n > old) best[dc] = .{ .distance = @intCast(d), .length = @intCast(n) };
			if (n == limit) {
				// No older source in this distance-symbol interval can
				// improve its nearest longest edge. The eligible prefix
				// count/cap was fixed above, so skipping cannot extend it.
				j = if (i <= class_end) range.lower else lowerPosition(positions, range.lower, j, i - class_end);
			}
		}
		// Distance-symbol intervals are disjoint and ordered, so this is
		// already the reference's ascending-distance DP tie order.
		for (best) |edge| if (edge.length != 0) try items.append(std.heap.page_allocator, edge);
	}
	offsets[raw.len] = items.items.len;
	return .{ .program = program, .offsets = offsets, .items = try a.dupe(Edge, items.items), .cut_positions = cut };
}

/// The previous production matcher, retained as the differential oracle: a
/// table lookup for every source's distance symbol, word-wise extension, and
/// the class record's length carried to the next position as a lower bound.
fn candidatesReference(a: A, raw: []const u8, prior: []const u8) !Edges {
	ensure(prior.len <= common.WINDOW_SIZE);
	ensure(raw.len <= std.math.maxInt(u32) - prior.len);
	var scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer scratch.deinit();
	const sa = scratch.allocator();
	const program = try ir.Program.init(a, raw, prior);
	var index = try PrefixIndex.build(sa, program);
	const joined = index.joined;
	const positions = index.positions;
	const offsets = try a.alloc(usize, raw.len + 1);
	var items: std.ArrayList(Edge) = .empty;
	defer items.deinit(std.heap.page_allocator);
	var cut: usize = 0;
	var previous = [_]Edge{.{ .distance = 0, .length = 0 }} ** 30;
	for (0..raw.len) |pos| {
		const i = prior.len + pos;
		offsets[pos] = items.items.len;
		if (i >= index.count) continue;
		const range = index.eligible(i, raw.len);
		if (range.cut) cut += 1;
		var best = [_]Edge{.{ .distance = 0, .length = 0 }} ** 30;
		const limit = @min(@as(usize, common.MAX_MATCH_LENGTH), raw.len - pos);
		var j = range.rank;
		while (j > range.lower) {
			j -= 1;
			const src: usize = positions[j];
			const d: u16 = @intCast(i - src);
			const dc = common.distCodeTable[d];
			const old = best[dc.code].length;
			ensure(old < limit);
			if (old >= 8) {
				const tail = old - 7;
				if (std.mem.readInt(u64, joined[src + tail ..][0..8], .little) != std.mem.readInt(u64, joined[i + tail ..][0..8], .little)) continue;
				if (std.mem.readInt(u64, joined[src..][0..8], .little) != std.mem.readInt(u64, joined[i..][0..8], .little)) continue;
			} else if (old >= 3 and joined[src + old] != joined[i + old]) continue;
			const prev = previous[dc.code];
			const known = if (prev.distance == d) @max(@as(usize, 3), prev.length - 1) else 3;
			ensure(known <= limit);
			const n = matchLengthFrom(joined, src, i, limit, known);
			if (n > old) best[dc.code] = .{ .distance = d, .length = n };
			if (n == limit) {
				const end: usize = common.DIST_BASE[dc.code] + (@as(usize, 1) << @intCast(dc.extra)) - 1;
				j = if (i <= end) range.lower else lowerPosition(positions, range.lower, j, i - end);
			}
		}
		for (best) |edge| if (edge.length != 0) try items.append(std.heap.page_allocator, edge);
		previous = best;
	}
	offsets[raw.len] = items.items.len;
	return .{ .program = program, .offsets = offsets, .items = try a.dupe(Edge, items.items), .cut_positions = cut };
}

test "class tracking and vector extension reproduce the reference matcher" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	var prng = std.Random.DefaultPrng.init(0x6d61746368);
	const random = prng.random();
	const buf = try a.alloc(u8, common.WINDOW_SIZE + 12001);
	for (0..40) |trial| {
		// Small alphabets, periodic structure and long runs saturate the
		// 1024-occurrence cap and every distance class; sparse mutations
		// place match ends at every vector-lane offset.
		const n = if (trial % 4 == 0) 2000 + random.intRangeAtMost(usize, 0, 1500) else 3001 + random.intRangeAtMost(usize, 0, 9000);
		const prior_len = switch (trial % 5) {
			0 => 0,
			1 => random.intRangeAtMost(usize, 1, 40),
			2 => common.WINDOW_SIZE,
			else => random.intRangeAtMost(usize, 0, 5000),
		};
		const data = buf[0 .. prior_len + n];
		const alphabet = random.intRangeAtMost(u8, 1, 4);
		const period = random.intRangeAtMost(usize, 1, 300);
		for (data, 0..) |*v, k| v.* = @intCast((k % period) % alphabet + if (random.intRangeAtMost(u32, 0, 400) == 0) @as(usize, 7) else 0);
		if (trial % 3 == 0) @memset(data[data.len / 3 .. data.len / 2], 0);
		const prior = data[0..prior_len];
		const raw = data[prior_len..];
		const expected = try candidatesReference(a, raw, prior);
		const actual = try candidatesWithHistory(a, raw, prior);
		try std.testing.expectEqualSlices(usize, expected.offsets, actual.offsets);
		try std.testing.expectEqualSlices(Edge, expected.items, actual.items);
		try std.testing.expectEqual(expected.cut_positions, actual.cut_positions);
	}
}

test "history matcher includes boundary-straddling prefixes and overlapping sources" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	for ([_][]const u8{ "a", "ab", "xyabab", "abcde", "aaaaaaaa" }) |prior| {
		for ([_][]const u8{ "", "a", "ab", "abababababa", "aaaaaaaaaaaa", "abcdeabcde" }) |raw| {
			const joined = try std.mem.concat(a, u8, &.{ prior, raw });
			const got = try candidatesWithHistory(a, raw, prior);
			for (0..raw.len) |pos| {
				const i = prior.len + pos;
				var expected = [_]Edge{.{ .distance = 0, .length = 0 }} ** 30;
				for (1..@min(i, common.WINDOW_SIZE) + 1) |distance| {
					var n: usize = 0;
					while (n < common.MAX_MATCH_LENGTH and pos + n < raw.len and joined[i - distance + n] == joined[i + n]) n += 1;
					const sym = common.distCodeTable[distance].code;
					if (n >= 3 and n > expected[sym].length) expected[sym] = .{ .distance = @intCast(distance), .length = @intCast(n) };
				}
				var count: usize = 0;
				for (expected) |e| if (e.length != 0) { count += 1; };
				const actual = got.items[got.offsets[pos]..got.offsets[pos + 1]];
				try std.testing.expectEqual(count, actual.len);
				for (actual) |e| try std.testing.expectEqualDeep(expected[common.distCodeTable[e.distance].code], e);
			}
		}
	}
}

test "history matcher reaches distance 32768 and drops it as the window advances" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	const prior = try a.alloc(u8, common.WINDOW_SIZE);
	@memset(prior, 0);
	@memcpy(prior[0..4], "abca");
	const got = try candidatesWithHistory(a, "abca", prior);
	try std.testing.expectEqual(@as(usize, 1), got.offsets[1]);
	try std.testing.expectEqualDeep(Edge{ .distance = common.WINDOW_SIZE, .length = 4 }, got.items[0]);
	// At offset one the same source is too far away; the shifted source
	// (prior[1]) is still exactly 32768 bytes behind and matches three bytes.
	try std.testing.expectEqual(@as(usize, 2), got.offsets[2]);
	try std.testing.expectEqualDeep(Edge{ .distance = common.WINDOW_SIZE, .length = 3 }, got.items[1]);
	const expired = try candidatesWithHistory(a, "xabca", prior);
	try std.testing.expectEqual(@as(usize, 0), expired.items.len);
}

pub const Counts = struct {
	ll: [286]u32 = @splat(0),
	dist: [30]u32 = @splat(0),
	ll_order: [286]u16 = undefined,
	d_order: [30]u16 = undefined,
	nl: usize = 0,
	nd: usize = 0,
	fn add(c: *Counts, sym: usize, distance: bool) void {
		if (distance) {
			if (c.dist[sym] == 0) {
				c.d_order[c.nd] = @intCast(sym);
				c.nd += 1;
			}
			c.dist[sym] += 1;
		} else {
			if (c.ll[sym] == 0) {
				c.ll_order[c.nl] = @intCast(sym);
				c.nl += 1;
			}
			c.ll[sym] += 1;
		}
	}
};
pub fn counts(ts: []const Token, ll: []const u8) Counts {
	var c: Counts = .{};
	c.add(common.EOB, false);
	for (ts) |t| switch (t) {
		.lit => |b| c.add(b, false),
		.match => |m| {
			const code = if (m.length == common.MAX_MATCH_LENGTH and (ll.len <= 285 or ll[285] == 0)) 284 else common.lenCodeTable[m.length].code;
			c.add(code, false);
			c.add(common.distCodeTable[m.distance].code, true);
		},
	};
	return c;
}
const KRAFT_FULL: u32 = 1 << 15; // Kraft sum in 2^-15 units

fn kraft(lens: []const u8) u32 {
	var sum: u32 = 0;
	for (lens) |l| if (l != 0) {
		ensure(l <= 15);
		sum += @as(u32, 1) << @intCast(15 - l);
	};
	return sum;
}
pub fn mergeTree(prev: []const u8, freq: []const u32, order: []const u16, out: []u8) void {
	opt.freqToLengths(freq, 15, out);
	for (order) |sym| if (sym < prev.len and prev[sym] != 0) {
		out[sym] = prev[sym];
	};
	if (order.len == 1) {
		out[order[0]] = 1;
		return;
	}
	// Stable ties follow Counter insertion order, not symbol order.
	while (kraft(out) > KRAFT_FULL) {
		var selected: ?usize = null;
		for (order) |sym| if (out[sym] < 15) {
			if (selected == null or freq[sym] < freq[selected.?] or
				(freq[sym] == freq[selected.?] and out[sym] > out[selected.?])) selected = sym;
		};
		ensure(selected != null);
		out[selected.?] += 1;
	}
	while (kraft(out) < KRAFT_FULL) {
		const deficit = KRAFT_FULL - kraft(out);
		var selected: ?usize = null;
		for (order) |sym| if (out[sym] > 1 and (@as(u32, 1) << @intCast(15 - out[sym])) <= deficit) {
			if (selected == null or freq[sym] > freq[selected.?] or
				(freq[sym] == freq[selected.?] and out[sym] < out[selected.?])) selected = sym;
		};
		ensure(selected != null);
		out[selected.?] -= 1;
	}
	ensure(kraft(out) == KRAFT_FULL);
}
/// Matchless distance tree under the production floor (opt.min_dist_codes).
pub fn emptyCl(a: A, ll: []const u8) !opt.EmptyDistCl {
	return opt.emptyDistCl(a, ll, .full);
}
fn header(scratch: *std.heap.ArenaAllocator, ll: []const u8, d: []const u8) !i64 {
	defer _ = scratch.reset(.retain_capacity);
	const a = scratch.allocator();
	const lt = trim(ll, common.EOB + 1);
	const dt = trim(d, 1);
	var any = false;
	for (dt) |l| {
		any = any or l != 0;
	}
	return if (any) (try opt.buildClSearch(a, lt, dt)).header_bits else (try emptyCl(a, lt)).built.header_bits;
}
pub const Prices = struct { ll: [286]f64, dist: [30]f64 };
pub fn prices(a: A, h: deflasm.Huff, c: Counts, scale: f64, literal_bytes: [256]bool) !Prices {
	var ll_buf: [288]u8 = @splat(0);
	var d_buf: [32]u8 = @splat(0);
	const ll = ll_buf[0..if (h.is_fixed) @as(usize, 288) else 286];
	const d = d_buf[0..if (h.is_fixed) @as(usize, 32) else 30];
	if (h.is_fixed) {
		@memcpy(ll, &common.fixed_ll_lengths);
		@memcpy(d, &common.fixed_dist_lengths);
	} else {
		@memcpy(ll[0..h.ll_lengths.len], h.ll_lengths);
		@memcpy(d[0..h.dist_lengths.len], h.dist_lengths);
	}
	var scratch = std.heap.ArenaAllocator.init(a);
	defer scratch.deinit();
	const le = @max(std.mem.max(u8, ll), 1);
	const de = if (std.mem.max(u8, d) == 0) 5 else std.mem.max(u8, d);
	var p: Prices = undefined;
	if (scale == 0) {
		for (ll[0..286], &p.ll) |v, *price| price.* = @floatFromInt(if (v == 0) le else v);
		for (d[0..30], &p.dist) |v, *price| price.* = @floatFromInt(if (v == 0) de else v);
		return p;
	}
	const base = try header(&scratch, ll, d);
	for (0..286) |sym| {
		if (sym == common.EOB or (sym < common.EOB and !literal_bytes[sym] and ll[sym] == 0)) {
			p.ll[sym] = @floatFromInt(if (ll[sym] == 0) le else ll[sym]);
			continue;
		}
		const saved = ll[sym];
		ll[sym] = if (saved == 0) le else 0;
		const hc = try header(&scratch, ll, d);
		ll[sym] = saved;
		const delta: f64 = @floatFromInt(if (saved == 0) hc - base else base - hc);
		p.ll[sym] = @as(f64, @floatFromInt(if (saved == 0) le else saved)) + scale * delta / @as(f64, @floatFromInt(@max(c.ll[sym], 1)));
	}
	for (0..30) |sym| {
		const saved = d[sym];
		d[sym] = if (saved == 0) de else 0;
		const hc = try header(&scratch, ll, d);
		d[sym] = saved;
		const delta: f64 = @floatFromInt(if (saved == 0) hc - base else base - hc);
		p.dist[sym] = @as(f64, @floatFromInt(if (saved == 0) de else saved)) + scale * delta / @as(f64, @floatFromInt(@max(c.dist[sym], 1)));
	}
	return p;
}
pub const Parse = struct { tokens: []Token, predicted: f64 };
pub fn parse(a: A, edges: Edges, p: Prices) !Parse {
	const raw = edges.program.raw();
	// Finite external scales may overflow the derived prices or path costs.
	for (p.ll) |price| if (!std.math.isFinite(price)) return error.NonFiniteCost;
	for (p.dist) |price| if (!std.math.isFinite(price)) return error.NonFiniteCost;
	const costs = try a.alloc(f64, raw.len + 1);
	@memset(costs, std.math.inf(f64));
	costs[0] = 0;
	// The winning edge into each position, split so the relaxation can blend
	// lanes; a literal is length 1 at distance 0.
	const back_len = try a.alloc(u16, raw.len + 1);
	const back_dist = try a.alloc(u16, raw.len + 1);
	var lp: [259]f64 = @splat(0);
	for (3..259) |n| lp[n] = p.ll[common.lenCodeTable[n].code] + @as(f64, @floatFromInt(common.lenCodeTable[n].extra));
	const W = 8;
	const lane_offsets: @Vector(W, u16) = std.simd.iota(u16, W);
	for (raw, 0..) |b, i| {
		const ci = costs[i];
		if (!std.math.isFinite(ci)) return error.NonFiniteCost;
		const lit = ci + p.ll[b];
		if (lit < costs[i + 1]) {
			costs[i + 1] = lit;
			back_len[i + 1] = 1;
			back_dist[i + 1] = 0;
		}
		const Frontier = struct { base: f64, length: u16 };
		var frontier: [30]Frontier = undefined;
		var used: usize = 0;
		for (edges.at(i)) |e| {
			const dc = common.distCodeTable[e.distance];
			const base = ci + p.dist[dc.code] + @as(f64, @floatFromInt(dc.extra));
			var covered: usize = 2;
			for (frontier[0..used]) |old| {
				if (old.base <= base) covered = @max(covered, old.length);
			}
			// Sources are visited in the original nearest-first tie order.
			// IEEE addition is monotone: old.base <= base also implies
			// old.base + lp[n] <= base + lp[n]. The earlier source already
			// offered this whole prefix; a tie must continue to retain it.
			if (covered >= e.length) continue;
			var keep: usize = 0;
			for (frontier[0..used]) |old| {
				if (base <= old.base and e.length >= old.length) continue;
				frontier[keep] = old;
				keep += 1;
			}
			ensure(keep < frontier.len);
			frontier[keep] = .{ .base = base, .length = e.length };
			used = keep + 1;
			// Each length relaxes its own target, so lanes are independent and
			// the strict comparison keeps the scalar loop's first-winner ties.
			var n: usize = covered + 1;
			const end: usize = @as(usize, e.length) + 1;
			const base_v: @Vector(W, f64) = @splat(base);
			const dist_v: @Vector(W, u16) = @splat(e.distance);
			while (n + W <= end) : (n += W) {
				const cost_v = base_v + @as(@Vector(W, f64), lp[n..][0..W].*);
				const cur_v: @Vector(W, f64) = costs[i + n ..][0..W].*;
				const better = cost_v < cur_v;
				if (@reduce(.Or, better)) {
					costs[i + n ..][0..W].* = @select(f64, better, cost_v, cur_v);
					const len_v = @as(@Vector(W, u16), @splat(@intCast(n))) + lane_offsets;
					back_len[i + n ..][0..W].* = @select(u16, better, len_v, back_len[i + n ..][0..W].*);
					back_dist[i + n ..][0..W].* = @select(u16, better, dist_v, back_dist[i + n ..][0..W].*);
				}
			}
			while (n < end) : (n += 1) {
				const cost = base + lp[n];
				if (cost < costs[i + n]) {
					costs[i + n] = cost;
					back_len[i + n] = @intCast(n);
					back_dist[i + n] = e.distance;
				}
			}
		}
	}
	const predicted = costs[raw.len] + p.ll[common.EOB];
	if (!std.math.isFinite(predicted)) return error.NonFiniteCost;
	var ts: std.ArrayList(Token) = .empty;
	var i = raw.len;
	while (i != 0) {
		const length = back_len[i];
		const distance = back_dist[i];
		ensure(length > 0 and length <= i);
		try ts.append(a, if (distance == 0) .{ .lit = raw[i - 1] } else .{ .match = .{ .length = length, .distance = distance } });
		i -= length;
	}
	std.mem.reverse(Token, ts.items);
	return .{ .tokens = ts.items, .predicted = predicted };
}
pub fn materialize(a: A, ts: []Token, prev: ?deflasm.Huff, is_last: bool) !deflasm.Block {
	return materializeOrdered(a, ts, prev, is_last, false);
}

/// Feedback completions merge trees in symbol order. The main reparse walk
/// uses first-occurrence order instead; both retain their own tie ordering.
pub fn materializeBySymbol(a: A, ts: []Token, prev: ?deflasm.Huff, is_last: bool) !deflasm.Block {
	return materializeOrdered(a, ts, prev, is_last, true);
}

fn materializeOrdered(a: A, ts: []Token, prev: ?deflasm.Huff, is_last: bool, comptime by_symbol: bool) !deflasm.Block {
	var block = try opt.makeDynamicBlock(a, ts, is_last, false, false);
	if (prev) |h| {
		var c = counts(ts, h.ll_lengths);
		if (by_symbol) {
			std.mem.sort(u16, c.ll_order[0..c.nl], {}, std.sort.asc(u16));
			std.mem.sort(u16, c.d_order[0..c.nd], {}, std.sort.asc(u16));
		}
		var ll: [286]u8 = undefined;
		var d: [30]u8 = undefined;
		mergeTree(h.ll_lengths, &c.ll, c.ll_order[0..c.nl], &ll);
		var b = &block.body.huff;
		b.ll_lengths = try a.dupe(u8, trim(&ll, common.EOB + 1));
		if (c.nd != 0) {
			mergeTree(h.dist_lengths, &c.dist, c.d_order[0..c.nd], &d);
			opt.distFloor(&d);
			b.dist_lengths = try a.dupe(u8, trim(&d, 1));
			const cl = try opt.buildClCrossing(a, b.ll_lengths, b.dist_lengths);
			b.cl_entries = cl.entries.items;
			b.cl_lengths = cl.cl_lengths;
		} else {
			const e = try emptyCl(a, b.ll_lengths);
			b.dist_lengths = try a.dupe(u8, e.dist);
			b.cl_entries = e.built.entries.items;
			b.cl_lengths = e.built.cl_lengths;
		}
	}
	return block;
}
test "match edges preserve nearest longest sources and overlapping copies" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	const raw = "ababababcdababababcdzzabababa";
	const got = try candidates(a, raw);
	for (0..raw.len) |i| {
		var expected = [_]Edge{.{ .distance = 0, .length = 0 }} ** 30;
		for (1..i + 1) |distance| {
			var length: usize = 0;
			while (length < common.MAX_MATCH_LENGTH and i + length < raw.len and raw[i - distance + length] == raw[i + length]) length += 1;
			const ds = common.distCodeTable[distance].code;
			if (length >= 3 and length > expected[ds].length) expected[ds] = .{ .distance = @intCast(distance), .length = @intCast(length) };
		}
		var n: usize = 0;
		for (expected) |edge| if (edge.length > 0) {
			n += 1;
		};
		const actual = got.items[got.offsets[i]..got.offsets[i + 1]];
		try std.testing.expectEqual(n, actual.len);
		for (actual) |edge| try std.testing.expectEqualDeep(expected[common.distCodeTable[edge.distance].code], edge);
	}
}
test "large matcher keeps nearest 1024 prefix occurrences" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	const raw = try a.alloc(u8, 3001);
	@memset(raw, 'x');
	const got = try candidates(a, raw);
	try std.testing.expect(got.cut_positions > 0);
	for (1..raw.len - 2) |i| {
		const es = got.items[got.offsets[i]..got.offsets[i + 1]];
		var expected: usize = 0;
		for (common.DIST_BASE) |base| if (base <= @min(i, 1024)) {
			expected += 1;
		};
		try std.testing.expectEqual(expected, es.len);
		for (es, 0..) |e, j| {
			try std.testing.expectEqual(common.DIST_BASE[j], e.distance);
			try std.testing.expectEqual(@min(common.MAX_MATCH_LENGTH, raw.len - i), e.length);
		}
	}
}
test "tree completion uses insertion order to break equal-frequency ties" {
	const freq = [_]u32{ 1, 1, 1, 1 };
	const prev = [_]u8{ 3, 3, 3, 3 };
	var out: [4]u8 = undefined;
	mergeTree(&prev, &freq, &.{ 2, 0, 3, 1 }, &out);
	try std.testing.expectEqualDeep([_]u8{ 2, 3, 1, 3 }, out);
	try std.testing.expectEqual(@as(u32, KRAFT_FULL), kraft(&out));
}

test "indexed sources keep the prefix cap and 32768-byte window independent" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	const raw = try a.alloc(u8, 40000);
	for (raw, 0..) |*v, i| v.* = @intCast(i % 37);
	const got = try candidates(a, raw);
	// 32768/37 < 1024: there are more old occurrences, but they must not
	// count as a chain-cap cutoff after falling out of the window.
	try std.testing.expectEqual(@as(usize, 0), got.cut_positions);
	for ([_]usize{ common.MAX_MATCH_LENGTH, 3000, 32767, common.WINDOW_SIZE, 32769, 39740, 39996 }) |pos| {
		var expected = [_]Edge{.{ .distance = 0, .length = 0 }} ** 30;
		var visited: usize = 0;
		for (1..@min(pos, common.WINDOW_SIZE) + 1) |distance| {
			var n: usize = 0;
			while (n < common.MAX_MATCH_LENGTH and pos + n < raw.len and raw[pos - distance + n] == raw[pos + n]) n += 1;
			if (n < 3) continue;
			if (visited == 1024) break;
			visited += 1;
			const sym = common.distCodeTable[distance].code;
			if (n > expected[sym].length) expected[sym] = .{ .distance = @intCast(distance), .length = @intCast(n) };
		}
		const actual = got.items[got.offsets[pos]..got.offsets[pos + 1]];
		var count: usize = 0;
		for (expected) |e| if (e.length != 0) { count += 1; };
		try std.testing.expectEqual(count, actual.len);
		for (actual) |e| try std.testing.expectEqualDeep(expected[common.distCodeTable[e.distance].code], e);
	}
}

test "word match extension agrees with byte comparison including overlap and tails" {
	var raw: [600]u8 = undefined;
	for (&raw, 0..) |*v, i| v.* = @intCast(i % 7);
	for (3..259) |limit| {
		for (3..limit + 1) |mismatch| {
			const pos = 280;
			const saved = raw[pos + mismatch];
			raw[pos + mismatch] = 255;
			try std.testing.expectEqual(@as(u16, @intCast(@min(limit, mismatch))), matchLength(&raw, 0, pos, limit));
			raw[pos + mismatch] = saved;
		}
		// A source inside the match's output range is legal for repeated data.
		try std.testing.expectEqual(@as(u16, @intCast(limit)), matchLength(&raw, 0, 7, limit));
	}
}

test "vector relaxation matches the scalar DP on saturated runs" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	var prng = std.Random.DefaultPrng.init(0x72656c6178);
	const random = prng.random();
	const raw = try a.alloc(u8, 3000);
	for (0..12) |trial| {
		// Long equal runs give every position 258-length edges in many
		// distance classes, so the eight-wide path and its tails both run.
		for (raw, 0..) |*v, k| v.* = if (trial % 2 == 0) 0 else @intCast((k / (300 + trial)) % 3);
		if (trial >= 6) for (0..trial) |_| {
			raw[random.intRangeAtMost(usize, 0, raw.len - 1)] = 9;
		};
		const es = try candidates(a, raw);
		var p: Prices = undefined;
		for (&p.ll) |*v| v.* = @floatFromInt(random.intRangeAtMost(u32, 1, 15));
		for (&p.dist) |*v| v.* = @floatFromInt(random.intRangeAtMost(u32, 1, 15));
		const expected = try parseReference(a, raw, es, p);
		const actual = try parse(a, es, p);
		try std.testing.expectEqual(expected.predicted, actual.predicted);
		try std.testing.expectEqualDeep(expected.tokens, actual.tokens);
	}
}

test "dominated DP intervals retain scalar updates and floating-point ties" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	var raw: [420]u8 = undefined;
	for (&raw, 0..) |*v, i| v.* = @intCast((i % 51) % 7 + if (i % 59 == 0) @as(usize, 1) else 0);
	const es = try candidates(a, &raw);
	for (0..100) |trial| {
		var p: Prices = undefined;
		// Include negative prices, near-equal floats, decreasing distance
		// prices, and exactly equal costs; these must not reorder ties.
		const jitter: f64 = if (trial % 3 == 0) 1e-13 else 0.125;
		for (&p.ll, 0..) |*v, i| v.* = @as(f64, @floatFromInt(@as(i64, @intCast((i * 11 + trial) % 19)) - 3)) + jitter * @as(f64, @floatFromInt(i % 4));
		for (&p.dist, 0..) |*v, i| v.* = @as(f64, @floatFromInt(@as(i64, @intCast((30 - i + trial * 3) % 15)) - 4)) + jitter * @as(f64, @floatFromInt(i % 3));
		const expected = try parseReference(a, &raw, es, p);
		const actual = try parse(a, es, p);
		try std.testing.expectEqual(expected.predicted, actual.predicted);
		try std.testing.expectEqualDeep(expected.tokens, actual.tokens);
	}
}

fn parseReference(a: A, raw: []const u8, edges: Edges, p: Prices) !Parse {
	// Finite external scales may overflow the derived prices or path costs.
	for (p.ll) |price| if (!std.math.isFinite(price)) return error.NonFiniteCost;
	for (p.dist) |price| if (!std.math.isFinite(price)) return error.NonFiniteCost;
	const costs = try a.alloc(f64, raw.len + 1);
	@memset(costs, std.math.inf(f64));
	costs[0] = 0;
	const back = try a.alloc(Edge, raw.len + 1);
	var lp: [259]f64 = @splat(0);
	for (3..259) |n| lp[n] = p.ll[common.lenCodeTable[n].code] + @as(f64, @floatFromInt(common.lenCodeTable[n].extra));
	for (raw, 0..) |b, i| {
		const ci = costs[i];
		if (!std.math.isFinite(ci)) return error.NonFiniteCost;
		const lit = ci + p.ll[b];
		if (lit < costs[i + 1]) {
			costs[i + 1] = lit;
			back[i + 1] = .{ .length = 1, .distance = 0 };
		}
		for (edges.at(i)) |e| {
			const dc = common.distCodeTable[e.distance];
			const base = ci + p.dist[dc.code] + @as(f64, @floatFromInt(dc.extra));
			for (3..@as(usize, e.length) + 1) |n| {
				const cost = base + lp[n];
				if (cost < costs[i + n]) {
					costs[i + n] = cost;
					back[i + n] = .{ .length = @intCast(n), .distance = e.distance };
				}
			}
		}
	}
	const predicted = costs[raw.len] + p.ll[common.EOB];
	if (!std.math.isFinite(predicted)) return error.NonFiniteCost;
	var ts: std.ArrayList(Token) = .empty;
	var i = raw.len;
	while (i != 0) {
		const e = back[i];
		ensure(e.length > 0 and e.length <= i);
		try ts.append(a, if (e.distance == 0) .{ .lit = raw[i - 1] } else .{ .match = .{ .length = e.length, .distance = e.distance } });
		i -= e.length;
	}
	std.mem.reverse(Token, ts.items);
	return .{ .tokens = ts.items, .predicted = predicted };
}
