//! Joint block-boundary and token-choice search over one DEFLATE stream.
//!
//! Each Huffman block contributes its codebooks as a price model over its own
//! decoded span, extended by `slack` bytes on either side. The candidates at
//! a position are the stream's own: its literal, or the match the incumbent
//! parse starts there at any length down to three (a length-258 match by its
//! cheaper legal spelling). Under one model the cheapest choice over any span
//! is a shortest path, so boundaries and token choices are searched together
//! in one layered DP: state (position, model); token edges inside a layer
//! priced by that model's code lengths; a switch between models at any
//! position paid with the closing model's EOB and the opening model's header.
//! The pass merges, splits and shifts block boundaries, shortens matches at a
//! new boundary and respells tokens; whole blocks remain candidates, so a
//! run's own encoding is always reachable. When enabled, per-block reparsing
//! discovers new matches after this search. Stored blocks bound
//! the search: each maximal run of consecutive Huffman blocks is searched on
//! its own. A run is replaced only when the search is strictly cheaper than
//! its blocks' own bits. Segments reuse the model's parsed header fields with
//! the chosen tokens, so the assembler reproduces exactly the price paid.
//!
//! DP working rows are windowed; backtracking reruns windows from saved entry
//! rows. Checkpoints and decoded-stream storage remain live across windows.
const std = @import("std");
const deflasm = @import("deflasm.zig");
const common = @import("deflcommon.zig");

const Block = deflasm.Block;
const Token = deflasm.Token;

pub const Options = struct {
	/// Bytes a model may reach beyond its block on either side.
	slack: u32 = 16384,
	/// Positions per forward window; bounds the DP's working set.
	window: u32 = 1 << 18,
};

pub const Result = struct {
	blocks: []Block,
	/// Per output block: differs from the input block at its span (needs the per-block search).
	fresh: []bool,
	/// Bits of the replaced runs before and after; untouched blocks excluded.
	before: u64,
	after: u64,
};

pub const Decoded = struct { raw: []u8, starts: []u32 };

/// Decode a whole stream; `starts[i]` is block i's decoded offset, with a final end entry.
pub fn decode(a: std.mem.Allocator, blocks: []const Block) !Decoded {
	const starts = try startsOf(a, blocks);
	errdefer a.free(starts);
	const raw = try a.alloc(u8, starts[blocks.len]);
	errdefer a.free(raw);
	var pos: usize = 0;
	for (blocks, 0..) |b, i| {
		std.debug.assert(pos == starts[i]);
		switch (b.body) {
			.stored => |d| {
				@memcpy(raw[pos .. pos + d.len], d);
				pos += d.len;
			},
			.huff => |h| for (h.tokens) |t| switch (t) {
				.lit => |c| {
					raw[pos] = c;
					pos += 1;
				},
				.match => |m| {
					if (m.length < 3 or m.length > common.MAX_MATCH_LENGTH or m.distance == 0 or m.distance > pos) return error.Malformed;
					for (0..m.length) |_| {
						raw[pos] = raw[pos - m.distance];
						pos += 1;
					}
				},
			},
		}
	}
	std.debug.assert(pos == raw.len);
	return .{ .raw = raw, .starts = starts };
}

/// Block start offsets of a token stream whose decoded bytes are already known.
pub fn startsOf(a: std.mem.Allocator, blocks: []const Block) ![]u32 {
	const starts = try a.alloc(u32, blocks.len + 1);
	errdefer a.free(starts);
	var pos: usize = 0;
	for (blocks, 0..) |b, i| {
		starts[i] = @intCast(pos);
		pos = std.math.add(usize, pos, try b.decodedLength()) catch return error.Malformed;
		if (pos > std.math.maxInt(u32) - 2 * common.MAX_MATCH_LENGTH) return error.Malformed;
	}
	starts[blocks.len] = @intCast(pos);
	return starts;
}

/// The match each decoded position starts in a parse (0: none). Built once
/// per round from the incumbent; later iterations only shorten or drop these.
pub const Edges = struct { len: []u16, dist: []u16 };

pub fn edgesOf(a: std.mem.Allocator, blocks: []const Block, dec: Decoded) !Edges {
	const len = try a.alloc(u16, dec.raw.len);
	const dist = try a.alloc(u16, dec.raw.len);
	@memset(len, 0);
	@memset(dist, 0);
	for (blocks, 0..) |b, i| {
		if (b.body != .huff) continue;
		var pos: u32 = dec.starts[i];
		for (b.body.huff.tokens) |t| switch (t) {
			.lit => pos += 1,
			.match => |m| {
				len[pos] = m.length;
				dist[pos] = m.distance;
				pos += m.length;
			},
		};
	}
	return .{ .len = len, .dist = dist };
}

const MAX: u32 = std.math.maxInt(u32);
const FORBID: u16 = std.math.maxInt(u16);
const LOOKAHEAD: u32 = common.MAX_MATCH_LENGTH + 1;

const Predecessor = packed struct(u32) {
	distance: u16 = 0,
	length: u9 = 0,
	_padding: u5 = 0,
	kind: enum(u2) { unset, previous_window, switch_model, token } = .unset,
};

fn ensure(ok: bool) void {
	if (!ok) @panic("boundary search invariant violated");
}

/// One price model: code lengths, the header bits of the cheapest block
/// carrying them, and derived match prices.
const Model = struct {
	ll: [common.MAX_SYMS]u8,
	dl: [common.fixed_dist_lengths.len]u8,
	lp: [common.MAX_MATCH_LENGTH + 1]u16, // length part of a match of n bytes; for 258 the cheaper legal spelling
	alt258: bool, // code 284 with five extra bits containing 31
	eob: u32,
	overhead: u32, // header bits (before the first token) of the cheapest block with these books
	source: u32, // index of that block in the stream
};

const Layer = struct { model: u32, s: u32, e: u32 };

fn buildModel(ll: [common.MAX_SYMS]u8, dl: [common.fixed_dist_lengths.len]u8, header_bits: u32, source: u32) Model {
	var lp: [common.MAX_MATCH_LENGTH + 1]u16 = @splat(FORBID);
	for (3..common.MAX_MATCH_LENGTH + 1) |n| {
		const lc = common.lenCodeTable[n];
		if (ll[lc.code] != 0) lp[n] = @as(u16, ll[lc.code]) + lc.extra;
	}
	var alt = false;
	const alt_code = common.lenCodeTable[common.MAX_MATCH_LENGTH - 1];
	if (ll[alt_code.code] != 0 and @as(u16, ll[alt_code.code]) + alt_code.extra < lp[common.MAX_MATCH_LENGTH]) {
		lp[common.MAX_MATCH_LENGTH] = @as(u16, ll[alt_code.code]) + alt_code.extra;
		alt = true;
	}
	return .{ .ll = ll, .dl = dl, .lp = lp, .alt258 = alt, .eob = ll[common.EOB], .overhead = header_bits, .source = source };
}

const Live = struct { layer: u32, lo: u32, hi: u32, best: []u32, pred: []Predecessor };
const Checkpoint = struct { layer: u32, lo: u32, vals: []u32 };

const WindowState = struct {
	arena: std.heap.ArenaAllocator,
	index: usize = std.math.maxInt(usize),
	a: u32 = 0,
	live: []Live = &.{},
	by_layer: std.AutoHashMapUnmanaged(u32, u32) = .empty,
	closed_pred: []u32 = &.{}, // closed rows from a through the window end

	fn init() WindowState {
		return .{ .arena = std.heap.ArenaAllocator.init(std.heap.page_allocator) };
	}
	fn deinit(self: *WindowState) void {
		self.arena.deinit();
	}
	fn find(self: *const WindowState, layer: u32) *Live {
		return &self.live[self.by_layer.get(layer).?];
	}
};

const Run = struct {
	raw: []const u8,
	edges: Edges,
	start: u32,
	end: u32,
	window: u32,
	models: []const Model,
	layers: []const Layer, // sorted by s
	checkpoints: [][]Checkpoint,
	allocator: std.mem.Allocator,

	fn windowCount(self: *const Run) usize {
		return (self.end - self.start + self.window - 1) / self.window;
	}

	/// Forward DP over window k from its checkpoint. Returns closed[b]; when
	/// `record`, stores the checkpoint of window k+1.
	fn forward(self: *Run, k: usize, st: *WindowState, record: bool) !u32 {
		_ = st.arena.reset(.retain_capacity);
		const wa = st.arena.allocator();
		st.by_layer = .empty;
		st.index = k;
		const a: u32 = self.start + @as(u32, @intCast(k)) * self.window;
		const b: u32 = @min(a + self.window, self.end);
		st.a = a;
		st.closed_pred = try wa.alloc(u32, b - a + 1);
		const raw_end: u32 = @min(b + LOOKAHEAD, self.end);

		var live: std.ArrayList(Live) = .empty;
		for (self.layers, 0..) |l, li| {
			if (l.s > raw_end or l.e < a) continue;
			const lo = @max(l.s, a);
			const hi = @min(l.e, raw_end);
			const n = hi - lo + 1;
			const best = try wa.alloc(u32, n);
			@memset(best, MAX);
			const pred = try wa.alloc(Predecessor, n);
			@memset(pred, .{});
			try st.by_layer.put(wa, @intCast(li), @intCast(live.items.len));
			try live.append(wa, .{ .layer = @intCast(li), .lo = lo, .hi = hi, .best = best, .pred = pred });
		}
		st.live = live.items;
		for (self.checkpoints[k]) |cp| {
			const lv = st.find(cp.layer);
			std.debug.assert(cp.lo >= lv.lo and cp.lo + cp.vals.len - 1 <= lv.hi);
			for (cp.vals, 0..) |v, i| {
				lv.best[cp.lo - lv.lo + i] = v;
				if (v != MAX) lv.pred[cp.lo - lv.lo + i] = .{ .kind = .previous_window };
			}
		}
		var active: std.ArrayList(u32) = .empty;
		var next_live: usize = 0;
		var closed_b: u32 = MAX;
		var p: u32 = a;
		while (p <= b) : (p += 1) {
			while (next_live < st.live.len and st.live[next_live].lo == p) : (next_live += 1) {
				try active.append(wa, @intCast(next_live));
			}
			// 1. The cheapest way to stand at p between blocks.
			var closed: u32 = if (p == self.start) 0 else MAX;
			var closed_by: u32 = MAX;
			for (active.items) |ai| {
				const lv = &st.live[ai];
				const v = lv.best[p - lv.lo];
				if (v == MAX) continue;
				const c = v + self.models[self.layers[lv.layer].model].eob;
				if (c < closed) {
					closed = c;
					closed_by = lv.layer;
				}
			}
			st.closed_pred[p - a] = closed_by;
			if (p == b) closed_b = closed;
			if (p < b) {
				const byte = self.raw[p];
				const edge_len = self.edges.len[p];
				const edge_dist = self.edges.dist[p];
				const edge_dc = common.distCodeTable[edge_dist];
				var write = active.items.len;
				var ai_index: usize = 0;
				while (ai_index < write) {
					const ai = active.items[ai_index];
					const lv = &st.live[ai];
					const layer = self.layers[lv.layer];
					if (layer.e == p) {
						write -= 1;
						active.items[ai_index] = active.items[write];
						continue;
					}
					ai_index += 1;
					const model = &self.models[layer.model];
					const row = p - lv.lo;
					// 2. Open a block of this model here.
					if (closed != MAX) {
						const cand = closed + model.overhead;
						if (cand < lv.best[row]) {
							lv.best[row] = cand;
							lv.pred[row] = .{ .kind = .switch_model };
						}
					}
					const c = lv.best[row];
					if (c == MAX) continue;
					// 3. Tokens under this model.
					const reach = lv.hi - p;
					if (model.ll[byte] != 0 and reach >= 1) {
						const cost = c + model.ll[byte];
						if (cost < lv.best[row + 1]) {
							lv.best[row + 1] = cost;
							lv.pred[row + 1] = .{ .kind = .token, .length = 1 };
						}
					}
					if (edge_len >= 3 and model.dl[edge_dc.code] != 0) {
						const base = c + model.dl[edge_dc.code] + edge_dc.extra;
						const limit: usize = @min(edge_len, reach);
						var n: usize = 3;
						while (n <= limit) : (n += 1) {
							const lp = model.lp[n];
							if (lp == FORBID) continue;
							const cost = base + lp;
							if (cost < lv.best[row + n]) {
								lv.best[row + n] = cost;
								lv.pred[row + n] = .{ .kind = .token, .length = @intCast(n), .distance = edge_dist };
							}
						}
					}
				}
				active.items.len = write;
			}
		}
		if (record and b < self.end) {
			var cps: std.ArrayList(Checkpoint) = .empty;
			const ca = self.allocator;
			for (st.live) |lv| {
				if (lv.hi < b or lv.lo > b) continue; // rows beyond b are reachable only through rows before it
				const vals = lv.best[b - lv.lo ..];
				if (std.mem.indexOfNone(u32, vals, &.{MAX}) != null)
					try cps.append(ca, .{ .layer = lv.layer, .lo = b, .vals = try ca.dupe(u32, vals) });
			}
			self.checkpoints[k + 1] = cps.items;
		}
		return closed_b;
	}
};

fn getWindow(run: *Run, slots: []WindowState, k: usize) !*WindowState {
	for (slots) |*cand| if (cand.index == k) return cand;
	var victim: *WindowState = &slots[0];
	for (slots) |*cand| {
		if (cand.index == std.math.maxInt(usize)) {
			victim = cand;
			break;
		}
		if (cand.index > victim.index) victim = cand;
	}
	_ = try run.forward(k, victim, false);
	return victim;
}

/// Search one run of Huffman blocks `blocks[first..past]`. Returns the
/// blocks in order with their DP cost, or null when the search is not
/// strictly cheaper than the run's own bits.
fn searchRun(a: std.mem.Allocator, blocks: []const Block, costs: []const u32, overheads: []const u32, dec: Decoded, edges: Edges, first: usize, past: usize, options: Options) deflasm.ParseError!?Result {
	var scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer scratch.deinit();
	const sa = scratch.allocator();
	const start = dec.starts[first];
	const end = dec.starts[past];
	if (end == start) return null;
	var before: u64 = 0;
	var models: std.ArrayList(Model) = .empty;
	var layers: std.ArrayList(Layer) = .empty;
	var keys: std.StringHashMapUnmanaged(u32) = .empty;
	for (first..past) |i| {
		const h = blocks[i].body.huff;
		before += costs[i];
		var ll: [common.MAX_SYMS]u8 = @splat(0);
		var dl: [common.fixed_dist_lengths.len]u8 = @splat(0);
		if (h.is_fixed) {
			ll = common.fixed_ll_lengths;
			dl = common.fixed_dist_lengths;
		} else {
			@memcpy(ll[0..h.ll_lengths.len], h.ll_lengths);
			@memcpy(dl[0..h.dist_lengths.len], h.dist_lengths);
		}
		// The DP pays the EOB separately when it closes a block.
		const header_bits = overheads[i] - ll[common.EOB];
		const key = try std.mem.concat(sa, u8, &.{ &ll, &dl });
		const entry = try keys.getOrPut(sa, key);
		if (!entry.found_existing) {
			entry.value_ptr.* = @intCast(models.items.len);
			try models.append(sa, buildModel(ll, dl, header_bits, @intCast(i)));
		} else if (header_bits < models.items[entry.value_ptr.*].overhead) {
			models.items[entry.value_ptr.*].overhead = header_bits;
			models.items[entry.value_ptr.*].source = @intCast(i);
		}
		try layers.append(sa, .{
			.model = entry.value_ptr.*,
			.s = @max(start, dec.starts[i] -| options.slack),
			.e = @min(end, dec.starts[i + 1] +| options.slack),
		});
	}
	// Merge layers of one model whose spans touch or overlap, then order by start.
	std.mem.sort(Layer, layers.items, {}, struct {
		fn lt(_: void, x: Layer, y: Layer) bool {
			return if (x.model != y.model) x.model < y.model else x.s < y.s;
		}
	}.lt);
	var count: usize = 0;
	for (layers.items, 0..) |l, i| {
		std.debug.assert(count <= i);
		if (count > 0) {
			const last = &layers.items[count - 1];
			if (last.model == l.model and l.s <= last.e) {
				last.e = @max(last.e, l.e);
				continue;
			}
		}
		layers.items[count] = l;
		count += 1;
	}
	layers.items.len = count;
	std.mem.sort(Layer, layers.items, {}, struct {
		fn lt(_: void, x: Layer, y: Layer) bool {
			return if (x.s != y.s) x.s < y.s else x.e < y.e;
		}
	}.lt);

	var run: Run = .{
		.raw = dec.raw,
		.edges = edges,
		.start = start,
		.end = end,
		.window = @max(options.window, 2 * LOOKAHEAD),
		.models = models.items,
		.layers = layers.items,
		.checkpoints = undefined,
		.allocator = sa,
	};
	const nwin = run.windowCount();
	run.checkpoints = try sa.alloc([]Checkpoint, nwin);
	@memset(run.checkpoints, &.{});
	var states = [_]WindowState{ WindowState.init(), WindowState.init() };
	defer for (&states) |*state| state.deinit();
	var after: u32 = MAX;
	for (0..nwin) |k| after = try run.forward(k, &states[0], true);
	if (after == MAX or after >= before) return null;

	// Reuse the last forward window; rerun earlier windows during backtracking.
	std.debug.assert(states[0].index == nwin - 1);
	var token_count: usize = 0;
	for (blocks[first..past]) |b| token_count += b.body.huff.tokens.len;
	var rev_tokens = try std.ArrayList(Token).initCapacity(std.heap.page_allocator, token_count);
	defer rev_tokens.deinit(std.heap.page_allocator);
	const Rev = struct { model: u32, from: u32, to: u32, count: usize };
	var rev: std.ArrayList(Rev) = .empty;
	var q: u32 = end;
	var seg_end = end;
	var seg_count: usize = 0;
	var layer: u32 = MAX;
	{
		const st_last = try getWindow(&run, &states, nwin - 1);
		layer = st_last.closed_pred[end - st_last.a];
	}
	ensure(layer != MAX);
	while (true) {
		const k: usize = @min((q - start) / run.window, nwin - 1);
		var st_k = try getWindow(&run, &states, k);
		var lv = st_k.find(layer);
		ensure(q >= lv.lo and q <= lv.hi);
		var pr = lv.pred[q - lv.lo];
		if (pr.kind == .previous_window) {
			ensure(k > 0 and q < st_k.a + LOOKAHEAD);
			st_k = try getWindow(&run, &states, k - 1);
			lv = st_k.find(layer);
			ensure(q >= lv.lo and q <= lv.hi);
			pr = lv.pred[q - lv.lo];
		}
		switch (pr.kind) {
			.token => {
				const n: u16 = pr.length;
				const d = pr.distance;
				const model = &models.items[run.layers[layer].model];
				try rev_tokens.append(std.heap.page_allocator, if (n == 1 and d == 0) .{ .lit = dec.raw[q - 1] } else .{ .match = .{
					.length = n,
					.distance = d,
					.original_alt258 = n == common.MAX_MATCH_LENGTH and model.alt258,
				} });
				seg_count += 1;
				q -= n;
			},
			.switch_model => {
				try rev.append(sa, .{ .model = run.layers[layer].model, .from = q, .to = seg_end, .count = seg_count });
				if (q == start) break;
				const st_q = try getWindow(&run, &states, @min((q - start) / run.window, nwin - 1));
				layer = st_q.closed_pred[q - st_q.a];
				ensure(layer != MAX);
				seg_end = q;
				seg_count = 0;
			},
			else => {
				ensure(false);
				unreachable;
			},
		}
	}
	// Materialize in forward order. A segment that is exactly one input
	// block, under that block's own header, with the same tokens, is reused.
	std.mem.reverse(Token, rev_tokens.items);
	const out = try a.alloc(Block, rev.items.len);
	const fresh = try a.alloc(bool, rev.items.len);
	var consumed: usize = 0;
	var block_at = first;
	for (0..rev.items.len) |n| {
		const seg = rev.items[rev.items.len - 1 - n];
		const model = &models.items[seg.model];
		const tokens = rev_tokens.items[consumed .. consumed + seg.count];
		consumed += seg.count;
		while (block_at < past and dec.starts[block_at] < seg.from) block_at += 1;
		const whole = block_at < past and dec.starts[block_at] == seg.from and dec.starts[block_at + 1] == seg.to and model.source == block_at and
			tokensEqual(blocks[block_at].body.huff.tokens, tokens);
		out[n] = blocks[model.source];
		fresh[n] = !whole;
		if (!whole) {
			out[n].body.huff.tokens = try a.dupe(Token, tokens);
			// Retain the selected length-258 spelling, but discard old final padding.
			out[n].body.huff.encoding = .{ .hclen = if (out[n].body.huff.encoding) |e| e.hclen else 0 };
		}
	}
	ensure(consumed == rev_tokens.items.len);
	return .{ .blocks = out, .fresh = fresh, .before = before, .after = after };
}

fn tokensEqual(x: []const Token, y: []const Token) bool {
	if (x.len != y.len) return false;
	for (x, y) |p, q| {
		const same = switch (p) {
			.lit => |c| q == .lit and q.lit == c,
			.match => |m| q == .match and q.match.length == m.length and q.match.distance == m.distance and q.match.original_alt258 == m.original_alt258,
		};
		if (!same) return false;
	}
	return true;
}

/// Search every run of Huffman blocks in `blocks`, whose decoded form is
/// `dec` and whose candidate matches are `edges`; `costs[i]` is block i's
/// exact bit cost and `overheads[i]` its header-plus-EOB cost. Returns the
/// rewritten stream, or null when no run improved. Stored blocks and
/// unimproved runs are copied unchanged.
pub fn search(a: std.mem.Allocator, blocks: []const Block, costs: []const u32, overheads: []const u32, dec: Decoded, edges: Edges, options: Options) deflasm.ParseError!?Result {
	var out: std.ArrayList(Block) = .empty;
	var fresh: std.ArrayList(bool) = .empty;
	var before: u64 = 0;
	var after: u64 = 0;
	var improved = false;
	var i: usize = 0;
	while (i < blocks.len) {
		if (blocks[i].body == .stored) {
			try out.append(a, blocks[i]);
			try fresh.append(a, false);
			i += 1;
			continue;
		}
		var j = i;
		while (j < blocks.len and blocks[j].body == .huff) j += 1;
		if (try searchRun(a, blocks, costs, overheads, dec, edges, i, j, options)) |found| {
			improved = true;
			before += found.before;
			after += found.after;
			try out.appendSlice(a, found.blocks);
			try fresh.appendSlice(a, found.fresh);
		} else {
			try out.appendSlice(a, blocks[i..j]);
			try fresh.appendNTimes(a, false, j - i);
		}
		i = j;
	}
	if (!improved) return null;
	for (out.items) |*b| b.is_last = false;
	out.items[out.items.len - 1].is_last = true;
	return .{ .blocks = out.items, .fresh = fresh.items, .before = before, .after = after };
}

fn bitsOf(a: std.mem.Allocator, block: Block) !u32 {
	var buf: std.ArrayList(u8) = .empty;
	defer buf.deinit(a);
	var w = common.BitWriter.init(&buf, a);
	try deflasm.assembleBlock(&w, block);
	return @intCast(w.totalBits());
}

test "single-model search still considers literals instead of a match" {
	const deflopt = @import("deflopt.zig");
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	var tokens: [131]Token = undefined;
	for (tokens[0..100]) |*t| t.* = .{ .lit = 'a' };
	for (tokens[100..130]) |*t| t.* = .{ .match = .{ .length = 4, .distance = 1 } };
	tokens[130] = .{ .match = .{ .length = 3, .distance = 1 } };
	const block = try deflopt.makeDynamicBlock(a, &tokens, true, false, false);
	const h = block.body.huff;
	try std.testing.expectEqual(@as(u8, 4), h.ll_lengths[common.FIRST_LENGTH_SYMBOL] + h.dist_lengths[0]);
	try std.testing.expectEqual(@as(u8, 3), 3 * h.ll_lengths['a']);
	const blocks = [_]Block{block};
	const costs = [_]u32{try bitsOf(a, block)};
	var header = block;
	header.body.huff.tokens = &.{};
	const overheads = [_]u32{try bitsOf(a, header)};
	const dec = try decode(a, &blocks);
	const edges = try edgesOf(a, &blocks, dec);
	const result = try search(a, &blocks, &costs, &overheads, dec, edges, .{});
	try std.testing.expect(result != null);
	try std.testing.expectEqual(costs[0] - 1, result.?.after);
	try std.testing.expectEqual(result.?.after, try bitsOf(a, result.?.blocks[0]));
	try std.testing.expectEqualSlices(u8, dec.raw, (try decode(a, result.?.blocks)).raw);
}

test "boundary search moves a misplaced split to the cheaper model and prices it exactly" {
	const deflopt = @import("deflopt.zig");
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	// Block A: 100 'a' then 50 'b'; block B: 1000 'b'. The split belongs at 100:
	// under A's books a 'b' costs two bits, under B's one.
	var ta: [150]Token = undefined;
	for (0..100) |i| ta[i] = .{ .lit = 'a' };
	for (100..150) |i| ta[i] = .{ .lit = 'b' };
	var tb: [1000]Token = undefined;
	for (&tb) |*t| t.* = .{ .lit = 'b' };
	var tc: [10000]Token = undefined;
	for (&tc) |*t| t.* = .{ .lit = 'c' };
	const blocks = [_]Block{
		try deflopt.makeDynamicBlock(a, &ta, false, false, false),
		try deflopt.makeDynamicBlock(a, &tb, false, false, false),
		try deflopt.makeDynamicBlock(a, &tc, true, false, false),
	};
	var costs: [blocks.len]u32 = undefined;
	var overheads: [blocks.len]u32 = undefined;
	for (blocks, 0..) |b, i| {
		costs[i] = try bitsOf(a, b);
		var header = b;
		header.body.huff.tokens = &.{};
		overheads[i] = try bitsOf(a, header);
	}
	const dec = try decode(a, &blocks);
	try std.testing.expectEqual(@as(u32, 1150), dec.starts[2]);
	const edges = try edgesOf(a, &blocks, dec);
	for ([_]u32{ 4096, 600 }) |window| {
		// Enough output storage for the changed tokens and framing, but not
		// a discarded copy of the much larger, unchanged third block.
		var output_storage: [(ta.len + tb.len) * @sizeOf(Token) + 4096]u8 = undefined;
		var output_allocator = std.heap.FixedBufferAllocator.init(&output_storage);
		const res = (try search(output_allocator.allocator(), &blocks, &costs, &overheads, dec, edges, .{ .slack = 64, .window = window })).?;
		try std.testing.expectEqual(@as(usize, 3), res.blocks.len);
		try std.testing.expectEqual(@as(usize, 100), res.blocks[0].body.huff.tokens.len);
		try std.testing.expectEqual(res.before - 50, res.after);
		try std.testing.expect(res.fresh[0] and res.fresh[1]);
		try std.testing.expect(!res.fresh[2]);
		try std.testing.expectEqual(blocks[2].body.huff.tokens.ptr, res.blocks[2].body.huff.tokens.ptr);
		// The assembler charges exactly what the search paid, and the content survives.
		var total: u64 = 0;
		for (res.blocks) |b| total += try bitsOf(a, b);
		try std.testing.expectEqual(res.after, total);
		const redecoded = try decode(a, res.blocks);
		try std.testing.expectEqualSlices(u8, dec.raw, redecoded.raw);
	}
	// Without slack the boundary cannot move; a tie keeps the input.
	try std.testing.expect((try search(a, &blocks, &costs, &overheads, dec, edges, .{ .slack = 0, .window = 4096 })) == null);
}
