//! Resumable queries over a shared match graph. Prices rank answers; they do
//! not remove paths. A query owns its price view, never the underlying graph.
const std = @import("std");
const ir = @import("deflir.zig");
const reparse = @import("deflreparse.zig");
const deflasm = @import("deflasm.zig");
const common = @import("deflcommon.zig");
const A = std.mem.Allocator;
const Token = deflasm.Token;
fn ensure(ok: bool) void { if (!ok) @panic("deferred search invariant violated"); }

pub const MAX_QUERY_LENGTH = 4096;
pub const DEFAULT_HEAP_ENTRIES = 262144;

pub const Stats = struct {
	queries: usize = 0, shared_queries: usize = 0,
	initialized_positions: usize = 0, packed_answers: usize = 0,
	heap_entries: usize = 0, root_answers: usize = 0,
	max_heap_entries: usize = DEFAULT_HEAP_ENTRIES,
	limited: bool = false,
};

pub const Path = struct {
	edge: reparse.Edge,
	tail: ?*const Path,
	cost: f64,
	pub fn append(self: *const Path, a: A, raw: []const u8, out: *std.ArrayList(Token)) !void {
		var path = self;
		var pos: usize = 0;
		while (path.tail) |tail| {
			const e = path.edge;
			ensure(e.length > 0 and pos + e.length <= raw.len);
			try out.append(a, if (e.distance == 0) .{ .lit = raw[pos] } else .{ .match = .{ .length = e.length, .distance = e.distance } });
			pos += e.length;
			path = tail;
		}
		ensure(pos == raw.len);
	}
};
const end_path: Path = .{ .edge = .{ .length = 0, .distance = 0 }, .tail = null, .cost = 0 };

/// Every edge in the supplied graph denotes all lengths 3..edge.length.
/// Literals are implicit. Restrictions only filter the requested alphabet;
/// no dominance or fixed-price tie rule removes a remaining production.
pub const Query = struct {
	const Choice = struct { edge: reparse.Edge, rank: usize = 0, cost: f64 };
	fn order(_: void, x: Choice, y: Choice) std.math.Order {
		if (x.cost != y.cost) return std.math.order(x.cost, y.cost);
		if (x.edge.length != y.edge.length) return std.math.order(x.edge.length, y.edge.length);
		if (x.edge.distance != y.edge.distance) return std.math.order(x.edge.distance, y.edge.distance);
		return std.math.order(x.rank, y.rank);
	}
	const Item = struct {
		initialized: bool = false,
		answers: std.ArrayList(*const Path) = .empty,
		heap: std.PriorityQueue(Choice, void, order) = .initContext({}),
		pending: ?Choice = null,
	};
	a: A, edges: reparse.Edges,
	start: usize, length: usize, mask: ir.SymbolMask, prices: reparse.Prices,
	costs: []f64, items: []Item, stats: *Stats,

	pub fn init(a: A, edges: reparse.Edges, start: usize, length: usize, mask: ir.SymbolMask, prices: reparse.Prices, stats: *Stats) !Query {
		ensure(length > 0 and length <= MAX_QUERY_LENGTH and start + length <= edges.program.raw().len);
		for (prices.ll) |p| ensure(std.math.isFinite(p));
		for (prices.dist) |p| ensure(std.math.isFinite(p));
		const costs = try a.alloc(f64, length + 1);
		const items = try a.alloc(Item, length);
		@memset(items, .{});
		var q: Query = .{ .a = a, .edges = edges, .start = start,
			.length = length, .mask = mask, .prices = prices, .costs = costs,
			.items = items, .stats = stats };
		costs[length] = 0;
		var pos = length;
		while (pos > 0) {
			pos -= 1;
			costs[pos] = std.math.inf(f64);
			var choices = q.alternatives(pos);
			while (choices.next()) |e| costs[pos] = @min(costs[pos], q.tokenCost(pos, e) + costs[pos + e.length]);
			ensure(std.math.isFinite(costs[pos]));
		}
		stats.queries += 1;
		return q;
	}
	fn alternatives(q: *const Query, pos: usize) ir.Alternatives {
		return q.edges.alternatives(.{ .start = q.start + pos, .length = q.length - pos }, q.mask);
	}
	fn tokenCost(q: *const Query, pos: usize, e: reparse.Edge) f64 {
		if (e.distance == 0) return q.prices.ll[q.edges.program.raw()[q.start + pos]];
		const lc = common.lenCodeTable[e.length];
		const dc = common.distCodeTable[e.distance];
		return q.prices.ll[lc.code] + @as(f64, @floatFromInt(lc.extra)) + q.prices.dist[dc.code] + @as(f64, @floatFromInt(dc.extra));
	}
	fn push(q: *Query, item: *Item, choice: Choice) !void {
		if (q.stats.heap_entries >= q.stats.max_heap_entries) {
			q.stats.limited = true;
			return error.WorkLimit;
		}
		try item.heap.push(q.a, choice);
		q.stats.heap_entries += 1;
	}
	fn initialize(q: *Query, pos: usize) !void {
		const item = &q.items[pos];
		if (item.initialized) return;
		item.initialized = true;
		q.stats.initialized_positions += 1;
		var choices = q.alternatives(pos);
		while (choices.next()) |e| try q.push(item, .{ .edge = e, .cost = q.tokenCost(pos, e) + q.costs[pos + e.length] });
	}
	/// Only winning branches ask their child for an actual packed answer.
	/// Neighboring child ranks remain suspended until the next request.
	pub fn get(q: *Query, pos: usize, rank: usize) error{ OutOfMemory, WorkLimit }!?*const Path {
		ensure(pos <= q.length);
		if (q.stats.limited) return error.WorkLimit;
		if (pos == q.length) return if (rank == 0) &end_path else null;
		try q.initialize(pos);
		const item = &q.items[pos];
		while (item.answers.items.len <= rank) {
			if (item.pending) |old| {
				item.pending = null;
				if (try q.get(pos + old.edge.length, old.rank + 1)) |tail| {
					try q.push(item, .{ .edge = old.edge, .rank = old.rank + 1, .cost = q.tokenCost(pos, old.edge) + tail.cost });
				}
			}
			const next = item.heap.pop() orelse return null;
			const tail = (try q.get(pos + next.edge.length, next.rank)).?;
			ensure(next.cost == q.tokenCost(pos, next.edge) + tail.cost);
			const answer = try q.a.create(Path);
			answer.* = .{ .edge = next.edge, .tail = tail, .cost = next.cost };
			if (item.answers.items.len > 0) ensure(item.answers.items[item.answers.items.len - 1].cost <= answer.cost);
			try item.answers.append(q.a, answer);
			item.pending = next;
			q.stats.packed_answers += 1;
		}
		return item.answers.items[rank];
	}
};

/// Query reuse is scoped to one decoded block and its history. Only the
/// additive reader's complete dependencies permit sharing priced answers.
pub const Graph = struct {
	a: A, edges: reparse.Edges, stats: *Stats,
	queries: std.ArrayList(*Query) = .empty,
	pub fn query(g: *Graph, start: usize, length: usize, mask: ir.SymbolMask, prices: reparse.Prices) !*Query {
		for (g.queries.items) |q| {
			if (q.start == start and q.length == length and q.mask == mask and
				std.mem.eql(f64, &q.prices.ll, &prices.ll) and std.mem.eql(f64, &q.prices.dist, &prices.dist)) {
				g.stats.shared_queries += 1;
				return q;
			}
		}
		const q = try g.a.create(Query);
		q.* = try Query.init(g.a, g.edges, start, length, mask, prices, g.stats);
		try g.queries.append(g.a, q);
		return q;
	}
};

/// Joint replacement requests pack a Cartesian product of local answer
/// streams. The four-span cap is a caller's neighborhood policy, not a
/// limit on DEFLATE or a claim that other supports are irrelevant.
pub const Request = struct {
	pub const Span = struct { token: usize, after_token: usize, start: usize, length: usize };
	const Combination = struct { ranks: [4]usize = @splat(0), cost: f64 };
	fn order(_: void, x: Combination, y: Combination) std.math.Order {
		if (x.cost != y.cost) return std.math.order(x.cost, y.cost);
		return std.mem.order(usize, &x.ranks, &y.ranks);
	}
	graph: *Graph, tokens: []const Token, spans: []const Span,
	queries: [4]*Query = undefined, mask: ir.SymbolMask, prices: reparse.Prices,
	heap: std.PriorityQueue(Combination, void, order) = .initContext({}),
	seen: std.AutoHashMapUnmanaged([4]usize, void) = .empty,
	initialized: bool = false, pending: ?Combination = null,
	pub const Answer = struct { tokens: []Token, cost: f64 };

	pub fn supports(a: A, tokens: []const Token, mask: ir.SymbolMask) ![]const Span {
		var spans: std.ArrayList(Span) = .empty;
		var pos: usize = 0;
		for (tokens, 0..) |t, index| {
			const n: usize = switch (t) { .lit => 1, .match => |m| m.length };
			if (t == .match and mask & ir.matchSymbols(t.match.length, t.match.distance) != 0) {
				try spans.append(a, .{ .token = index, .after_token = index + 1, .start = pos, .length = n });
			}
			pos += n;
		}
		// The ordinary request leaves the whole parse unresolved. It uses
		// exactly the same graph/answer machinery as a local obligation.
		if (mask == 0) try spans.append(a, .{ .token = 0, .after_token = tokens.len, .start = 0, .length = pos });
		return spans.items;
	}
	fn push(r: *Request, ranks: [4]usize) !void {
		if (r.seen.contains(ranks)) return;
		try r.seen.put(r.graph.a, ranks, {});
		var cost: f64 = 0;
		for (0..r.spans.len) |i| {
			const answer = try r.queries[i].get(0, ranks[i]) orelse return;
			cost += answer.cost;
		}
		try r.heap.push(r.graph.a, .{ .ranks = ranks, .cost = cost });
	}
	pub fn next(r: *Request, a: A) !?Answer {
		ensure(r.spans.len > 0 and r.spans.len <= r.queries.len);
		if (!r.initialized) {
			r.initialized = true;
			for (r.spans, 0..) |span, i| r.queries[i] = try r.graph.query(span.start, span.length, r.mask, r.prices);
			try r.push(@splat(0));
		}
		if (r.pending) |old| {
			r.pending = null;
			for (0..r.spans.len) |i| {
				var ranks = old.ranks;
				ranks[i] += 1;
				try r.push(ranks);
			}
		}
		const combination = r.heap.pop() orelse return null;
		var out: std.ArrayList(Token) = .empty;
		var cursor: usize = 0;
		for (r.spans, 0..) |span, i| {
			ensure(cursor <= span.token and span.token < r.tokens.len);
			try out.appendSlice(a, r.tokens[cursor..span.token]);
			const path = (try r.queries[i].get(0, combination.ranks[i])).?;
			try path.append(a, r.graph.edges.program.raw()[span.start..][0..span.length], &out);
			ensure(span.after_token > span.token and span.after_token <= r.tokens.len);
			cursor = span.after_token;
		}
		try out.appendSlice(a, r.tokens[cursor..]);
		r.pending = combination;
		r.graph.stats.root_answers += 1;
		return .{ .tokens = out.items, .cost = combination.cost };
	}
};

const Enumerated = struct { tokens: []Token, cost: f64 };
fn enumerateForTest(a: A, q: *const Query, pos: usize, tokens: *std.ArrayList(Token), out: *std.ArrayList(Enumerated), cost: f64) error{OutOfMemory}!void {
	if (pos == q.length) {
		try out.append(a, .{ .tokens = try a.dupe(Token, tokens.items), .cost = cost });
		return;
	}
	try tokens.append(a, .{ .lit = q.edges.program.raw()[q.start + pos] });
	try enumerateForTest(a, q, pos + 1, tokens, out, cost + q.prices.ll[q.edges.program.raw()[q.start + pos]]);
	_ = tokens.pop();
	for (q.edges.at(q.start + pos)) |e| {
		if (q.mask & (@as(u64, 1) << @intCast(common.distCodeTable[e.distance].code)) != 0) continue;
		const limit = @min(e.length, q.length - pos);
		if (limit < 3) continue;
		for (3..limit + 1) |n| {
			if (q.mask & (@as(u64, 1) << @intCast(ir.LENGTH_MASK_SHIFT + common.lenCodeTable[n].code - common.FIRST_LENGTH_SYMBOL)) != 0) continue;
			try tokens.append(a, .{ .match = .{ .length = @intCast(n), .distance = e.distance } });
			try enumerateForTest(a, q, pos + n, tokens, out, cost + q.tokenCost(pos, .{ .length = @intCast(n), .distance = e.distance }));
			_ = tokens.pop();
		}
	}
}
fn tokensEqualForTest(x: []const Token, y: []const Token) bool {
	if (x.len != y.len) return false;
	for (x, y) |t, u| if (!std.meta.eql(t, u)) return false;
	return true;
}

test "deferred queries retain ties and higher priced paths, exhaustively" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	const raw = "aaaaaaa";
	const edges = try reparse.candidatesWithHistory(a, raw, "aaaaa");
	var p: reparse.Prices = .{ .ll = @splat(4), .dist = @splat(2) };
	p.ll['a'] = 3;
	for ([_]ir.SymbolMask{ 0, 1, 15, 1 << 33, (1 << 32) | (1 << 35), 3 | (1 << 34) }) |mask| {
		var stats: Stats = .{};
		var q = try Query.init(a, edges, 0, raw.len, mask, p, &stats);
		var all: std.ArrayList(Enumerated) = .empty;
		var buffer: std.ArrayList(Token) = .empty;
		try enumerateForTest(a, &q, 0, &buffer, &all, 0);
		const matched = try a.alloc(bool, all.items.len);
		@memset(matched, false);
		var last: f64 = -std.math.inf(f64);
		for (0..all.items.len) |rank| {
			const answer = (try q.get(0, rank)).?;
			try std.testing.expect(answer.cost >= last);
			last = answer.cost;
			buffer.clearRetainingCapacity();
			try answer.append(a, raw, &buffer);
			var found = false;
			for (all.items, 0..) |reference, i| {
				if (!matched[i] and tokensEqualForTest(reference.tokens, buffer.items)) {
					try std.testing.expectEqual(reference.cost, answer.cost);
					matched[i] = true;
					found = true;
					break;
				}
			}
			try std.testing.expect(found);
		}
		try std.testing.expectEqual(@as(?*const Path, null), try q.get(0, all.items.len));
		for (matched) |yes| try std.testing.expect(yes);
		try std.testing.expect(all.items.len > 1);
		try std.testing.expect(last > q.costs[0]);
	}
}

test "deferred repricing shares only equivalent views and preserves old cursors" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	const raw = "abc";
	const edges = try reparse.candidatesWithHistory(a, raw, "abcabc");
	var stats: Stats = .{};
	var g: Graph = .{ .a = a, .edges = edges, .stats = &stats };
	var p: reparse.Prices = .{ .ll = @splat(8), .dist = @splat(3) };
	p.dist[common.distCodeTable[6].code] = 2; // d3 and d6 tie after extra bits.
	const original = try g.query(0, 3, 0, p);
	const first = (try original.get(0, 0)).?;
	try std.testing.expectEqual(@as(u16, 3), first.edge.distance);
	try std.testing.expectEqual(@as(usize, 1), stats.packed_answers);
	const same = try g.query(0, 3, 0, p);
	try std.testing.expect(same == original);
	p.dist[common.distCodeTable[6].code] = 1;
	const repriced = try g.query(0, 3, 0, p);
	try std.testing.expect(repriced != original);
	try std.testing.expectEqual(@as(u16, 6), (try repriced.get(0, 0)).?.edge.distance);
	const second = (try original.get(0, 1)).?;
	try std.testing.expectEqual(@as(u16, 6), second.edge.distance);
	try std.testing.expectEqual(first.cost, second.cost);
	try std.testing.expect((try original.get(0, 2)).?.cost > second.cost);
	const no_three = try g.query(0, 3, @as(ir.SymbolMask, 1) << 32, p);
	try std.testing.expect(no_three != repriced);
	try std.testing.expectEqual(@as(u16, 0), (try no_three.get(0, 0)).?.edge.distance);
	try std.testing.expectEqual(@as(usize, 1), stats.shared_queries);
}

test "length exclusions shorten matches while preserving untouched spans" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	const edges = try reparse.candidatesWithHistory(a, "aaaaaaaaaaaa", "aa");
	var stats: Stats = .{};
	var g: Graph = .{ .a = a, .edges = edges, .stats = &stats };
	const tokens = [_]Token{ .{ .match = .{ .length = 5, .distance = 1 } },
		.{ .lit = 'a' }, .{ .match = .{ .length = 6, .distance = 1 } } };
	// Exclude length five and distance two, exercising both alphabets in
	// one request. The six-byte match is outside the replacement footprint.
	const mask: ir.SymbolMask = (1 << 34) | 2;
	const spans = try Request.supports(a, &tokens, mask);
	try std.testing.expectEqual(@as(usize, 1), spans.len);
	var r: Request = .{ .graph = &g, .tokens = &tokens, .spans = spans, .mask = mask,
		.prices = .{ .ll = @splat(8), .dist = @splat(1) } };
	const answer = (try r.next(a)).?;
	try std.testing.expect(std.meta.eql(tokens[2], answer.tokens[answer.tokens.len - 1]));
	var pos: usize = 0;
	for (answer.tokens) |t| {
		try std.testing.expect(edges.program.accepts(pos, t));
		if (t == .match) try std.testing.expect(mask & ir.matchSymbols(t.match.length, t.match.distance) == 0);
		pos += switch (t) { .lit => 1, .match => |m| m.length };
	}
	try std.testing.expectEqual(@as(usize, 12), pos);
}

test "deferred joint request enumerates every combination without greedy commitment" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	const raw = "abcabc";
	const edges = try reparse.candidatesWithHistory(a, raw, "abcabcabc");
	var stats: Stats = .{};
	var g: Graph = .{ .a = a, .edges = edges, .stats = &stats };
	const tokens = [_]Token{ .{ .match = .{ .length = 3, .distance = 3 } }, .{ .match = .{ .length = 3, .distance = 6 } } };
	const mask = (@as(u32, 1) << @intCast(common.distCodeTable[3].code)) | (@as(u32, 1) << @intCast(common.distCodeTable[6].code));
	const spans = try Request.supports(a, &tokens, mask);
	var r: Request = .{ .graph = &g, .tokens = &tokens, .spans = spans, .mask = mask, .prices = .{ .ll = @splat(5), .dist = @splat(1) } };
	var expected: usize = 1;
	for (spans) |span| {
		const q = try g.query(span.start, span.length, mask, r.prices);
		var all: std.ArrayList(Enumerated) = .empty;
		var buffer: std.ArrayList(Token) = .empty;
		try enumerateForTest(a, q, 0, &buffer, &all, 0);
		expected *= all.items.len;
	}
	var count: usize = 0;
	var previous: f64 = -std.math.inf(f64);
	while (try r.next(a)) |answer| {
		try std.testing.expect(answer.cost >= previous);
		previous = answer.cost;
		for (answer.tokens) |t| if (t == .match) {
			try std.testing.expect(mask & ir.matchSymbols(t.match.length, t.match.distance) == 0);
		};
		count += 1;
		try std.testing.expect(count <= expected);
	}
	try std.testing.expectEqual(expected, count);
	try std.testing.expect(count >= 4);
}

test "deferred graph work limit remains explicit after a partial initialization" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	const edges = try reparse.candidatesWithHistory(a, "aaaa", "aaaa");
	var stats: Stats = .{ .max_heap_entries = 1 };
	var q = try Query.init(a, edges, 0, 4, 0, .{ .ll = @splat(4), .dist = @splat(2) }, &stats);
	try std.testing.expectError(error.WorkLimit, q.get(0, 0));
	try std.testing.expectError(error.WorkLimit, q.get(0, 0));
	try std.testing.expectEqual(@as(usize, 0), stats.packed_answers);
}

test "deferred whole-block request can change the original token boundaries" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	const raw = "abcabc";
	const edges = try reparse.candidatesWithHistory(a, raw, "abc");
	var stats: Stats = .{};
	var g: Graph = .{ .a = a, .edges = edges, .stats = &stats };
	const tokens = [_]Token{ .{ .match = .{ .length = 3, .distance = 3 } }, .{ .match = .{ .length = 3, .distance = 3 } } };
	var r: Request = .{ .graph = &g, .tokens = &tokens, .spans = try Request.supports(a, &tokens, 0),
		.mask = 0, .prices = .{ .ll = @splat(8), .dist = @splat(1) } };
	const first = (try r.next(a)).?;
	try std.testing.expectEqual(@as(usize, 1), first.tokens.len);
	try std.testing.expectEqualDeep(Token{ .match = .{ .length = 6, .distance = 3 } }, first.tokens[0]);
	try std.testing.expectEqual(@as(usize, 1), stats.packed_answers);
}
