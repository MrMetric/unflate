//! Completion-driven controller for the production reparser. Production uses
//! a bounded search over alternative parses that eliminate rare distance codes.
const std = @import("std");
const ir = @import("deflir.zig");
const reparse = @import("deflreparse.zig");
const deferred = @import("deflsearch.zig");
const deflasm = @import("deflasm.zig");
const common = @import("deflcommon.zig");
const A = std.mem.Allocator;
const Block = deflasm.Block;
fn ensure(ok: bool) void { if (!ok) @panic("feedback controller invariant violated"); }

const Encoding = struct { bytes: []const u8, bits: i64 };
fn encode(a: A, block: Block) !Encoding {
	var out: std.ArrayList(u8) = .empty;
	var w = common.BitWriter.init(&out, a);
	try deflasm.assembleBlock(&w, block);
	const bits: i64 = @intCast(w.totalBits());
	if (block.is_last) try deflasm.finishDeflate(&w, block);
	try w.alignByte();
	return .{ .bytes = out.items, .bits = bits };
}
fn decode(a: A, bytes: []const u8) error{OutOfMemory}!Block {
	var r: common.BitReader = .{ .data = bytes };
	return deflasm.parseBlock(&r, a) catch |err| switch (err) {
		error.Malformed => @panic("completed feedback encoding failed to parse"),
		error.OutOfMemory => return error.OutOfMemory,
	};
}

/// Target rare distance codes individually, in adjacent pairs, and in a tail.
/// Each request searches for an equivalent parse without the targeted codes.
fn goals(a: A, h: deflasm.Huff) ![]ir.SymbolMask {
	var distances: [30]u32 = @splat(0);
	for (h.tokens) |t| if (t == .match) {
		distances[common.distCodeTable[t.match.distance].code] += 1;
	};
	var masks: std.ArrayList(ir.SymbolMask) = .empty;
	try rareGoals(a, &masks, &distances);
	return masks.items;
}

fn rareGoals(a: A, masks: *std.ArrayList(ir.SymbolMask), counts: []const u32) !void {
	var previous: ?usize = null;
	for (counts, 0..) |count, sym| {
		if (count == 0) continue;
		if (count > 2) { previous = null; continue; }
		const bit = @as(ir.SymbolMask, 1) << @intCast(sym);
		try masks.append(a, bit);
		if (previous) |p| try masks.append(a, bit | (@as(ir.SymbolMask, 1) << @intCast(p)));
		previous = sym;
	}
	var tail: ir.SymbolMask = 0;
	var uses: u32 = 0;
	var sym: usize = counts.len;
	while (sym > 0) {
		sym -= 1;
		const count = counts[sym];
		if (count == 0) continue;
		if (count > 2 or uses + count > 4) break;
		uses += count;
		tail |= @as(ir.SymbolMask, 1) << @intCast(sym);
	}
	if (@popCount(tail) > 2) try masks.append(a, tail);
}

const Context = struct { block: Block, prices: reparse.Prices };
const Task = struct {
	anchor: usize, context: usize, mask: ir.SymbolMask, request: ?deferred.Request = null,
	answer: ?deferred.Request.Answer = null, variant: usize = 0,
	exhausted: bool = false,
};
const Controller = struct {
	const Key = struct { anchor: usize, context: usize, mask: ir.SymbolMask };
	a: A, graph: *deferred.Graph,
	contexts: std.ArrayList(Context) = .empty,
	context_ids: std.StringHashMapUnmanaged(usize) = .empty,
	tasks: std.ArrayList(*Task) = .empty,
	task_ids: std.AutoHashMapUnmanaged(Key, void) = .empty,
	initial: usize = 0, initial_cursor: usize = 0, feedback_cursor: usize = 0,

	fn context(c: *Controller, encoded: Encoding) !?usize {
		if (c.context_ids.get(encoded.bytes)) |id| return id;
		if (c.contexts.items.len >= 16) {
			return null;
		}
		const block = try decode(c.a, encoded.bytes);
		if (block.body != .huff or block.body.huff.is_fixed) return null;
		const id = c.contexts.items.len;
		const bytes = try c.a.dupe(u8, encoded.bytes);
		try c.contexts.append(c.a, .{ .block = block,
			.prices = try reparse.prices(c.a, block.body.huff, .{}, 0, @splat(false)) });
		try c.context_ids.put(c.a, bytes, id);
		return id;
	}
	fn add(c: *Controller, anchor: usize, context_id: usize, mask: ir.SymbolMask) !void {
		const key: Key = .{ .anchor = anchor, .context = context_id, .mask = mask };
		if (c.task_ids.contains(key)) return;
		try c.task_ids.put(c.a, key, {});
		const task = try c.a.create(Task);
		task.* = .{ .anchor = anchor, .context = context_id, .mask = mask };
		try c.tasks.append(c.a, task);
	}
	fn addGoals(c: *Controller, id: usize) !void {
		for (try goals(c.a, c.contexts.items[id].block.body.huff)) |mask| try c.add(id, id, mask);
	}
	fn feedback(c: *Controller, task: *const Task, encoded: Encoding) !?usize {
		const before = c.contexts.items.len;
		const id = try c.context(encoded) orelse return null;
		// Re-price the unresolved original footprint; polishing may have
		// changed its token boundaries or already removed the target symbol.
		try c.add(task.anchor, id, task.mask);
		// A genuinely new completed context can ask for different joint
		// changes too. Its full encoding, not its histogram, identifies it.
		if (c.contexts.items.len > before) try c.addGoals(id);
		return id;
	}
	fn select(c: *Controller, feedback_turn: bool) ?usize {
		const start: usize = if (feedback_turn) c.initial else 0;
		const end: usize = if (feedback_turn) c.tasks.items.len else c.initial;
		if (start == end) return null;
		const cursor = if (feedback_turn) &c.feedback_cursor else &c.initial_cursor;
		for (0..end - start) |_| {
			const id = start + cursor.* % (end - start);
			cursor.* += 1;
			if (!c.tasks.items[id].exhausted) return id;
		}
		return null;
	}
	fn next(c: *Controller, task: *Task) !bool {
		if (task.answer != null) return true;
		const h = c.contexts.items[task.anchor].block.body.huff;
		if (task.request == null) {
			const spans = try deferred.Request.supports(c.a, h.tokens, task.mask);
			ensure(spans.len > 0 and spans.len <= 4);
			task.request = .{ .graph = c.graph, .tokens = h.tokens, .spans = spans,
				.mask = task.mask, .prices = c.contexts.items[task.context].prices };
		}
		task.answer = try task.request.?.next(c.a);
		if (task.answer == null) {
			task.exhausted = true;
			return false;
		}
		return true;
	}
};

const Cand = struct { task: usize, bytes: []const u8 };

/// A task's pending answer, materialized under its current variant and
/// assembled: the cheap part of an evaluation, without the read. Null when
/// the task is exhausted. The answer stays on the task until `advance`.
fn produce(c: *Controller, sa: A, ca: A, id: usize, is_last: bool) !?Cand {
	const task = c.tasks.items[id];
	if (task.exhausted) return null;
	if (!(try c.next(task))) return null;
	const answer = task.answer.?;
	const ctx = c.contexts.items[task.context];
	const candidate = try reparse.materializeBySymbol(sa, answer.tokens, if (task.variant == 0) ctx.block.body.huff else null, is_last);
	const request = try encode(sa, candidate);
	return .{ .task = id, .bytes = try ca.dupe(u8, request.bytes) };
}

fn advance(task: *Task) void {
	task.variant += 1;
	if (task.variant == 2) {
		task.variant = 0;
		task.answer = null;
	}
}

/// `backend.polishEncoded` is the production projection/check/cache service. Only
/// completed encodings cross that boundary. The caller owns the incumbent
/// restart policy and supplies the exploration budget.
pub fn run(a: A, seed: Block, edges: reparse.Edges, backend: anytype, budget: usize) !Block {
	const raw = edges.program.raw();
	if (budget == 0) return seed;
	if (raw.len > 4096 or seed.body != .huff or seed.body.huff.is_fixed) return seed;
	var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer arena.deinit();
	const ca = arena.allocator();
	var scratch = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	defer scratch.deinit();
	var chart_stats: deferred.Stats = .{ .max_heap_entries = 262144 };
	var graph: deferred.Graph = .{ .a = ca, .edges = edges, .stats = &chart_stats };
	var c: Controller = .{ .a = ca, .graph = &graph };
	var best = try encode(ca, seed);
	const seed_id = (try c.context(best)).?;
	try c.addGoals(seed_id);
	c.initial = c.tasks.items.len;
	if (c.initial == 0) return seed;
	var completed: std.StringHashMapUnmanaged(Encoding) = .empty;
	var evaluations: usize = 0;
	var turns: usize = 0;
	while (evaluations < budget and turns < 8 * budget) : (turns += 1) {
		_ = scratch.reset(.retain_capacity);
		const sa = scratch.allocator();
		// Initial requests keep two turns out of three; feedback has its own
		// cursor, so new contexts do not erase old continuations.
		const feedback_turn = turns % 3 == 2;
		const id = c.select(feedback_turn) orelse c.select(!feedback_turn) orelse break;
		const maybe = produce(&c, sa, ca, id, seed.is_last) catch |err| switch (err) {
			error.WorkLimit => break,
			else => |e| return e,
		};
		const cd = maybe orelse continue;
		const task = c.tasks.items[cd.task];
		var output: Encoding = undefined;
		const cached = completed.get(cd.bytes);
		if (cached) |hit| {
			output = hit;
		} else {
			const polished = try backend.polishEncoded(sa, cd.bytes);
			const result = try encode(sa, polished);
			output = .{ .bytes = try ca.dupe(u8, result.bytes), .bits = result.bits };
			try completed.put(ca, cd.bytes, output);
			// Bound logical new requests, independent of backend cache
			// warmth/eviction. Otherwise the cache would change the search,
			// rather than merely its runtime.
			evaluations += 1;
		}
		if (output.bits < best.bits) best = output;
		_ = try c.feedback(task, output);
		advance(task);
	}
	return decode(a, best.bytes);
}
