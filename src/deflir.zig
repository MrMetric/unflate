//! Semantic DEFLATE IR. Encodings live in deflasm; prices and search state do
//! not belong to the immutable output program or its interval alternatives.
const std = @import("std");
const deflasm = @import("deflasm.zig");
const common = @import("deflcommon.zig");

pub const Span = struct {
	start: usize,
	length: usize,

	pub fn token(start: usize, t: deflasm.Token) Span {
		return .{ .start = start, .length = switch (t) { .lit => 1, .match => |m| m.length } };
	}

	pub fn bytes(s: Span, p: Program) []const u8 {
		return p.raw()[s.start..][0..s.length];
	}
};

/// Immutable history followed by output; consumers borrow the same buffer.
/// A span's identity includes its program and position: equal text elsewhere
/// need not admit the same relative copies.
pub const Program = struct {
	bytes: []const u8,
	history: usize,

	pub fn raw(p: Program) []const u8 { return p.bytes[p.history..]; }
	pub fn prior(p: Program) []const u8 { return p.bytes[0..p.history]; }

	pub fn init(a: std.mem.Allocator, output: []const u8, dictionary: []const u8) !Program {
		return .{ .bytes = try std.mem.concat(a, u8, &.{ dictionary, output }), .history = dictionary.len };
	}

	/// Own one buffer for history and output, allocated in the block arena.
	pub fn decode(a: std.mem.Allocator, block: deflasm.Block, dictionary: []const u8) !Program {
		if (block.body == .stored) return init(a, block.body.stored, dictionary);
		var length: usize = dictionary.len;
		for (block.body.huff.tokens) |t| length = std.math.add(usize, length, Span.token(0, t).length) catch return error.Malformed;
		const buffer = try a.alloc(u8, length);
		errdefer a.free(buffer);
		@memcpy(buffer[0..dictionary.len], dictionary);
		var pos: usize = dictionary.len;
		for (block.body.huff.tokens) |t| switch (t) {
			.lit => |b| { buffer[pos] = b; pos += 1; },
			.match => |m| {
				if (m.length < 3 or m.length > 258 or m.distance == 0 or m.distance > 32768 or
					m.distance > pos) return error.Malformed;
				for (0..m.length) |_| {
					buffer[pos] = buffer[pos - m.distance];
					pos += 1;
				}
			},
		};
		return .{ .bytes = buffer, .history = dictionary.len };
	}

	/// Check an instruction without executing or allocating another output.
	/// Overlapping source and target slices are intentional: induction over
	/// output positions establishes the same semantics as a forward LZ copy.
	pub fn accepts(p: Program, start: usize, t: deflasm.Token) bool {
		const s = Span.token(start, t);
		if (start > p.raw().len or s.length > p.raw().len - start) return false;
		switch (t) {
			.lit => |b| return p.raw()[start] == b,
			.match => |m| {
				if (m.length < 3 or m.length > 258 or m.distance == 0 or m.distance > 32768) return false;
				const pos = p.history + start;
				return m.distance <= pos and std.mem.eql(u8, p.bytes[pos..][0..m.length], p.bytes[pos - m.distance..][0..m.length]);
			},
		}
	}

	pub fn check(p: Program, block: deflasm.Block) void {
		if (block.body == .stored) {
			if (!std.mem.eql(u8, p.raw(), block.body.stored)) @panic("stored candidate changed program output");
			return;
		}
		var pos: usize = 0;
		for (block.body.huff.tokens) |t| {
			if (!p.accepts(pos, t)) @panic("candidate instruction changed program output");
			pos += Span.token(pos, t).length;
		}
		if (pos != p.raw().len) @panic("candidate changed program length");
	}
};

pub const Edge = struct { distance: u16, length: u16 };

/// Low bits exclude distance classes 0..29; bits 32..60 exclude canonical
/// length classes 257..285. Length 258 is one semantic class regardless of
/// its eventual spelling as 285 or 284+31. Literals remain available.
pub const SymbolMask = u64;
pub fn matchSymbols(length: u16, distance: u16) SymbolMask {
	return (@as(SymbolMask, 1) << @intCast(common.distCodeTable[distance].code)) |
		(@as(SymbolMask, 1) << @intCast(32 + common.lenCodeTable[length].code - 257));
}

/// Each stored match represents lengths 3..length; literals are implicit.
/// The matcher supplies a bounded subset of legal matches, not all programs.
pub const Graph = struct {
	program: Program,
	offsets: []const usize,
	items: []const Edge,
	cut_positions: usize,

	pub fn at(g: Graph, pos: usize) []const Edge {
		return g.items[g.offsets[pos]..g.offsets[pos + 1]];
	}

	pub fn alternatives(g: Graph, span: Span, mask: SymbolMask) Alternatives {
		std.debug.assert(span.length > 0 and span.start + span.length <= g.program.raw().len);
		return .{ .edges = g.at(span.start), .limit = span.length, .mask = mask };
	}
};

/// Literal first, then ascending lengths within the matcher's source order.
/// Clipping and symbol restrictions are shared by every deferred reader.
pub const Alternatives = struct {
	edges: []const Edge,
	limit: usize,
	mask: SymbolMask,
	length: usize = 1,

	pub fn next(it: *Alternatives) ?Edge {
		if (it.length == 1) {
			it.length = 3;
			return .{ .length = 1, .distance = 0 };
		}
		while (it.edges.len > 0) {
			const e = it.edges[0];
			if (it.mask & (@as(SymbolMask, 1) << @intCast(common.distCodeTable[e.distance].code)) == 0 and
				it.length <= @min(e.length, it.limit)) {
				const n = it.length;
				it.length += 1;
				if (it.mask & matchSymbols(@intCast(n), e.distance) != 0) continue;
				return .{ .length = @intCast(n), .distance = e.distance };
			}
			it.edges = it.edges[1..];
			it.length = 3;
		}
		return null;
	}
};

test "interval equivalence includes history, position, overlap and exact coverage" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	const p = try Program.init(a, "abcabcabcx", "zzabc");
	try std.testing.expect(p.accepts(0, .{ .match = .{ .length = 9, .distance = 3 } }));
	try std.testing.expect(p.accepts(0, .{ .match = .{ .length = 3, .distance = 3 } }));
	try std.testing.expect(!p.accepts(1, .{ .match = .{ .length = 9, .distance = 3 } }));
	try std.testing.expect(!p.accepts(0, .{ .match = .{ .length = 3, .distance = 6 } }));
	const other = try Program.init(a, p.raw(), "zzabd");
	try std.testing.expect(!other.accepts(0, .{ .match = .{ .length = 3, .distance = 3 } }));
	try std.testing.expect(other.accepts(3, .{ .match = .{ .length = 6, .distance = 3 } }));
	try std.testing.expect(!p.accepts(0, .{ .match = .{ .length = 3, .distance = 0 } }));
	try std.testing.expect(!p.accepts(p.raw().len, .{ .lit = 'x' }));
	const historical = try Program.init(a, "abc", "abczz");
	try std.testing.expect(historical.accepts(0, .{ .match = .{ .length = 3, .distance = 5 } }));
	var window: [32768]u8 = @splat('z');
	@memcpy(window[0..3], "abc");
	const boundary = try Program.init(a, "abc", &window);
	try std.testing.expect(boundary.accepts(0, .{ .match = .{ .length = 3, .distance = 32768 } }));
	try std.testing.expect(!boundary.accepts(0, .{ .match = .{ .length = 3, .distance = 32769 } }));
}

test "program decode and interval verification agree with a forward interpreter" {
	var arena = std.heap.ArenaAllocator.init(std.testing.allocator);
	defer arena.deinit();
	const a = arena.allocator();
	var random = std.Random.DefaultPrng.init(0x6972);
	var expected: [900]u8 = undefined;
	var tokens: [100]deflasm.Token = undefined;
	const prior = "abcabcde";
	var pos: usize = 0;
	for (&tokens) |*t| {
		if (random.random().boolean()) {
			const b = random.random().intRangeAtMost(u8, 'a', 'e');
			t.* = .{ .lit = b };
			expected[pos] = b;
			pos += 1;
		} else {
			const d = random.random().intRangeAtMost(u16, 1, @intCast(pos + prior.len));
			const n = random.random().intRangeAtMost(u16, 3, 9);
			t.* = .{ .match = .{ .length = n, .distance = d } };
			for (0..n) |_| {
				expected[pos] = if (d > pos) prior[prior.len - (d - pos)] else expected[pos - d];
				pos += 1;
			}
		}
	}
	const block: deflasm.Block = .{ .is_last = true, .body = .{ .huff = .{
		.is_fixed = true, .tokens = &tokens, .ll_lengths = &.{}, .dist_lengths = &.{},
		.cl_lengths = @splat(0), .cl_entries = &.{},
	} } };
	const p = try Program.decode(a, block, prior);
	try std.testing.expectEqualSlices(u8, expected[0..pos], p.raw());
	p.check(block);
	var bad = block;
	bad.body.huff.tokens = tokens[0..1];
	const first = tokens[0];
	for ([_]deflasm.Match{
		.{ .length = 3, .distance = 0 }, .{ .length = 3, .distance = 9 },
		.{ .length = 2, .distance = 1 }, .{ .length = 259, .distance = 1 },
	}) |m| {
		tokens[0] = .{ .match = m };
		try std.testing.expectError(error.Malformed, Program.decode(std.testing.allocator, bad, prior));
	}
	tokens[0] = first;
	// Check every legal length/distance against an independent byte oracle,
	// including candidates absent from the original parse.
	for (0..pos - 2) |start| for (1..@min(50, start + prior.len) + 1) |d| {
		for (3..@min(12, pos - start) + 1) |n| {
			var matches = true;
			for (0..n) |i| {
				const at = start + i;
				const b = if (d > at) prior[prior.len - (d - at)] else expected[at - d];
				matches = matches and expected[at] == b;
			}
			try std.testing.expectEqual(matches, p.accepts(start, .{ .match = .{ .length = @intCast(n), .distance = @intCast(d) } }));
		}
	};
}

