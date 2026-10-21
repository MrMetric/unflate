const std = @import("std");

pub fn rdint(comptime T: type, d: []const u8, p: usize, comptime endian: std.builtin.Endian) T
{
	return std.mem.readInt(T, d[p..][0..@divExact(@bitSizeOf(T), 8)], endian);
}

pub fn rdint_le(comptime T: type, d: []const u8, p: usize) T
{
	return rdint(T, d, p, .little);
}
pub fn rdint_be(comptime T: type, d: []const u8, p: usize) T
{
	return rdint(T, d, p, .big);
}

pub fn wrint(comptime T: type, d: []u8, p: usize, v: T, comptime endian: std.builtin.Endian) void
{
	std.mem.writeInt(T, d[p..][0..@divExact(@bitSizeOf(T), 8)], v, endian);
}

pub fn wrint_le(comptime T: type, d: []u8, p: usize, v: T) void
{
	wrint(T, d, p, v, .little);
}
pub fn wrint_be(comptime T: type, d: []u8, p: usize, v: T) void
{
	wrint(T, d, p, v, .big);
}
