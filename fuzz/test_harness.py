#!/usr/bin/env python3
"""Inject optimizer errors into the real fuzz wrapper; verification must abort."""
import signal
import subprocess
import sys
import tempfile
from pathlib import Path


STUB = '''const std = @import("std");
fn fail(len: usize) error{Malformed, OutOfMemory, VerificationFailed} {
    return switch (len) { 0 => error.Malformed, 1 => error.OutOfMemory, else => error.VerificationFailed };
}
pub const deflate = struct {
    pub const Options = struct { reparse: bool = true, min_dist_codes: u8 = 2 };
    pub fn optimize(_: std.mem.Allocator, _: *std.ArrayList(u8), data: []const u8, _: Options, _: enum { none }) !void {
        return fail(data.len);
    }
};
pub const Format = enum { gzip, png, zip };
pub fn optimize(_: std.mem.Allocator, _: Format, data: []const u8, _: struct { stream: deflate.Options }) ![]const u8 {
    return fail(data.len);
}
'''
CALL = '''import ctypes, resource, sys
resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
lib = ctypes.CDLL(sys.argv[1])
fn = getattr(lib, 'unflate_fuzz_' + sys.argv[2])
types = [ctypes.c_void_p, ctypes.c_size_t, ctypes.c_void_p, ctypes.c_size_t]
fn.restype = ctypes.c_int64
args = [b'abc', int(sys.argv[3]), ctypes.create_string_buffer(3), 3]
if sys.argv[2] == 'container':
    types.insert(0, ctypes.c_int)
    args.insert(0, 1)
fn.argtypes = types
assert fn(*args) == -1
'''


def check() -> None:
	with tempfile.TemporaryDirectory() as td:
		stub = Path(td) / 'containers.zig'
		stub.write_text(STUB)
		library = Path(td) / 'harness.so'
		harness = Path(__file__).resolve().with_name('harness.zig')
		subprocess.run(['zig', 'build-lib', '-dynamic', '-lc', '--dep', 'containers',
			'-OReleaseSafe', '-fPIC', '-fno-stack-check', '-fno-stack-protector', f'-Mroot={harness}',
			'-OReleaseSafe', '-fPIC', '-fno-stack-check', '-fno-stack-protector', f'-Mcontainers={stub}',
			f'-femit-bin={library}'], check=True)
		for target in ('deflate', 'container'):
			for length in range(3):
				p = subprocess.run([sys.executable, '-c', CALL, str(library), target, str(length)], capture_output=True)
				if length == 2:
					assert p.returncode == -signal.SIGABRT, (target, 'verification failure was swallowed', p.returncode, p.stderr)
					assert b'DEFLATE verification failed' in p.stderr, p.stderr
				else:
					assert p.returncode == 0, (target, length, p.stderr)
	print('Fuzz wrapper error classification: OK')


if __name__ == '__main__':
	check()
