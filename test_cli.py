#!/usr/bin/env python3
"""Exercise the built CLI, including failures before an in-place rewrite."""
import gzip
import io
import os
from pathlib import Path
import resource
import signal
import struct
import subprocess
import sys
import tempfile
import zipfile
import zlib

BINARY = Path(sys.argv[1]).resolve() if len(sys.argv) > 1 else Path(__file__).resolve().parent / 'zig-out/bin/unflate'


def run(*args: str, **kwargs: object) -> subprocess.CompletedProcess[bytes]:
	return subprocess.run([str(BINARY), *args], capture_output=True, **kwargs)


def chunk(kind: bytes, data: bytes) -> bytes:
	return struct.pack('>I', len(data)) + kind + data + struct.pack('>I', zlib.crc32(kind + data))


def containers() -> None:
	raw = b'container roundtrip\n' * 32
	gz = gzip.compress(raw, compresslevel=0, mtime=123456)
	archive = io.BytesIO()
	with zipfile.ZipFile(archive, 'w', compression=zipfile.ZIP_DEFLATED, compresslevel=0) as z:
		z.comment = b'archive comment'
		entry = zipfile.ZipInfo('entry.txt', (2020, 1, 2, 3, 4, 6))
		entry.comment = b'entry comment'
		entry.compress_type = zipfile.ZIP_DEFLATED
		z.writestr(entry, raw)
	zip_bytes = archive.getvalue()
	pixels = b'\0' + b'\x44' * 128
	ihdr = struct.pack('>IIBBBBB', 128, 1, 8, 0, 0, 0, 0)
	text = b'label\0preserved text'
	png = b'\x89PNG\r\n\x1a\n' + chunk(b'IHDR', ihdr) + chunk(b'tEXt', text) + chunk(b'IDAT', zlib.compress(pixels, 0)) + chunk(b'IEND', b'')
	for flags in ([], ['--fast']):
		for data in (gz, zip_bytes, png):
			r = run(*flags, input=data)
			assert r.returncode == 0, r.stderr
			assert len(r.stdout) <= len(data)
			if data == gz:
				assert gzip.decompress(r.stdout) == raw and r.stdout[:10] == gz[:10]
			elif data == zip_bytes:
				with zipfile.ZipFile(io.BytesIO(r.stdout)) as z:
					assert z.read('entry.txt') == raw and z.comment == b'archive comment'
					actual = z.getinfo('entry.txt')
					assert actual.comment == entry.comment and actual.date_time == entry.date_time
			else:
				pos, chunks = 8, {}
				while pos < len(r.stdout):
					n = struct.unpack_from('>I', r.stdout, pos)[0]
					kind, payload = r.stdout[pos+4:pos+8], r.stdout[pos+8:pos+8+n]
					assert zlib.crc32(kind + payload) == struct.unpack_from('>I', r.stdout, pos+8+n)[0]
					chunks[kind] = chunks.get(kind, b'') + payload
					pos += n + 12
				assert chunks[b'IHDR'] == ihdr and chunks[b'tEXt'] == text
				assert zlib.decompress(chunks[b'IDAT']) == pixels
			assert run(*flags, input=r.stdout).stdout == r.stdout, 'not a fixed point'


def main() -> None:
	containers()
	failures = []
	with tempfile.TemporaryDirectory() as td:
		root = Path(td)
		path = root / 'input.gz'
		original = gzip.compress(b'backup failure regression\n' * 32, compresslevel=0, mtime=0)
		path.write_bytes(original)
		backup = path.with_name(path.name + '.unflate-bak')
		backup.write_bytes(b'existing recovery data')
		r = run('-j1', str(path))
		assert r.returncode == 1 and path.read_bytes() == original
		assert backup.read_bytes() == b'existing recovery data'
		if b'EXIST' not in r.stdout + r.stderr:
			failures.append(f'backup collision lacks errno: {r.stdout!r} {r.stderr!r}')
		backup.unlink()
		before = path.stat()
		def limit_descriptors() -> None:
			resource.setrlimit(resource.RLIMIT_NOFILE, (4, resource.getrlimit(resource.RLIMIT_NOFILE)[1]))
		r = run('-j1', str(path), preexec_fn=limit_descriptors)
		assert r.returncode == 1 and path.read_bytes() == original
		assert b'MFILE' in r.stdout + r.stderr, r
		assert path.stat().st_ino == before.st_ino and path.stat().st_mtime_ns == before.st_mtime_ns
		if backup.exists():
			failures.append('failed backup preparation leaves a blocking backup')
			backup.unlink()
		def limit_backup_size() -> None:
			signal.signal(signal.SIGXFSZ, signal.SIG_IGN)
			resource.setrlimit(resource.RLIMIT_FSIZE, (128, resource.getrlimit(resource.RLIMIT_FSIZE)[1]))
		r = run('-j1', str(path), preexec_fn=limit_backup_size)
		assert r.returncode == 1 and path.read_bytes() == original
		assert b'FBIG' in r.stdout + r.stderr, r
		if backup.exists():
			failures.append('partial backup write leaves a blocking backup')
			backup.unlink()
		if os.geteuid() != 0:
			path.chmod(0)
			try:
				r = run('-j1', str(path))
				assert r.returncode == 1 and b'ACCES' in r.stdout + r.stderr, r
			finally:
				path.chmod(0o600)
			path.chmod(0o444)
			try:
				before = path.stat()
				for _ in range(2):
					r = run('-j1', str(path))
					assert r.returncode == 1 and b'ACCES' in r.stdout + r.stderr, r
					assert not backup.exists(), 'refused truncation leaves a blocking backup'
					assert path.read_bytes() == original
					assert path.stat().st_ino == before.st_ino and path.stat().st_mtime_ns == before.st_mtime_ns
			finally:
				path.chmod(0o600)
		for args in ((str(path / 'child'),), ('-i', str(path / 'child'), '-o', '/dev/null')):
			r = run(*args)
			assert r.returncode != 0 and b'NOTDIR' in r.stderr, r
		# A directory descriptor reliably makes read(2) fail with EISDIR.
		fd = os.open(root, os.O_RDONLY | os.O_DIRECTORY)
		try:
			r = run(stdin=fd)
		finally:
			os.close(fd)
		if r.returncode == 0 or r.stdout or b'ISDIR' not in r.stderr:
			failures.append(f'filter read failure swallowed: {r.stdout!r} {r.stderr!r}')
		# Even a complete gzip must not be emitted if the following read fails.
		reader, writer = os.pipe2(os.O_NONBLOCK)
		try:
			os.write(writer, original)
			r = run(stdin=reader)
		finally:
			os.close(reader)
			os.close(writer)
		assert r.returncode == 1 and not r.stdout and b'AGAIN' in r.stderr, r
		# Successful in-place rewrite preserves file identity and metadata.
		path.chmod(0o640)
		os.utime(path, ns=(1234567890000000000, 1234567891000000000))
		os.setxattr(path, 'user.unflate-test', b'preserved')
		before = path.stat()
		alias = root / 'alias.gz'
		os.link(path, alias)
		r = run('-r', '-j2', str(root))
		assert r.returncode == 0 and b'1 file(s)' in r.stdout, r
		after = path.stat()
		for field in ('st_ino', 'st_mode', 'st_uid', 'st_gid', 'st_mtime_ns'):
			assert getattr(before, field) == getattr(after, field), field
		assert os.getxattr(alias, 'user.unflate-test') == b'preserved'
		assert gzip.decompress(alias.read_bytes()) == gzip.decompress(original)
		assert after.st_size < before.st_size and not backup.exists()
		assert run('-i', str(path), '-o', '/dev/null').returncode == 0
		output = root / 'output.gz'
		output.write_bytes(b'keep me')
		assert run('-i', str(path), '-o', str(output)).returncode != 0
		assert output.read_bytes() == b'keep me'
		bad = run(input=original[:-5])
		assert bad.returncode != 0 and not bad.stdout
	assert not failures, '\n'.join(failures)
	print('CLI checks passed')


if __name__ == '__main__':
	main()
