#!/usr/bin/env python3
"""Evaluation counters belong to one input, including reused batch workers."""
import gzip
import subprocess
import sys
import tempfile
from pathlib import Path


def check(binary: str) -> None:
	data = gzip.compress(bytes(range(256)) * 4, mtime=0)
	def run(args: list[str], stdin: bytes | None = None) -> dict[str, bytes]:
		p = subprocess.run([binary, *args], input=stdin, capture_output=True, check=True)
		rows = {}
		for line in p.stderr.splitlines():
			if line.startswith(b'explore-stats '):
				assert b' input=' in line, ('missing input label', line)
				counters, name = line.rsplit(b' input=', 1)
				assert name.decode() not in rows, ('duplicate statistics', line)
				rows[name.decode()] = counters
		return rows

	assert not run([], data), 'statistics should be opt-in'
	with tempfile.TemporaryDirectory() as td:
		paths = [Path(td) / f'input {i}.gz' for i in range(4)]
		for flag in ('--explore-stats', '--measure-agreement'):
			baseline = run([flag], data)
			assert set(baseline) == {'<stdin>'}, baseline
			counters = baseline['<stdin>']
			assert b'reads=0/0/0 ' not in counters, 'fixture must exercise counters'
			paths[0].write_bytes(data)
			assert run([flag, '-i', str(paths[0]), '-o', '/dev/null']) == {str(paths[0]): counters}
			for jobs in (1, 2):
				for path in paths:
					path.write_bytes(data)
				assert run([flag, '-j', str(jobs), *map(str, paths)]) == dict.fromkeys(map(str, paths), counters)
	print('CLI per-input statistics: OK')


if __name__ == '__main__':
	assert len(sys.argv) == 2, 'usage: test_cli_stats.py BINARY'
	check(str(Path(sys.argv[1]).resolve()))
