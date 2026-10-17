#!/usr/bin/env python3
"""Check the compressor adapters and archive handling without external tools."""
import gzip
import hashlib
import contextlib
import io
from pathlib import Path
import subprocess
import sys
import tempfile
from unittest.mock import patch
import zipfile

import evaluate as e


def main() -> None:
	with tempfile.TemporaryDirectory() as td:
		root = Path(td)
		raw = b'a reproducible gzip fixture\n' * 100
		expected = hashlib.sha256(raw).hexdigest()
		seed = root / 'seed.gz'
		seed.write_bytes(gzip.compress(raw, mtime=0))
		original = seed.read_bytes()
		output = root / 'output.gz'
		for missing in ('gzip', 'deflopt'):
			def locate(command, **kwargs):
				return None if command == e.TOOLS[missing] else sys.executable
			with patch.object(sys, 'argv', ['evaluate.py', '--results', str(root / 'missing.json')]), \
					patch.object(e.shutil, 'which', side_effect=locate), \
					patch.object(e.subprocess, 'run', side_effect=AssertionError('missing tool reached version probe')), \
					contextlib.redirect_stderr(io.StringIO()) as errors:
				try:
					e.main()
				except SystemExit as failure:
					assert failure.code == 2 and f'{missing} not found' in errors.getvalue()
				else:
					raise AssertionError('missing executable accepted')
		with patch.dict(e.TOOLS, unflate=sys.executable, zopfli=sys.executable, defluff=sys.executable):
			copy = ['-c', 'import sys; sys.stdout.buffer.write(sys.stdin.buffer.read())']
			for tool in ('unflate', 'defluff'):
				with patch.object(e.time, 'perf_counter', side_effect=[10.0, 12.5]):
					row = e.measure(tool, copy, seed, output, expected)
				assert row['seconds'] == 2.5 and row['bytes'] == len(original)
				assert output.read_bytes() == original == seed.read_bytes()
			# Zopfli receives decoded bytes. Recompression can legitimately grow them.
			flags = ['-c', 'import gzip,sys; from pathlib import Path; sys.stdout.buffer.write(gzip.compress(Path(sys.argv[1]).read_bytes(),compresslevel=0,mtime=0))']
			row = e.measure('zopfli', flags, seed, output, expected)
			assert row['bytes'] > len(original) and gzip.decompress(output.read_bytes()) == raw
			output.unlink()
			for code, exception in (
				('import gzip,sys; sys.stdout.buffer.write(gzip.compress(b"wrong",mtime=0))', ValueError),
				('import gzip,sys; sys.stdout.buffer.write(gzip.compress(b"wrong",mtime=123))', ValueError),
				('raise SystemExit(7)', subprocess.CalledProcessError),
			):
				try:
					e.measure('unflate', ['-c', code], seed, output, expected)
				except exception:
					pass
				else:
					raise AssertionError('invalid output accepted')
				assert not output.exists() and seed.read_bytes() == original

		def wine(argv, **kwargs):
			assert argv[:3] == [e.TOOLS['wine'], e.TOOLS['deflopt'], '/bsack']
			assert argv[3].startswith('Z:/') and kwargs['check']
			path = Path(argv[3][2:])
			assert path != seed and path.read_bytes() == original
			path.write_bytes(gzip.compress(raw, compresslevel=0, mtime=0))
		with patch.object(e.subprocess, 'run', wine):
			row = e.measure('deflopt', ['/bsack'], seed, output, expected)
			assert row['bytes'] > len(original) and seed.read_bytes() == original

		# The best state requires crossing both a byte tie and a larger output.
		graph = {b'aa': (b'bb', b'aa'), b'bb': (b'bb', b'ccc'),
			b'ccc': (b'd', b'bb'), b'd': (b'd', b'd')}
		(root / 'seed.gz').write_bytes(b'aa')
		report = {'runs': {'seed': {'bytes': 2}}}
		visited = []
		def run(label, tool, flags, parent):
			state = (root / (parent + '.gz')).read_bytes()
			visited.append((state, tool))
			data = graph[state][tool == 'deflopt']
			(root / (label + '.gz')).write_bytes(data)
			report['runs'][label] = {'bytes': len(data), 'seconds': 1.0}
			return label
		result = e.legacy_search('seed', run, root, report)
		assert (root / (result['best'] + '.gz')).read_bytes() == b'd'
		assert result['seconds'] == 8.0 and len(set(visited)) == 8
		assert 'seed-defluff' in report['runs'] and 'seed-deflopt' in report['runs']

		archive = root / 'source.zip'
		with zipfile.ZipFile(archive, 'w') as z:
			z.writestr('fixture', raw)
		(root / 'eval-corpora.sha256').write_text(f'{e.digest(archive)}  source.zip\n')
		cache = root / 'cache'
		cache.mkdir()
		with patch.object(e, 'ROOT', root), patch.object(e, 'CORPORA', {'test': archive.as_uri()}):
			inputs = e.corpus_inputs(cache)
			assert inputs['test/fixture'].read_bytes() == raw
			archive.unlink()
			inputs['test/fixture'].write_bytes(b'stale extraction')
			assert e.corpus_inputs(cache)['test/fixture'].read_bytes() == raw
			(cache / 'source.zip').write_bytes(b'corrupt archive')
			try:
				e.corpus_inputs(cache)
			except ValueError:
				pass
			else:
				raise AssertionError('corrupt archive accepted')
	print('evaluator checks passed')


if __name__ == '__main__':
	main()
