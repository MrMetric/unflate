#!/usr/bin/env python3
"""Compare compressors followed by unflate and the original DEFLATE optimizers."""
import argparse
from collections.abc import Callable
import gzip
import hashlib
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import tempfile
import time
import urllib.request
import zipfile
import zlib

ROOT = Path(__file__).resolve().parent
TOOLS = {
	'gzip': 'gzip', 'zopfli': 'zopfli', 'ect': 'ect',
	'unflate': str(ROOT / 'zig-out/bin/unflate'),
	'defluff': 'defluff', 'deflopt': 'DeflOpt.exe', 'wine': 'wine',
}
CORPORA = {
	'canterbury': 'https://corpus.canterbury.ac.nz/resources/cantrbry.zip',
	'enwik8': 'https://mattmahoney.net/dc/enwik8.zip',
}


def digest(path: Path) -> str:
	with path.open('rb') as f:
		return hashlib.file_digest(f, 'sha256').hexdigest()


def corpus_inputs(directory: Path) -> dict[str, Path]:
	checksums = {name: checksum for checksum, name in
		(line.split() for line in (ROOT / 'eval-corpora.sha256').read_text().splitlines())}
	inputs = {}
	for corpus, url in CORPORA.items():
		archive = directory / url.rsplit('/', 1)[1]
		if not archive.exists():
			print(f'Download {url}', flush=True)
			request = urllib.request.Request(url, headers={'User-Agent': 'unflate-evaluator'})
			with urllib.request.urlopen(request, timeout=60) as response, tempfile.NamedTemporaryFile(dir=directory) as target:
				shutil.copyfileobj(response, target)
				target.flush()
				shutil.copyfile(target.name, archive)
		if digest(archive) != checksums[archive.name]:
			raise ValueError(f'archive checksum mismatch: {archive}')
		with zipfile.ZipFile(archive) as z:
			for member in z.infolist():
				if not member.is_dir():
					inputs[f'{corpus}/{member.filename}'] = Path(z.extract(member, directory / 'inputs' / corpus))
	return inputs


def environment() -> dict:
	cpu = platform.processor()
	if Path('/proc/cpuinfo').exists():
		cpu = next((line.split(':', 1)[1].strip() for line in Path('/proc/cpuinfo').read_text().splitlines() if line.startswith('model name')), cpu)
	return {
		"cpu"   : cpu,
		"python": platform.python_version(),
		"zlib"  : zlib.ZLIB_RUNTIME_VERSION,
	}


def measure(tool: str, flags: list[str], source: Path, output: Path, expected_hash: str, compressed: bool = True) -> dict:
	"""Time compression (including required decoding), then verify the gzip output."""
	output.parent.mkdir(parents=True, exist_ok=True)
	with tempfile.TemporaryDirectory(dir=output.parent) as td:
		work = Path(td)
		result = work / 'output.gz'
		argv = [TOOLS[tool], *flags]
		if tool in ('ect', 'deflopt'):
			shutil.copyfile(source, result)
			if tool == 'ect':
				os.utime(result, (0, 0))  # ECT uses filesystem mtime for the gzip timestamp.
		if tool == 'deflopt':
			argv = [TOOLS['wine'], TOOLS[tool], *flags, 'Z:' + str(result.resolve())]
		start = time.perf_counter()
		if compressed and tool in ('gzip', 'zopfli'):
			with gzip.open(source, 'rb') as inp, (work / 'decoded').open('wb') as out:
				shutil.copyfileobj(inp, out)
			source = work / 'decoded'
		if tool == 'ect':
			subprocess.run([*argv, str(result)], stdout=subprocess.DEVNULL, check=True)
		elif tool == 'deflopt':
			subprocess.run(argv, stdout=subprocess.DEVNULL, env={**os.environ, 'WINEDEBUG': '-all'}, check=True)
		else:
			with source.open('rb') as inp, result.open('wb') as out:
				if tool == 'zopfli':
					argv.append(str(source))
				subprocess.run(argv, stdin=inp, stdout=out, check=True)
		seconds = time.perf_counter() - start
		with result.open('rb') as f:
			if f.read(8) != b'\x1f\x8b\x08\x00\x00\x00\x00\x00':
				raise ValueError('expected gzip without optional metadata or timestamp')
		with gzip.open(result, 'rb') as f:
			if hashlib.file_digest(f, 'sha256').hexdigest() != expected_hash:
				raise ValueError('decompressed content mismatch')
		result.replace(output)
	return {'bytes': output.stat().st_size, 'seconds': seconds}


def legacy_search(parent: str, run: Callable, directory: Path, report: dict) -> dict:
	"""Visit every reachable encoding, including ties and growth, retaining the smallest."""
	queue = [parent]
	seen = {digest(directory / (parent + '.gz'))}
	best = parent
	seconds = 0.0
	label = parent.rsplit('/', 1)[-1]
	for index, source in enumerate(queue):
		for tool, flags in (('defluff', []), ('deflopt', ['/bsack'])):
			prefix = label if index == 0 else f'{label}-legacy{index}'
			child = run(prefix + '-' + tool, tool, flags, source)
			row = report['runs'][child]
			seconds += row['seconds']
			if row['bytes'] < report['runs'][best]['bytes']:
				best = child
			checksum = digest(directory / (child + '.gz'))
			if checksum not in seen:
				seen.add(checksum)
				queue.append(child)
	return {'best': best, 'seconds': seconds}


def evaluate(name: str, raw: Path, directory: Path, report: dict) -> None:
	expected_hash = digest(raw)
	report['sources'][name] = {'bytes': raw.stat().st_size}

	def run(label: str, tool: str, flags: list[str], parent: str | None = None) -> str:
		run_id = name + '/' + label
		source = directory / (parent + '.gz') if parent else raw
		output = directory / (run_id + '.gz')
		print(f'RUN {run_id}', flush=True)
		row = measure(tool, flags, source, output, expected_hash, compressed=parent is not None)
		report['runs'][run_id] = {'input': parent or name, 'tool': tool, 'flags': flags, **row}
		print(f'  {row["bytes"]:,} B; {row["seconds"]:.3f} s', flush=True)
		return run_id

	seed = run('gzip9', 'gzip', ['-9', '-n', '-c'])
	baselines = [seed]
	for iterations in (1, 5, 15, 30):
		baselines.append(run(f'zopfli{iterations}', 'zopfli', ['--gzip', f'--i{iterations}', '-c'], seed))
	for level in range(1, 10):
		baselines.append(run(f'ect{level}', 'ect', ['-gzip', f'-{level}'], seed))
	for parent in baselines:
		label = parent.rsplit('/', 1)[1]
		run(label + '-unflate', 'unflate', [], parent)
		run(label + '-fast', 'unflate', ['--fast'], parent)
		report['legacy'][parent] = legacy_search(parent, run, directory, report)


def main() -> None:
	parser = argparse.ArgumentParser(description=__doc__)
	parser.add_argument('inputs', nargs='*', type=Path, help='raw files; defaults to downloading Canterbury and enwik8')
	parser.add_argument('--results', type=Path, default=ROOT / 'eval/results.json')
	parser.add_argument('--zopfli-version', help='Zopfli has no version switch; supply its version if known')
	args = parser.parse_args()
	if args.results.exists():
		parser.error(f'{args.results} already exists; choose a new --results path')
	for tool, command in TOOLS.items():
		found = shutil.which(command, mode=os.F_OK if tool == 'deflopt' else os.F_OK | os.X_OK)
		if found is None:
			parser.error(f'{tool} not found: {command}; install it or update TOOLS')
		if tool == 'deflopt':
			TOOLS[tool] = str(Path(found).resolve())
	versions = {'zopfli': args.zopfli_version}
	for tool, flag in (('gzip', '--version'), ('ect', '-help'), ('unflate', '--version')):
		probe = subprocess.run([TOOLS[tool], flag], capture_output=True, text=True, check=True)
		lines = (probe.stdout + probe.stderr).splitlines()
		versions[tool] = next((line for line in lines if line.startswith('Version ')), lines[0])
	# defluff prints its banner before rejecting empty input; DeflOpt has no version switch.
	for tool, argv in (('defluff', [TOOLS['defluff']]),
			('deflopt', [TOOLS['wine'], TOOLS['deflopt'], '/?'])):
		probe = subprocess.run(argv, input=b'', capture_output=True, env={**os.environ, 'WINEDEBUG': '-all'})
		versions[tool] = next((line.strip(' *\r') for line in
			(probe.stdout + probe.stderr).decode().splitlines() if tool.lower() in line.lower()), None)
		if versions[tool] is None:
			parser.error(f'{tool} version probe failed: {(probe.stdout + probe.stderr).decode().strip()}')
	versions['wine'] = subprocess.check_output([TOOLS['wine'], '--version'], text=True).strip()
	directory = ROOT / 'eval'
	directory.mkdir(exist_ok=True)
	inputs = {f'local/{p.name}': p.resolve() for p in args.inputs} if args.inputs else corpus_inputs(directory)
	if args.inputs and len(inputs) != len(args.inputs):
		parser.error('input files must have distinct basenames')
	report = {'environment': environment(), 'tools': versions, 'sources': {}, 'runs': {}, 'legacy': {}}
	args.results.parent.mkdir(parents=True, exist_ok=True)
	with args.results.open('x') as out, tempfile.TemporaryDirectory(dir=directory) as td:
		try:
			for name, raw in inputs.items():
				evaluate(name, raw, Path(td), report)
		finally:
			json.dump(report, out, indent="\t")
			out.write('\n')


if __name__ == '__main__':
	main()
