"""Write small seed corpora for each fuzz target into DIR/{deflate,gzip,png,zip}.

Seeds come from Python's zlib across levels and strategies, so the corpus
starts with stored, fixed and dynamic blocks, multi-block streams and
multiple gzip members. Extra files named on the command line are sorted into
the matching target by signature (raw DEFLATE is also extracted from gzip
files). Keep seeds small: optimizer time grows with block size.

usage: python3 fuzz/make_seeds.py DIR [FILE ...]
"""
import io
import os
import random
import struct
import sys
import zipfile
import zlib

MAX_SEED = 4 * 1024


def samples():
	rnd = random.Random(1951)
	text = b"It was the best of times, it was the worst of times, it was the age of wisdom. "
	yield b""
	yield b"a"
	yield b"ab" * 3
	yield text
	yield text * 20
	yield b"\x00" * 3000
	yield bytes(rnd.randrange(256) for _ in range(600))
	yield bytes(rnd.choice(b"ACGT") for _ in range(4000))
	yield bytes(range(256)) * 4
	words = text.split()
	yield b" ".join(rnd.choice(words) for _ in range(1200))
	# Long matches at the far end of the window and 258-byte runs.
	yield b"x" * 300 + bytes(rnd.randrange(256) for _ in range(9000)) + b"x" * 300


def deflate(data, level, strategy, wbits=-15, mem=8):
	c = zlib.compressobj(level, zlib.DEFLATED, wbits, mem, strategy)
	return c.compress(data) + c.flush()


def blocky(data, level):
	"""Several blocks: a full flush between pieces ends each block."""
	c = zlib.compressobj(level, zlib.DEFLATED, -15)
	out = b""
	for i in range(0, len(data), max(1, len(data) // 3)):
		out += c.compress(data[i:i + max(1, len(data) // 3)]) + c.flush(zlib.Z_FULL_FLUSH)
	return out + c.flush()


def raw_streams():
	strategies = (zlib.Z_DEFAULT_STRATEGY, zlib.Z_FILTERED, zlib.Z_HUFFMAN_ONLY, zlib.Z_RLE, zlib.Z_FIXED)
	for data in samples():
		for level in (0, 1, 6, 9):
			for strategy in strategies:
				yield data, deflate(data, level, strategy)
		yield data, blocky(data, 6)
		yield data, deflate(data, 9, zlib.Z_DEFAULT_STRATEGY, wbits=-9, mem=1)


def gzip_member(data, raw):
	header = b"\x1f\x8b\x08\x00" + b"\x00" * 4 + b"\x00\x03"
	return header + raw + struct.pack("<II", zlib.crc32(data), len(data) & 0xFFFFFFFF)


def gzip_named(data, raw):
	header = b"\x1f\x8b\x08\x08" + b"\x00" * 4 + b"\x02\x03" + b"seed.txt\x00"
	return header + raw + struct.pack("<II", zlib.crc32(data), len(data) & 0xFFFFFFFF)


def png_chunk(typ, data):
	return struct.pack(">I", len(data)) + typ + data + struct.pack(">I", zlib.crc32(typ + data))


def png(width, height, pixels, level, idat_split, aux):
	ihdr = struct.pack(">IIBBBBB", width, height, 8, 2, 0, 0, 0)
	rows = b"".join(b"\x00" + pixels[y * width * 3:(y + 1) * width * 3] for y in range(height))
	z = zlib.compress(rows, level)
	out = b"\x89PNG\r\n\x1a\n" + png_chunk(b"IHDR", ihdr)
	if aux:
		out += png_chunk(b"zTXt", b"Comment\x00\x00" + zlib.compress(b"seed " * 40, 1))
		out += png_chunk(b"iTXt", b"Title\x00\x01\x00en\x00Title\x00" + zlib.compress(b"seed title " * 10, 9))
		out += png_chunk(b"tEXt", b"Software\x00make_seeds.py")
	step = max(1, len(z) // idat_split)
	for i in range(0, len(z), step):
		out += png_chunk(b"IDAT", z[i:i + step])
	return out + png_chunk(b"IEND", b"")


def pngs():
	rnd = random.Random(2083)
	for w, h in ((1, 1), (8, 8), (32, 16), (40, 40)):
		smooth = bytes((x * 7 + y * 3 + c * 50) & 0xFF for y in range(h) for x in range(w) for c in range(3))
		noisy = bytes(rnd.randrange(256) for _ in range(w * h * 3))
		for pixels in (smooth, noisy):
			for level in (1, 9):
				yield png(w, h, pixels, level, 1, False)
		yield png(w, h, smooth, 6, 3, True)


def zips():
	data = list(samples())
	for compression in (zipfile.ZIP_DEFLATED, zipfile.ZIP_STORED):
		for level in (1, 9):
			buf = io.BytesIO()
			with zipfile.ZipFile(buf, "w", compression, compresslevel=level) as z:
				for i, d in enumerate(data[:6]):
					z.writestr(f"dir/file{i}.txt", d)
				z.comment = b"seed archive"
			yield buf.getvalue()
	buf = io.BytesIO()
	with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
		z.writestr("only.txt", data[4])
	yield buf.getvalue()


def gzip_raw(blob):
	"""Raw DEFLATE of each member, or nothing if the file does not parse."""
	out, pos = [], 0
	while pos < len(blob):
		d = zlib.decompressobj(31)
		try:
			d.decompress(blob[pos:])
		except zlib.error:
			return out
		if not d.eof:
			return out
		member = blob[pos:len(blob) - len(d.unused_data)]
		flags = member[3]
		k = 10
		if flags & 4:
			k += 2 + struct.unpack("<H", member[k:k + 2])[0]
		for bit in (8, 16):
			if flags & bit:
				k = member.index(b"\x00", k) + 1
		if flags & 2:
			k += 2
		out.append(member[k:-8])
		pos = len(blob) - len(d.unused_data)
	return out


def main():
	if len(sys.argv) < 2:
		sys.exit("usage: python3 fuzz/make_seeds.py DIR [FILE ...]")
	root = sys.argv[1]
	seeds = {t: {} for t in ("deflate", "gzip", "png", "zip")}

	def add(target, blob):
		if len(blob) <= MAX_SEED:
			seeds[target][zlib.crc32(blob) ^ len(blob) << 32] = blob

	for data, raw in raw_streams():
		add("deflate", raw)
		add("gzip", gzip_member(data, raw))
	members = [gzip_named(d, deflate(d, 6, zlib.Z_DEFAULT_STRATEGY)) for d in list(samples())[3:6]]
	add("gzip", b"".join(members))
	for blob in pngs():
		add("png", blob)
	for blob in zips():
		add("zip", blob)
	for path in sys.argv[2:]:
		with open(path, "rb") as f:
			blob = f.read()
		if blob.startswith(b"\x89PNG"):
			add("png", blob)
		elif blob.startswith(b"\x1f\x8b"):
			add("gzip", blob)
			for raw in gzip_raw(blob):
				add("deflate", raw)
		elif blob.startswith(b"PK"):
			add("zip", blob)

	for target, blobs in seeds.items():
		directory = os.path.join(root, target)
		os.makedirs(directory, exist_ok=True)
		for i, blob in enumerate(blobs.values()):
			with open(os.path.join(directory, f"seed{i:04d}"), "wb") as f:
				f.write(blob)
		print(f"{directory}: {len(blobs)} seeds")


if __name__ == "__main__":
	main()
