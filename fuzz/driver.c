/* AFL++ persistent-mode driver for the unflate optimizer.
 *
 * Every input runs through the optimizer, valid or not, so parser crashes on
 * malformed input are reachable. When zlib/libzip accept the input, the
 * output must decode with them to the same content (and a container must not
 * grow). Those decoders are independent of the optimizer's own
 * std.compress.flate check, so a corruption that check misses still aborts.
 *
 * Environment:
 *   UNFLATE_FUZZ_TARGET          deflate (default) | gzip | png | zip
 *   UNFLATE_FUZZ_FAST            1 = --fast (no reparse)
 *   UNFLATE_FUZZ_MIN_DIST_CODES  0, 1 or 2 (default 2)
 *   UNFLATE_FUZZ_STRICT          1 = also abort on disagreement about input
 *                                validity (optimizer rejects what the
 *                                reference accepts, or the reverse). A
 *                                container corruption caught by the
 *                                optimizer's own roundtrip check surfaces
 *                                only here, as a rejection.
 *   UNFLATE_FUZZ_FIXUP           0 = run inputs as given (default 1: first
 *                                recompute gzip CRC/ISIZE/FHCRC, PNG chunk
 *                                CRCs and zlib FCHECK/Adler-32, so mutants
 *                                get past checksum checks and the content
 *                                check still applies)
 *   UNFLATE_FUZZ_VERBOSE         1 = print the outcome of each input
 *
 * Built without afl-cc (fuzz/build.sh's repro binary) it reads one input
 * from stdin or argv[1] and runs it once; with UNFLATE_FUZZ_WRITE_FIXED=PATH
 * it also writes the fixed-up input there, which reproduces with the CLI.
 */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <zip.h>
#include <zlib.h>

extern void unflate_fuzz_configure(int fast, int min_dist_codes);
extern int64_t unflate_fuzz_deflate(const uint8_t *in, size_t len, uint8_t *out, size_t cap);
extern int64_t unflate_fuzz_container(int kind, const uint8_t *in, size_t len, uint8_t *out, size_t cap);

enum target { T_DEFLATE = 0, T_GZIP = 1, T_PNG = 2, T_ZIP = 3 };

/* Inputs whose reference decoding exceeds this are skipped before the
 * optimizer runs: decompression bombs only measure search time. */
#define MAX_PLAIN ((size_t)1 << 20)
#define MAX_FILE ((size_t)1 << 20)

static enum target target;
static int strict, verbose, fixup = 1;

static void fail(const char *what)
{
	fprintf(stderr, "unflate-fuzz: %s\n", what);
	abort();
}

static void note(const char *what)
{
	if (verbose) fprintf(stderr, "unflate-fuzz: %s\n", what);
}

/* ── growable byte buffer, capped at MAX_PLAIN ── */

struct buf {
	uint8_t *p;
	size_t n, cap;
};

/* Returns 0 when the cap would be exceeded. */
static int put(struct buf *b, const void *data, size_t n)
{
	if (n > MAX_PLAIN - b->n) return 0;
	if (b->n + n > b->cap) {
		size_t cap = b->cap ? b->cap : 4096;
		while (cap < b->n + n) cap *= 2;
		uint8_t *p = realloc(b->p, cap);
		if (!p) fail("out of memory");
		b->p = p;
		b->cap = cap;
	}
	if (n) memcpy(b->p + b->n, data, n);
	b->n += n;
	return 1;
}

static int put_u32(struct buf *b, uint32_t v)
{
	uint8_t x[4] = { v >> 24, v >> 16, v >> 8, v };
	return put(b, x, 4);
}

static int same(const struct buf *a, const struct buf *b)
{
	return a->n == b->n && (a->n == 0 || memcmp(a->p, b->p, a->n) == 0);
}

/* ── zlib ── */

enum status { VALID, INVALID, TOO_BIG };

/* Decode one stream. window_bits selects raw (-15), zlib (15) or gzip
 * (31). Appends to `plain`; `used` receives the input bytes consumed. */
static enum status inflate_one(const uint8_t *in, size_t len, int window_bits, struct buf *plain, size_t *used)
{
	z_stream z;
	memset(&z, 0, sizeof z);
	if (inflateInit2(&z, window_bits) != Z_OK) fail("inflateInit2");
	z.next_in = (Bytef *)in;
	z.avail_in = len;
	enum status st = INVALID;
	uint8_t chunk[65536];
	for (;;) {
		z.next_out = chunk;
		z.avail_out = sizeof chunk;
		int rc = inflate(&z, Z_NO_FLUSH);
		if (!put(plain, chunk, sizeof chunk - z.avail_out)) {
			st = TOO_BIG;
			break;
		}
		if (rc == Z_STREAM_END) {
			st = VALID;
			break;
		}
		if (rc != Z_OK) break; /* data error, or truncated (Z_BUF_ERROR) */
	}
	*used = len - z.avail_in;
	inflateEnd(&z);
	return st;
}

/* Gzip file: one or more members, nothing else. zlib checks CRC and ISIZE. */
static enum status inflate_gzip(const uint8_t *in, size_t len, struct buf *plain)
{
	if (len == 0) return INVALID;
	size_t pos = 0;
	while (pos < len) {
		size_t used;
		enum status st = inflate_one(in + pos, len - pos, 31, plain, &used);
		if (st != VALID) return st;
		pos += used;
	}
	return VALID;
}

/* ── PNG canonical form ──
 * Chunk sequence with each consecutive IDAT run joined and decoded, and the
 * compressed text of zTXt, iCCP and compressed iTXt decoded. An auxiliary
 * stream that does not decode is kept raw (the optimizer must keep it
 * verbatim). The optimizer may merge IDAT chunks, so their split is not part
 * of the form. IDAT is decoded as libpng decodes it: the zlib stream must end
 * with a valid Adler-32, and bytes after it are ignored. */

static uint32_t rd32(const uint8_t *p)
{
	return (uint32_t)p[0] << 24 | (uint32_t)p[1] << 16 | (uint32_t)p[2] << 8 | p[3];
}

/* Offset of the zlib stream inside an auxiliary chunk, or -1. */
static long aux_stream_offset(const uint8_t *type, const uint8_t *d, size_t n)
{
	const uint8_t *nul = memchr(d, 0, n);
	if (!nul) return -1;
	size_t k = nul - d + 1;
	if (!memcmp(type, "zTXt", 4) || !memcmp(type, "iCCP", 4))
		return k + 1 <= n ? (long)(k + 1) : -1;
	if (!memcmp(type, "iTXt", 4)) {
		if (k + 2 > n || d[k] != 1) return -1; /* uncompressed */
		k += 2;
		for (int field = 0; field < 2; field++) {
			nul = memchr(d + k, 0, n - k);
			if (!nul) return -1;
			k = nul - d + 1;
		}
		return (long)k;
	}
	return -1;
}

/* Exactly one zlib stream filling the slice. */
static enum status inflate_exact(const uint8_t *in, size_t len, struct buf *plain)
{
	size_t used;
	enum status st = inflate_one(in, len, 15, plain, &used);
	if (st == VALID && used != len) return INVALID;
	return st;
}

static enum status png_canon(const uint8_t *in, size_t len, struct buf *form)
{
	static const uint8_t sig[8] = { 0x89, 'P', 'N', 'G', '\r', '\n', 0x1a, '\n' };
	if (len < 8 || memcmp(in, sig, 8)) return INVALID;
	struct buf idat = { 0 };
	enum status st = VALID;
	size_t pos = 8;
	int in_idat = 0;
	while (st == VALID && pos < len) {
		if (len - pos < 12) { st = INVALID; break; }
		size_t n = rd32(in + pos);
		if (n > 0x7fffffff || n > len - pos - 12) { st = INVALID; break; }
		const uint8_t *type = in + pos + 4, *d = in + pos + 8;
		if (crc32(0, type, n + 4) != rd32(d + n)) { st = INVALID; break; }
		pos += 12 + n;
		int is_idat = !memcmp(type, "IDAT", 4);
		if (in_idat && !is_idat) {
			struct buf plain = { 0 };
			size_t used;
			st = inflate_one(idat.p, idat.n, 15, &plain, &used);
			if (st == VALID && !(put(form, "IDAT", 4) && put_u32(form, plain.n) && put(form, plain.p, plain.n)))
				st = TOO_BIG;
			free(plain.p);
			idat.n = 0;
		}
		in_idat = is_idat;
		if (is_idat) {
			if (!put(&idat, d, n)) st = TOO_BIG;
			continue;
		}
		if (st != VALID) break;
		long off = aux_stream_offset(type, d, n);
		struct buf plain = { 0 };
		int decoded = off >= 0 && inflate_exact(d + off, n - off, &plain) == VALID;
		if (decoded) {
			if (!(put(form, type, 4) && put(form, "Z", 1) && put_u32(form, off) && put(form, d, off)
			      && put_u32(form, plain.n) && put(form, plain.p, plain.n)))
				st = TOO_BIG;
		} else {
			if (!(put(form, type, 4) && put(form, "R", 1) && put_u32(form, n) && put(form, d, n)))
				st = TOO_BIG;
		}
		free(plain.p);
	}
	/* A file ending inside an IDAT run has no IEND; the optimizer rejects it. */
	if (st == VALID && in_idat) st = INVALID;
	free(idat.p);
	return st;
}

/* ── ZIP canonical form via libzip (CRC checked on read) ── */

static enum status zip_canon(const uint8_t *in, size_t len, struct buf *form)
{
	zip_error_t err;
	zip_error_init(&err);
	zip_source_t *src = zip_source_buffer_create(in, len, 0, &err);
	if (!src) fail("zip_source_buffer_create");
	zip_t *za = zip_open_from_source(src, ZIP_RDONLY | ZIP_CHECKCONS, &err);
	zip_error_fini(&err);
	if (!za) {
		zip_source_free(src);
		return INVALID;
	}
	enum status st = VALID;
	zip_int64_t count = zip_get_num_entries(za, 0);
	int comment_len = 0;
	const char *comment = zip_get_archive_comment(za, &comment_len, ZIP_FL_ENC_RAW);
	if (!(put_u32(form, count) && put_u32(form, comment_len) && put(form, comment, comment_len))) st = TOO_BIG;
	for (zip_int64_t i = 0; st == VALID && i < count; i++) {
		zip_stat_t s;
		if (zip_stat_index(za, i, ZIP_FL_ENC_RAW, &s) != 0) { st = INVALID; break; }
		size_t name_len = strlen(s.name);
		if (!(put_u32(form, name_len) && put(form, s.name, name_len) && put_u32(form, s.crc))) { st = TOO_BIG; break; }
		if (s.encryption_method != ZIP_EM_NONE) {
			if (!put(form, "E", 1)) st = TOO_BIG;
			continue;
		}
		if (s.size > MAX_PLAIN - form->n) { st = TOO_BIG; break; }
		zip_file_t *f = zip_fopen_index(za, i, 0);
		if (!f) { st = INVALID; break; }
		uint8_t chunk[65536];
		zip_int64_t got;
		size_t total = 0;
		while ((got = zip_fread(f, chunk, sizeof chunk)) > 0) {
			total += got;
			if (!put(form, chunk, got)) { st = TOO_BIG; break; }
		}
		if (got < 0 || zip_fclose(f) != 0) { if (st == VALID) st = INVALID; }
		else if (st == VALID && total != s.size) st = INVALID;
	}
	zip_discard(za);
	return st;
}

/* ── checksum fixup ──
 * Rewrites checksums in place wherever the framing around them parses;
 * stops quietly where it does not. */

struct digest {
	size_t used; /* input bytes of the raw DEFLATE stream */
	uint32_t crc, adler, size;
};

static int digest_raw(const uint8_t *in, size_t len, struct digest *d)
{
	z_stream z;
	memset(&z, 0, sizeof z);
	if (inflateInit2(&z, -15) != Z_OK) fail("inflateInit2");
	z.next_in = (Bytef *)in;
	z.avail_in = len;
	d->crc = crc32(0, NULL, 0);
	d->adler = adler32(0, NULL, 0);
	size_t total = 0;
	int rc, ok = 0;
	uint8_t chunk[65536];
	do {
		z.next_out = chunk;
		z.avail_out = sizeof chunk;
		rc = inflate(&z, Z_NO_FLUSH);
		size_t n = sizeof chunk - z.avail_out;
		d->crc = crc32(d->crc, chunk, n);
		d->adler = adler32(d->adler, chunk, n);
		total += n;
		if (rc == Z_STREAM_END) ok = 1;
	} while (rc == Z_OK && total <= MAX_PLAIN);
	d->used = len - z.avail_in;
	d->size = total;
	inflateEnd(&z);
	return ok;
}

static void put_le32(uint8_t *p, uint32_t v)
{
	p[0] = v; p[1] = v >> 8; p[2] = v >> 16; p[3] = v >> 24;
}

static void put_be32(uint8_t *p, uint32_t v)
{
	p[0] = v >> 24; p[1] = v >> 16; p[2] = v >> 8; p[3] = v;
}

static void fixup_gzip(uint8_t *p, size_t len)
{
	size_t pos = 0;
	while (len - pos >= 18 && p[pos] == 0x1f && p[pos + 1] == 0x8b && p[pos + 2] == 8) {
		uint8_t flg = p[pos + 3];
		size_t k = pos + 10;
		if (flg & 4) k += 2 + (p[k] | p[k + 1] << 8);
		for (int bit = 8; bit <= 16; bit <<= 1) {
			if (!(flg & bit)) continue;
			const uint8_t *nul = k < len ? memchr(p + k, 0, len - k) : NULL;
			if (!nul) return;
			k = nul - p + 1;
		}
		if (flg & 2) {
			if (k + 2 > len) return;
			uint32_t c = crc32(0, p + pos, k - pos);
			p[k] = c;
			p[k + 1] = c >> 8;
			k += 2;
		}
		if (k > len) return;
		struct digest d;
		if (!digest_raw(p + k, len - k, &d) || len - k - d.used < 8) return;
		k += d.used;
		put_le32(p + k, d.crc);
		put_le32(p + k + 4, d.size);
		pos = k + 8;
	}
}

/* A zlib stream at the start of p[0..len]: fix FCHECK, then the Adler-32
 * right after the final block when four bytes fit there. Bytes beyond it stay
 * as trailing data, which libpng accepts. */
static void fixup_zlib(uint8_t *p, size_t len)
{
	if (len < 6) return;
	unsigned flg = p[1] & 0xe0;
	p[1] = flg | (31 - (p[0] * 256u + flg) % 31) % 31;
	struct digest d;
	if (digest_raw(p + 2, len - 2, &d) && len - 2 - d.used >= 4) put_be32(p + 2 + d.used, d.adler);
}

static void fixup_png(uint8_t *p, size_t len)
{
	if (len < 8 || memcmp(p, "\x89PNG\r\n\x1a\n", 8)) return;
	/* Chunk data offsets, in file order; IDAT runs are reassembled in `run`. */
	struct { size_t off, n; int idat; } chunks[4096];
	size_t count = 0;
	for (size_t pos = 8; len - pos >= 12 && count < 4096;) {
		size_t n = rd32(p + pos);
		if (n > len - pos - 12) break;
		chunks[count].off = pos + 8;
		chunks[count].n = n;
		chunks[count].idat = !memcmp(p + pos + 4, "IDAT", 4);
		count++;
		pos += 12 + n;
	}
	struct buf run = { 0 };
	for (size_t i = 0; i < count; i++) {
		if (!chunks[i].idat) {
			uint8_t *d = p + chunks[i].off;
			long off = aux_stream_offset(d - 4, d, chunks[i].n);
			if (off >= 0) fixup_zlib(d + off, chunks[i].n - off);
			continue;
		}
		size_t j = i;
		run.n = 0;
		while (j < count && chunks[j].idat && put(&run, p + chunks[j].off, chunks[j].n)) j++;
		if (j < count && chunks[j].idat) break; /* run over the size cap */
		fixup_zlib(run.p, run.n);
		for (size_t k = i, at = 0; k < j; at += chunks[k].n, k++) memcpy(p + chunks[k].off, run.p + at, chunks[k].n);
		i = j - 1;
	}
	free(run.p);
	for (size_t i = 0; i < count; i++) {
		uint8_t *type = p + chunks[i].off - 4;
		put_be32(type + 4 + chunks[i].n, crc32(0, type, chunks[i].n + 4));
	}
}

/* ── one input ── */

static enum status reference(enum target t, const uint8_t *in, size_t len, struct buf *form)
{
	size_t used;
	switch (t) {
	case T_DEFLATE: return inflate_one(in, len, -15, form, &used);
	case T_GZIP: return inflate_gzip(in, len, form);
	case T_PNG: return png_canon(in, len, form);
	case T_ZIP: return zip_canon(in, len, form);
	}
	fail("unknown target");
	return INVALID;
}

static const char *write_fixed;

static void run_one(const uint8_t *given, size_t len)
{
	if (len > MAX_FILE) return;
	uint8_t *in = malloc(len ? len : 1);
	if (!in) fail("out of memory");
	if (len) memcpy(in, given, len);
	if (fixup && target == T_GZIP) fixup_gzip(in, len);
	if (fixup && target == T_PNG) fixup_png(in, len);
	if (write_fixed) {
		FILE *f = fopen(write_fixed, "wb");
		if (!f || fwrite(in, 1, len, f) != len || fclose(f)) fail("cannot write UNFLATE_FUZZ_WRITE_FIXED");
	}
	struct buf before = { 0 }, after = { 0 };
	enum status st = reference(target, in, len, &before);
	if (st == TOO_BIG) {
		note("skipped: reference output over the size cap");
		goto done;
	}

	/* A raw stream may legitimately grow (the container guard is what bounds
	 * file size), so give it headroom; containers must fit in the input. */
	size_t cap = target == T_DEFLATE ? 2 * len + 65536 : len;
	uint8_t *out = malloc(cap ? cap : 1);
	if (!out) fail("out of memory");
	int64_t r = target == T_DEFLATE ? unflate_fuzz_deflate(in, len, out, cap)
	                                : unflate_fuzz_container(target, in, len, out, cap);

	if (target != T_DEFLATE && r > (int64_t)len) fail("container output larger than input");
	if (r == -2) {
		note("skipped: raw output over the headroom cap");
	} else if (r < 0) {
		if (st == VALID && strict) fail("optimizer rejected input the reference accepts");
		note(st == VALID ? "rejected (reference accepts)" : "rejected (reference rejects)");
	} else if (st != VALID) {
		/* Containers pass some inputs through verbatim (BGZF, Zip64,
		 * unparseable ZIP entries); identical bytes are no claim. */
		int verbatim = (size_t)r == len && memcmp(out, in, len) == 0;
		if (strict && !verbatim) fail("optimizer re-encoded input the reference rejects");
		note(verbatim ? "passed through (reference rejects)" : "re-encoded (reference rejects)");
	} else {
		enum status st2 = reference(target, out, (size_t)r, &after);
		if (st2 == INVALID) fail("output rejected by reference decoder");
		if (st2 == TOO_BIG) fail("output decodes larger than input");
		if (!same(&before, &after)) fail("output content differs from input");
		note("ok");
	}
	free(out);
done:
	free(before.p);
	free(after.p);
	free(in);
}

/* ── entry ── */

static int env_int(const char *name, int dflt)
{
	const char *v = getenv(name);
	return v && *v ? atoi(v) : dflt;
}

static void configure(void)
{
	const char *t = getenv("UNFLATE_FUZZ_TARGET");
	if (!t || !*t || !strcmp(t, "deflate")) target = T_DEFLATE;
	else if (!strcmp(t, "gzip")) target = T_GZIP;
	else if (!strcmp(t, "png")) target = T_PNG;
	else if (!strcmp(t, "zip")) target = T_ZIP;
	else {
		fprintf(stderr, "unflate-fuzz: UNFLATE_FUZZ_TARGET must be deflate, gzip, png or zip\n");
		exit(2);
	}
	int floor = env_int("UNFLATE_FUZZ_MIN_DIST_CODES", 2);
	if (floor < 0 || floor > 2) {
		fprintf(stderr, "unflate-fuzz: UNFLATE_FUZZ_MIN_DIST_CODES must be 0, 1 or 2\n");
		exit(2);
	}
	strict = env_int("UNFLATE_FUZZ_STRICT", 0);
	fixup = env_int("UNFLATE_FUZZ_FIXUP", 1);
	verbose = env_int("UNFLATE_FUZZ_VERBOSE", 0);
	unflate_fuzz_configure(env_int("UNFLATE_FUZZ_FAST", 0), floor);
}

#ifdef __AFL_FUZZ_TESTCASE_LEN

__AFL_FUZZ_INIT();

int main(void)
{
	configure();
	__AFL_INIT();
	const uint8_t *buf = __AFL_FUZZ_TESTCASE_BUF;
	while (__AFL_LOOP(1000)) run_one(buf, __AFL_FUZZ_TESTCASE_LEN);
	return 0;
}

#else

int main(int argc, char **argv)
{
	configure();
	FILE *f = argc > 1 ? fopen(argv[1], "rb") : stdin;
	if (!f) {
		perror(argv[1]);
		return 2;
	}
	struct buf in = { 0 };
	uint8_t chunk[65536];
	size_t n;
	while ((n = fread(chunk, 1, sizeof chunk, f)) > 0) {
		if (in.n + n > in.cap) {
			in.cap = (in.n + n) * 2;
			in.p = realloc(in.p, in.cap);
			if (!in.p) fail("out of memory");
		}
		memcpy(in.p + in.n, chunk, n);
		in.n += n;
	}
	verbose = 1;
	write_fixed = getenv("UNFLATE_FUZZ_WRITE_FIXED");
	run_one(in.p ? in.p : (const uint8_t *)"", in.n);
	free(in.p);
	return 0;
}

#endif
