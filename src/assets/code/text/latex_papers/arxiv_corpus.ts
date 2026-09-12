import { mkdir, readFile, writeFile } from "node:fs/promises";
import { gunzipSync } from "node:zlib";
import { fileURLToPath } from "node:url";
import { task } from "knitting";
import { type PaperRecord, parsePaperHost, type PaperSource } from "./tex_parse.ts";

// Sixteen well-known papers, chosen for the spread: the smallest is 22 KB of
// LaTeX and the largest is 226 KB. Two of them are PDF-only submissions, which
// is a case any real corpus job has to survive.
export const PAPER_IDS = [
  "1706.03762", // Attention Is All You Need
  "1512.03385", // Deep Residual Learning
  "1409.1556", // VGG
  "1810.04805", // BERT
  "1406.2661", // Generative Adversarial Nets
  "1505.04597", // U-Net
  "1312.6114", // Auto-Encoding Variational Bayes
  "1502.03167", // Batch Normalization
  "1301.3781", // word2vec
  "1607.06450", // Layer Normalization
  "2010.11929", // An Image is Worth 16x16 Words
  "1503.02531", // Distilling the Knowledge in a Neural Network
  "2001.08361", // Scaling Laws for Neural Language Models
  "1910.10683", // T5
  "1611.03530", // Rethinking Generalization
  "1804.02767", // YOLOv3
];

const CACHE_DIR = fileURLToPath(new URL("./papers/", import.meta.url));

// arXiv asks that you not hammer the e-print endpoint. This downloads each
// paper once, one at a time, and every later run reads the cache. If you want
// thousands of papers, use arXiv's bulk access rather than a loop like this.
const REQUEST_SPACING_MS = 3_000;

export function archivePath(id: string): string {
  return `${CACHE_DIR}${id}.tar.gz`;
}

/** Download whatever is missing from the cache. Silent when there is nothing to do. */
export async function ensureCorpus(ids: string[] = PAPER_IDS): Promise<string[]> {
  await mkdir(CACHE_DIR, { recursive: true });
  let fetched = 0;

  for (const id of ids) {
    const path = archivePath(id);
    try {
      await readFile(path);
      continue;
    } catch {
      // not cached yet
    }
    if (fetched === 0) console.log(`Fetching sources from arXiv into ${CACHE_DIR}`);
    else await new Promise((resolve) => setTimeout(resolve, REQUEST_SPACING_MS));

    const response = await fetch(`https://arxiv.org/e-print/${id}`, {
      headers: { "user-agent": "knitting-docs-example/1.0" },
    });
    if (!response.ok) throw new Error(`arXiv ${id}: HTTP ${response.status}`);
    const bytes = new Uint8Array(await response.arrayBuffer());
    await writeFile(path, bytes);
    fetched++;
    console.log(`  ${id}  ${bytes.byteLength.toLocaleString()} bytes`);
  }

  if (fetched > 0) console.log(`Cached ${fetched} new archives.\n`);
  return ids.map(archivePath);
}

/**
 * Read the .tex entries out of a tar archive.
 *
 * tar is 512-byte header blocks followed by padded contents, which is little
 * enough format to hand-roll rather than take a dependency on for one example.
 */
function untarTexFiles(archive: Uint8Array): Record<string, string> {
  const decoder = new TextDecoder();
  const files: Record<string, string> = {};
  let offset = 0;
  let longName: string | null = null;

  while (offset + 512 <= archive.length) {
    const header = archive.subarray(offset, offset + 512);
    if (header.every((byte) => byte === 0)) break;

    const field = (start: number, length: number) =>
      decoder.decode(header.subarray(start, start + length))
        .replace(/\0.*$/, "").trim();

    const prefix = field(345, 155);
    const rawName = field(0, 100);
    const name = longName ?? (prefix ? `${prefix}/${rawName}` : rawName);
    const size = Number.parseInt(field(124, 12), 8) || 0;
    const type = String.fromCharCode(header[156]!);
    const body = archive.subarray(offset + 512, offset + 512 + size);
    offset += 512 + Math.ceil(size / 512) * 512;

    if (type === "L") {
      // GNU long name: this entry's content is the next header's real name.
      longName = decoder.decode(body).replace(/\0.*$/, "");
      continue;
    }
    longName = null;
    if (type !== "0" && type !== "\0") continue;
    if (!/\.(tex|ltx)$/i.test(name)) continue;
    files[name] = decoder.decode(body);
  }

  return files;
}

/** Read one archive off disk and unpack the .tex files in it. */
export async function loadArchive(path: string): Promise<PaperSource> {
  const id = path.split("/").pop()!.replace(/\.tar\.gz$/, "");
  const archive = await readFile(path);
  // `node:zlib`, not `DecompressionStream`. Both work on all three runtimes and
  // the streaming one looks more idiomatic, but it does not get faster when you
  // add workers -- measured flat from 1 thread to 8. `gunzipSync` runs inside
  // the worker that called it, so it scales with the pool like everything else.
  return { id, files: untarTexFiles(gunzipSync(archive)) };
}

/**
 * Read, unpack and parse one archive, start to finish, inside the worker.
 *
 * This is the shape worth copying. The job crosses the boundary as a path --
 * a few dozen bytes -- rather than as the megabyte of LaTeX inside the archive,
 * and the gunzip goes parallel along with the parsing instead of staying on the
 * host as a serial prelude to it.
 */
export const indexArchive = task<string, PaperRecord>({
  f: async (path: string) => parsePaperHost(await loadArchive(path)),
});
