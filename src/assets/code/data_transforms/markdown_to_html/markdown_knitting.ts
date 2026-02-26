import { createPool, isMain } from "@vixeny/knitting";
import {
  buildMarkdownDocs,
  markdownToHtmlCompressed,
  markdownToHtmlCompressedHost,
  sumChunkBytes,
} from "./utils.ts";

const THREADS = 2;
const DOCS = 100;

function runHost(markdowns: string[]): { ms: number; bytes: number } {
  const started = performance.now();
  let bytes = 0;
  for (let i = 0; i < markdowns.length; i++) {
    bytes += markdownToHtmlCompressedHost(markdowns[i]!).byteLength;
  }
  return { ms: performance.now() - started, bytes };
}

async function runWorkers(
  markdowns: string[],
): Promise<{ ms: number; bytes: number }> {
  const pool = createPool({ threads: THREADS })({ markdownToHtmlCompressed });

  try {
    const started = performance.now();
    const jobs: ReturnType<typeof pool.call.markdownToHtmlCompressed>[] = [];
    for (let i = 0; i < markdowns.length; i++) {
      jobs.push(pool.call.markdownToHtmlCompressed(markdowns[i]!));
    }

    const chunks = await Promise.all(jobs);
    return { ms: performance.now() - started, bytes: sumChunkBytes(chunks) };
  } finally {
    pool.shutdown();
  }
}

function printMetrics(mode: string, ms: number, bytes: number): void {
  const secs = Math.max(1e-9, ms / 1000);
  const dps = DOCS / secs;
  console.log(mode);
  console.log("docs        :", DOCS.toLocaleString());
  console.log("bytes       :", bytes.toLocaleString());
  console.log("took        :", `${ms.toFixed(2)} ms`);
  console.log("throughput  :", `${dps.toFixed(0)} docs/s`);
}

async function main() {
  const markdowns = buildMarkdownDocs(DOCS);
  const host = runHost(markdowns);
  const knitting = await runWorkers(markdowns);
  const uplift = (host.ms / Math.max(1e-9, knitting.ms) - 1) * 100;

  console.log("Markdown -> HTML + brotli quick run");
  console.log(`threads: ${THREADS}`);
  console.log("");
  printMetrics("host", host.ms, host.bytes);
  console.log("");
  printMetrics("knitting", knitting.ms, knitting.bytes);
  console.log("");
  console.log(`uplift: ${uplift.toFixed(1)}%`);
  console.log(`byte parity: ${host.bytes === knitting.bytes}`);
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
