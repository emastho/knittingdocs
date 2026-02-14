import { createPool, isMain, task } from "@vixeny/knitting";
import { brotliCompressSync } from "node:zlib";
import { markdownToHtmlHost } from "./render_markdown.ts";

const THREADS = 2;
const DOCS = 2_000;

const TOPICS = [
  "workers",
  "schema",
  "compression",
  "batching",
  "latency",
  "rendering",
  "validation",
  "throughput",
];

function pick<T>(arr: T[], i: number): T {
  return arr[i % arr.length]!;
}

function makeMarkdown(i: number): string {
  const topicA = pick(TOPICS, i);
  const topicB = pick(TOPICS, i + 3);
  const topicC = pick(TOPICS, i + 5);
  const id = i.toString(36);

  return [
    `# Job ${id.toUpperCase()}`,
    "",
    `This page documents a ${topicA} pipeline for ${topicB}.`,
    "",
    "## Checklist",
    "",
    `- Parse input payload ${id}`,
    "- Validate required fields and defaults",
    `- Render output for ${topicC}`,
    "",
    "## Sample code",
    "",
    "```ts",
    `const jobId = \"${id}\";`,
    "const status = \"ready\";",
    "```",
    "",
    `Generated at 2026-01-${String((i % 27) + 1).padStart(2, "0")}.`,
  ].join("\n");
}

function renderHeavy(markdown: string): Uint8Array {
  const html = markdownToHtmlHost(markdown);
  return brotliCompressSync(html);
}

export const markdownToHtmlHeavy = task<string, Uint8Array>({
  f: (markdown) => renderHeavy(markdown),
});

function buildDocs(): string[] {
  const markdowns = new Array<string>(DOCS);
  for (let i = 0; i < DOCS; i++) markdowns[i] = makeMarkdown(i);
  return markdowns;
}

function runHost(markdowns: string[]): { ms: number; chunks: Uint8Array[] } {
  const outputs = new Array<Uint8Array>(markdowns.length);
  const started = performance.now();
  for (let i = 0; i < markdowns.length; i++) {
    outputs[i] = renderHeavy(markdowns[i]!);
  }
  return { ms: performance.now() - started, chunks: outputs };
}

async function runWorkers(
  callMarkdown: (markdown: string) => Promise<Uint8Array>,
  markdowns: string[],
): Promise<{ ms: number; chunks: Uint8Array[] }> {
  const jobs: Promise<Uint8Array>[] = [];
  const started = performance.now();
  for (let i = 0; i < markdowns.length; i++) {
    jobs.push(callMarkdown(markdowns[i]!));
  }
  const chunks = await Promise.all(jobs);
  return { ms: performance.now() - started, chunks };
}

function sumBytes(chunks: Uint8Array[]): number {
  let total = 0;
  for (let i = 0; i < chunks.length; i++) {
    total += chunks[i]!.length;
  }
  return total;
}

function sameChunks(a: Uint8Array[], b: Uint8Array[]): boolean {
  if (a.length !== b.length) return false;

  for (let i = 0; i < a.length; i++) {
    const left = a[i]!;
    const right = b[i]!;
    if (left.length !== right.length) return false;
    for (let j = 0; j < left.length; j++) {
      if (left[j] !== right[j]) return false;
    }
  }

  return true;
}

function printMetrics(mode: string, ms: number, bytes: number): void {
  const secs = Math.max(1e-9, ms / 1000);
  const dps = DOCS / secs;
  console.log(`${mode} took       : ${ms.toFixed(2)} ms`);
  console.log(`${mode} throughput : ${dps.toFixed(0)} docs/s`);
  console.log(`${mode} bytes      : ${bytes.toLocaleString()}`);
}

async function main() {
  const markdowns = buildDocs();
  const pool = createPool({ threads: THREADS })({ markdownToHtmlHeavy });

  try {
    const host = runHost(markdowns);
    const knitting = await runWorkers(pool.call.markdownToHtmlHeavy, markdowns);

    if (!sameChunks(host.chunks, knitting.chunks)) {
      throw new Error("Host and worker raw bytes differ.");
    }

    const hostBytes = sumBytes(host.chunks);
    const knittingBytes = sumBytes(knitting.chunks);
    const uplift = (host.ms / Math.max(1e-9, knitting.ms) - 1) * 100;

    console.log("Markdown -> HTML quick bench");
    console.log("workload: parse + brotli, return raw compressed bytes");
    console.log("docs:", DOCS.toLocaleString());
    console.log("threads:", THREADS);
    console.log("");
    printMetrics("host", host.ms, hostBytes);
    printMetrics("knitting", knitting.ms, knittingBytes);
    console.log(`uplift         : ${uplift.toFixed(1)}%`);
    console.log(`byte parity    : ${hostBytes === knittingBytes}`);
  } finally {
    pool.shutdown();
  }
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
