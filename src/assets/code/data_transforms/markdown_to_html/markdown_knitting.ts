import { createPool, isMain } from "@vixeny/knitting";
import { markdownToHtml, markdownToHtmlHost } from "./render_markdown.ts";

const THREADS = 2;
const DOCS = 10_000;

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
    `const jobId = "${id}";`,
    'const status = "ready";',
    "```",
    "",
    `Generated at 2026-01-${String((i % 27) + 1).padStart(2, "0")}.`,
  ].join("\n");
}

function buildDocs(): string[] {
  const docs = new Array<string>(DOCS);
  for (let i = 0; i < DOCS; i++) docs[i] = makeMarkdown(i);
  return docs;
}

function runHost(markdowns: string[]): { ms: number; bytes: number } {
  let bytes = 0;
  const started = performance.now();
  for (let i = 0; i < markdowns.length; i++) {
    const html = markdownToHtmlHost(markdowns[i]!);
    bytes += html.length;
  }
  return { ms: performance.now() - started, bytes };
}

async function runWorkers(
  markdowns: string[],
): Promise<{ ms: number; bytes: number }> {
  const pool = createPool({ threads: THREADS })({ markdownToHtml });
  let bytes = 0;

  try {
    const started = performance.now();
    const jobs: ReturnType<typeof pool.call.markdownToHtml>[] = [];
    for (let i = 0; i < markdowns.length; i++) {
      jobs.push(pool.call.markdownToHtml(markdowns[i]!));
    }

    const htmls = await Promise.all(jobs);
    for (let i = 0; i < htmls.length; i++) {
      bytes += htmls[i]!.length;
    }
    return { ms: performance.now() - started, bytes };
  } finally {
    pool.shutdown();
  }
}

function printMetrics(mode: string, ms: number, bytes: number): void {
  const secs = Math.max(1e-9, ms / 1000);
  const dps = DOCS / secs;
  console.log(mode);
  console.log("docs        :", DOCS.toLocaleString());
  console.log("html bytes  :", bytes.toLocaleString());
  console.log("took        :", `${ms.toFixed(2)} ms`);
  console.log("throughput  :", `${dps.toFixed(0)} docs/s`);
}

async function main() {
  const markdowns = buildDocs();
  const host = runHost(markdowns);
  const knitting = await runWorkers(markdowns);
  const uplift = (host.ms / Math.max(1e-9, knitting.ms) - 1) * 100;

  console.log("Markdown -> HTML quick run");
  console.log(`threads: ${THREADS}`);
  console.log("");
  printMetrics("host", host.ms, host.bytes);
  console.log("");
  printMetrics("knitting", knitting.ms, knitting.bytes);
  console.log("");
  console.log(`uplift: ${uplift.toFixed(1)}%`);
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
