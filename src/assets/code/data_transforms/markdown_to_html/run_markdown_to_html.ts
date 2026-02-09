import { createPool, isMain } from "@vixeny/knitting";
import { markdownToHtml, markdownToHtmlHost } from "./render_markdown.ts";

function intArg(name: string, fallback: number): number {
  const i = process.argv.indexOf(`--${name}`);
  if (i !== -1 && i + 1 < process.argv.length) {
    const value = Number(process.argv[i + 1]);
    if (Number.isFinite(value) && value > 0) return Math.floor(value);
  }
  return fallback;
}

function strArg(name: string, fallback: string): string {
  const i = process.argv.indexOf(`--${name}`);
  if (i !== -1 && i + 1 < process.argv.length) {
    return String(process.argv[i + 1]);
  }
  return fallback;
}

const THREADS = intArg("threads", 2);
const DOCS = intArg("docs", 25_000);
const MODE = strArg("mode", "knitting");

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
  const n = i.toString(36);

  return [
    `# Job ${n.toUpperCase()}`,
    "",
    `This page documents a ${topicA} pipeline for ${topicB}.`,
    "",
    "## Checklist",
    "",
    `- Parse input payload ${n}`,
    `- Validate required fields and defaults`,
    `- Render output and track bytes (${topicC})`,
    "",
    "## Sample code",
    "",
    "```ts",
    `const jobId = "${n}";`,
    "const status = \"ready\";",
    "```",
    "",
    `Generated at 2026-01-${String((i % 27) + 1).padStart(2, "0")}.`,
  ].join("\n");
}

type Totals = {
  bytes: number;
  headings: number;
  words: number;
};

function mergeTotals(current: Totals, next: Totals): Totals {
  return {
    bytes: current.bytes + next.bytes,
    headings: current.headings + next.headings,
    words: current.words + next.words,
  };
}

function runHost(markdowns: string[]): Totals {
  let totals: Totals = { bytes: 0, headings: 0, words: 0 };
  for (let i = 0; i < markdowns.length; i++) {
    const result = markdownToHtmlHost(markdowns[i]!);
    totals = mergeTotals(totals, result);
  }
  return totals;
}

async function runWorkers(markdowns: string[]): Promise<Totals> {
  const pool = createPool({ threads: THREADS })({ markdownToHtml });

  try {
    const jobs: ReturnType<typeof pool.call.markdownToHtml>[] = [];
    for (let i = 0; i < markdowns.length; i++) {
      jobs.push(pool.call.markdownToHtml(markdowns[i]!));
    }

    const results = await Promise.all(jobs);

    let totals: Totals = { bytes: 0, headings: 0, words: 0 };
    for (const result of results) totals = mergeTotals(totals, result);
    return totals;
  } finally {
    pool.shutdown();
  }
}

async function main() {
  const markdowns = new Array<string>(DOCS);
  for (let i = 0; i < DOCS; i++) markdowns[i] = makeMarkdown(i);

  const started = performance.now();
  const totals = MODE === "host"
    ? runHost(markdowns)
    : await runWorkers(markdowns);
  const finished = performance.now();

  const tookMs = finished - started;
  const secs = Math.max(1e-9, tookMs / 1000);
  const docsPerSec = DOCS / secs;

  console.log("Markdown -> HTML transform");
  console.log("mode        :", MODE);
  console.log("threads     :", MODE === "host" ? 0 : THREADS);
  console.log("documents   :", DOCS.toLocaleString());
  console.log("html bytes  :", totals.bytes.toLocaleString());
  console.log("headings    :", totals.headings.toLocaleString());
  console.log("words       :", totals.words.toLocaleString());
  console.log("took        :", tookMs.toFixed(2), "ms");
  console.log("throughput  :", docsPerSec.toFixed(0), "docs/s");
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
