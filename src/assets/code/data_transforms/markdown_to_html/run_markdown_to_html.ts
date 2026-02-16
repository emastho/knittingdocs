import { createPool, isMain } from "@vixeny/knitting";
import { markdownToHtml, markdownToHtmlHost } from "./utils.ts";

function intArg(name: string, fallback: number): number {
  const i = process.argv.indexOf(`--${name}`);
  if (i !== -1 && i + 1 < process.argv.length) {
    const value = Number(process.argv[i + 1]);
    if (Number.isFinite(value) && value > 0) return Math.floor(value);
  }
  return fallback;
}

const THREADS = intArg("threads", 2);

const SAMPLE_MARKDOWN = [
  "# Knitting markdown example",
  "",
  "This example renders markdown on the host and in a worker.",
  "",
  "## Checklist",
  "",
  "- Parse markdown",
  "- Render HTML",
  "- Compare outputs",
  "",
  "```ts",
  "const status = 'ready';",
  "```",
].join("\n");

async function main() {
  const hostHtml = markdownToHtmlHost(SAMPLE_MARKDOWN);
  const pool = createPool({ threads: THREADS })({ markdownToHtml });

  try {
    const workerHtml = await pool.call.markdownToHtml(SAMPLE_MARKDOWN);

    console.log("Markdown -> HTML example");
    console.log("threads      :", THREADS);
    console.log("same html    :", hostHtml === workerHtml);
    console.log("html length  :", workerHtml.length);
    console.log("html preview :", workerHtml.slice(0, 120), "...");
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
