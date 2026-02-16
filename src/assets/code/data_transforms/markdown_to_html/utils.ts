import { task } from "@vixeny/knitting";
import { marked } from "marked";
import { brotliCompressSync } from "node:zlib";

marked.setOptions({
  gfm: true,
});

export function markdownToHtmlHost(markdown: string): string {
  return marked.parse(markdown) as string;
}

export const markdownToHtml = task<string, string>({
  f: markdownToHtmlHost,
});

export function markdownToHtmlCompressedHost(markdown: string) {
  const html = markdownToHtmlHost(markdown);
  return brotliCompressSync(html);
}

export const markdownToHtmlCompressed = task<string, Buffer>({
  f: markdownToHtmlCompressedHost,
});

export const TOPICS = [
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

export function makeMarkdown(i: number): string {
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
    'const status = "ready";',
    "```",
    "",
    `Generated at 2026-01-${String((i % 27) + 1).padStart(2, "0")}.`,
  ].join("\n");
}

export function buildMarkdownDocs(count: number): string[] {
  const docs = new Array<string>(count);
  for (let i = 0; i < count; i++) docs[i] = makeMarkdown(i);
  return docs;
}

export function sumChunkBytes(
  chunks: ArrayLike<{ byteLength: number }>,
): number {
  let total = 0;
  for (let i = 0; i < chunks.length; i++) {
    total += chunks[i]!.byteLength;
  }
  return total;
}
