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

export function markdownToHtmlCompressedHost(markdown: string): Uint8Array {
  const html = markdownToHtmlHost(markdown);
  return brotliCompressSync(html);
}

export const markdownToHtmlCompressed = task<string, Uint8Array>({
  f: markdownToHtmlCompressedHost,
});
