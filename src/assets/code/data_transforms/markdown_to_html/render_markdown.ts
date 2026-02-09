import { task } from "@vixeny/knitting";
import { marked } from "marked";

type RenderResult = {
  html: string;
  bytes: number;
  headings: number;
  words: number;
};

const encoder = new TextEncoder();

function countHeadings(markdown: string): number {
  const matches = markdown.match(/^#{1,6}\s+/gm);
  return matches ? matches.length : 0;
}

function countWords(markdown: string): number {
  const normalized = markdown.replace(/\s+/g, " ").trim();
  if (normalized.length === 0) return 0;
  return normalized.split(" ").length;
}

marked.setOptions({
  gfm: true,
});

export function markdownToHtmlHost(markdown: string): RenderResult {
  const html = marked.parse(markdown) as string;

  return {
    html,
    bytes: encoder.encode(html).length,
    headings: countHeadings(markdown),
    words: countWords(markdown),
  };
}

export const markdownToHtml = task<string, RenderResult>({
  f: (markdown) => markdownToHtmlHost(markdown),
});
