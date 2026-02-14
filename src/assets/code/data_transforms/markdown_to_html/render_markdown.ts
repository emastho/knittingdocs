import { task } from "@vixeny/knitting";
import { marked } from "marked";

marked.setOptions({
  gfm: true,
});

export function markdownToHtmlHost(markdown: string): string {
  return marked.parse(markdown) as string;
}

export const markdownToHtml = task<string, string>({
  f: marked.parse,
});
