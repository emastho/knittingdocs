import type { APIRoute } from "astro";
import {
  cleanBody,
  docUrl,
  ESSENTIALS,
  groupDocs,
  loadDocs,
  rawBodyFor,
  TAGLINE,
  TITLE,
} from "../lib/llms";

export const prerender = true;

export const GET: APIRoute = async ({ site }) => {
  const groups = groupDocs(await loadDocs());

  const parts: string[] = [
    `# ${TITLE} — full documentation`,
    "",
    `> ${TAGLINE}`,
    "",
    ESSENTIALS,
  ];

  for (const group of groups) {
    for (const d of group.docs) {
      const body = cleanBody(rawBodyFor(d.id));
      if (!body) continue;
      const desc = String(d.data.description ?? "").trim();
      parts.push(
        "",
        "---",
        "",
        `# ${d.data.title}`,
        `URL: ${docUrl(d.id, site)}`,
        desc ? `\n${desc}` : "",
        "",
        body,
      );
    }
  }

  return new Response(parts.join("\n"), {
    headers: { "content-type": "text/plain; charset=utf-8" },
  });
};
