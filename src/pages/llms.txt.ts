import type { APIRoute } from "astro";
import {
  docUrl,
  ESSENTIALS,
  fileUrl,
  groupDocs,
  loadDocs,
  TAGLINE,
  TITLE,
} from "../lib/llms";

export const prerender = true;

export const GET: APIRoute = async ({ site }) => {
  const groups = groupDocs(await loadDocs());

  const lines: string[] = [
    `# ${TITLE}`,
    "",
    `> ${TAGLINE}`,
    "",
    `**Building with Knitting? Fetch [llms-full.txt](${
      fileUrl("llms-full.txt", site)
    }) first** — it inlines every documentation page into one file. The essentials below cover the common path; the full text covers everything else.`,
    "",
    ESSENTIALS,
    "",
  ];

  for (const group of groups) {
    lines.push(`## ${group.label}`, "");
    for (const d of group.docs) {
      const desc = String(d.data.description ?? "").trim();
      lines.push(
        `- [${d.data.title}](${docUrl(d.id, site)})${desc ? `: ${desc}` : ""}`,
      );
    }
    lines.push("");
  }

  lines.push(
    "## Full text",
    "",
    `- [llms-full.txt](${
      fileUrl("llms-full.txt", site)
    }): every documentation page inlined into one file.`,
    "",
  );

  return new Response(lines.join("\n"), {
    headers: { "content-type": "text/plain; charset=utf-8" },
  });
};
