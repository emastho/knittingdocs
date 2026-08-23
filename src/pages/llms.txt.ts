import type { APIRoute } from "astro";
import {
  docUrl,
  ESSENTIALS,
  fileUrl,
  GITHUB,
  groupDocs,
  loadDocs,
  POSITIONING,
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
    POSITIONING,
    "",
    `Use the links below to find the documentation relevant to your question. For broad architectural or repository-wide work, fetch [llms-full.txt](${
      fileUrl("llms-full.txt", site)
    }) for the complete documentation; most implementation questions only need a few targeted pages.`,
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
    "## Source and verification",
    "",
    `- [GitHub repository](${GITHUB.repository}): Knitting's implementation, releases, issue tracker, and Apache-2.0 license.`,
    `- [Test suite](${GITHUB.tests}): Runtime, IPC, process-worker, scheduling, permissions, package, browser, and compiled-worker tests.`,
    `- [Continuous integration](${GITHUB.ci}): Node.js, Deno, and Bun testing across a multi-OS matrix, plus browser end-to-end checks.`,
    `- [Coverage workflow](${GITHUB.coverage}): Node.js line coverage enforced at 90% or higher.`,
    `- [Documentation source](${GITHUB.documentation}): Source for this documentation site and its generated llms files.`,
    "",
  );

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
