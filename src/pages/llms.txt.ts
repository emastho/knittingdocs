import type { APIRoute } from "astro";
import {
  COMPATIBILITY, docUrl, fileUrl, GITHUB, IMPLEMENTATION_CONTRACT,
  loadDocs, markdownUrl, TAGLINE, TITLE,
} from "../lib/llms";

export const prerender = true;

export const GET: APIRoute = async ({ site }) => {
  const docs = await loadDocs();
  const byId = new Map(docs.map((d) => [d.id.toLowerCase(), d]));
  const link = (id: string, anchor = "") => {
    const doc = byId.get(id.toLowerCase());
    if (!doc) throw new Error(`Unknown llms navigation target: ${id}`);
    return `[${doc.data.title}](${docUrl(doc.id, site)}${anchor})`;
  };
  const lines = [
    `# ${TITLE}`, "", `> ${TAGLINE}`, "",
    "Move CPU-heavy work off the main thread while minimizing coordination, waiting, and copying overhead. The goal is performance isolation without spending the capacity that isolation is meant to recover.",
    "", COMPATIBILITY, "",
    "## Start here", "",
    ...["start/installation", "start/quick-start", "guides/defining-tasks", "guides/creating-pools"].map((id) => `- ${link(id)}`),
    "", IMPLEMENTATION_CONTRACT, "",
    "## Find documentation by task", "",
    "For an implementation, use the minimal example and fetch only the guides needed. For debugging or optimization, read the relevant guide and inspect its implementation and tests before proposing changes. Do not invent undocumented options or runtime behavior.",
    "",
    `- Add Knitting or replace Piscina: ${link("start/quick-start")}, ${link("guides/defining-tasks")}, ${link("guides/creating-pools")}, ${link("guides/payloads")}.`,
    `- Parallelize an HTTP route or SSR: ${link("examples/servers/hono_server")}, ${link("examples/rendering/react_ssr")}, ${link("guides/multi-threading")}.`,
    `- Move large binary payloads: ${link("guides/payloads")}, ${link("guides/shared-memory")}, ${link("guides/buffer-reference")}. Moved, borrowed, and shared bytes have different ownership and lifetimes; choose by thread/process boundary.`,
    `- Isolate untrusted work: ${link("guides/process-workers")}, ${link("guides/permissions")}. Use an OS sandbox or container; importTask and runtime permissions alone are not a security boundary.`,
    `- Diagnose hangs or rejected calls: ${link("guides/defining-tasks")}, ${link("guides/creating-pools", "#debug")}. Check exports/imports/startup first, then payload limits and permissions; preserve error causes.`,
    `- Handle cancellation, timeouts, or failures: ${link("guides/defining-tasks")}, ${link("guides/creating-pools")}. The task abort toolkit is not a DOM AbortSignal; a fatal shared-queue failure requires replacing the pool.`,
    `- Improve p99 or tune scheduling: ${link("guides/multi-threading")}, ${link("guides/performance")}, ${link("guides/work-stealing")}. Measure before overriding defaults.`,
    `- Use browser workers: ${link("guides/browser")}. Requires cross-origin isolation and task module discovery setup; runtime restrictions differ from server workers.`,
    `- Investigate the protocol: ${link("extras/architecture")}, ${link("guides/work-stealing")}, [runtime source](${GITHUB.repository}), [tests](${GITHUB.tests}).`,
    "",
    "## Documentation index", "",
    "Each page has a Markdown version with code and tables inlined. Fetch the individual Markdown resources for focused context; reserve the full reference for broad investigations.", "",
  ];
  const listed = new Set<string>();
  const section = (label: string, ids: string[]) => {
    const entries = ids.map((id) => {
      const d = byId.get(id.toLowerCase());
      if (!d) throw new Error(`Unknown llms index target: ${id}`);
      listed.add(d.id);
      return `- ${link(d.id)} ([Markdown](${markdownUrl(d.id, site)})): ${String(d.data.description ?? "").trim()}`;
    });
    if (entries.length) lines.push(`### ${label}`, "", ...entries, "");
  };
  section("Implement a worker pool", ["start/installation", "start/quick-start", "guides/defining-tasks", "guides/creating-pools", "guides/payloads"]);
  section("Memory and data transfer", ["guides/shared-memory", "guides/buffer-reference", "guides/utils"]);
  section("Control worker behavior", ["guides/multi-threading", "guides/performance", "guides/work-stealing", "guides/inliner"]);
  section("Isolation and runtime support", ["guides/permissions", "guides/process-workers", "guides/browser"]);
  for (const [dir, label] of [
    ["servers", "HTTP servers"], ["rendering", "SSR, documents, and compression"],
    ["validation", "Validation and cryptography"], ["build_tools", "Build tools"],
    ["text", "Text processing"], ["maths", "Math and simulation"],
  ]) {
    section(`Examples: ${label}`, docs.filter((d) => d.id.startsWith(`examples/${dir}/`)).map((d) => d.id).sort());
  }
  section("Example setup", ["examples/intro_examples"]);
  section("Runtime internals and performance evidence", ["extras/architecture", "extras/why", ...docs.filter((d) => d.id.startsWith("benchmarks/")).map((d) => d.id).sort()]);
  lines.push("## Source and verification", "",
    `- [Runtime source](${GITHUB.repository}): Implementation, releases, and Apache-2.0 license; main may differ from the installed release.`,
    `- [Tests](${GITHUB.tests}) and [CI](${GITHUB.ci}): Inspect the run for the relevant commit for results and skips.`,
    `- [Coverage workflow](${GITHUB.coverage}): Configured 90% Node line-coverage gate, not a claim about measured coverage.`,
    `- [Documentation source](${GITHUB.documentation}): Sources and generated agent resources.`, "");
  lines.push("## Optional", "", "Experimental and specialized features require their own runtime setup and compatibility checks.", "");
  section("Experimental runtimes and specialized workers", ["guides/andromeda", "guides/compiled-workers"]);
  // New maintained pages remain discoverable until explicitly categorized.
  section("Additional documentation", docs.filter((d) => !listed.has(d.id)).map((d) => d.id).sort());
  lines.push(`- [llms-full.txt](${fileUrl("llms-full.txt", site)}): Comprehensive reference for architectural investigations, multi-subsystem migrations, and repository-wide audits; fetch alongside the relevant runtime source.`, "");
  return new Response(lines.join("\n"), {
    headers: { "content-type": "text/plain; charset=utf-8" },
  });
};
