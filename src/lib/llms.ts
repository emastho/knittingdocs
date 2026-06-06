import { getCollection, type CollectionEntry } from "astro:content";

type Doc = CollectionEntry<"docs">;

export const TITLE = "Knitting";

export const TAGLINE =
  "Knitting is a zero-dependency worker pool over a shared-memory IPC runtime for Node.js, Deno, and Bun. Export a function, create a pool, and call it like a normal async function — on real threads or isolated processes.";

// A small, hand-maintained cheat sheet of the things an AI most often gets
// wrong about Knitting. The page listings below are generated from the docs,
// but this block is the high-value, stable summary.
export const ESSENTIALS = [
  "## Essentials (read this first)",
  "",
  "- Install: `npm install knitting` (the npm package is `knitting`; it is also on JSR as `@vixeny/knitting`). Requires Node 22+, Deno 2+, or Bun 1+.",
  "- A task is an exported function at module scope. Wrap it with `task({ f })` only when you want options like a timeout or an abort signal.",
  "- Tasks take ONE argument. Use a tuple or object for multiple values: `([a, b]) => a + b`.",
  "- Guard host-only code with `isMain` — workers re-import the module.",
  "- Module loading: each worker re-imports the module that DEFINES your tasks, and its top-level `import`s run in every worker (they are hoisted — `isMain` does NOT gate them). Keep tasks in a lean module separate from your server/framework code. Tasks must be `export`ed or the loader can't find them and the call silently hangs. `importTask` targets must be plain functions, not `task()` wrappers.",
  "- Create a pool with `createPool(options)({ taskA, taskB })`, then call `await pool.call.taskA(args)`.",
  "- Cleanup: `using pool = createPool(...)` disposes the pool at scope exit. `await pool.shutdown()` still exists to close it earlier or to await teardown.",
  '- Isolation: `importTask({ href, name })` keeps a task\'s code off the host (only the worker imports it). Set `worker.runtime: "process"` to run each worker as a separate process — including inside a bwrap sandbox or a container.',
  "- Security: for untrusted or security-sensitive code, define the task with `importTask`. The host holds only a typed wrapper and never imports or evaluates the module, so that code runs only in the worker (under its permissions), never at host scope.",
  "- Zero-copy IN: `ProcessSharedBuffer` (`knitting/process-shared-buffer`) shares bytes across processes; `SharedArrayBuffer` and `BufferReference` (`knitting/unsafe`) move bytes to thread workers without copying. Pick by boundary — process vs thread.",
  "- Zero-copy OUT (good practice): for large binary results from a thread worker, RETURN a `BufferReference` so bytes move back instead of being copied through the transport. `knitting/utils` converts string/JSON/number ↔ `SharedArrayBuffer`.",
  "- Optimized for HTTP: `call.*()` accepts `Promise<supported>` inputs, so forward `request.arrayBuffer()` (e.g. Hono `c.req.arrayBuffer()`) straight into a task without awaiting it on the request thread — UTF-8 decode / JSON parse then happens in the worker. Ideal for SSR, JWT, and upload routes.",
  "- Workers are quiet and contained by default: in strict mode (the default) worker `console.*` does NOT reach the host — set `permission: { console: true }` to surface it. Task code cannot take the host down: `process.exit`, `process.kill`, `process.abort`, and `Deno.exit` are blocked.",
  "- Payload size: dynamic payloads are hard-capped at ~8 MiB by default (over-cap calls reject with `KNT_ERROR_3`). Raise it with `payload: { maxPayloadBytes, payloadMaxByteLength }` — `maxPayloadBytes` must be `<= payloadMaxByteLength >> 3`; the buffer growth cap defaults to 64 MiB.",
  "- Cancellation & timeouts: `task({ f, timeout: { time: 100 } })` bounds a call, `task({ f, abortSignal: true })` injects an `AbortSignal`, and `worker.hardTimeoutMs` is a hard wall-clock kill for runaway CPU.",
  "- Errors are real: thrown errors and rejected promises return to the host as `Error` objects with `name`, `message`, `stack`, and the full `cause` chain.",
  "",
  "```ts",
  'import { createPool, isMain } from "knitting";',
  "",
  "export const square = (n: number) => n * n;",
  "export const greet = (name: string) => `hello ${name}`;",
  "",
  "if (isMain) {",
  "  // `using` shuts the pool down when this block ends.",
  "  using pool = createPool({ threads: 2 })({ square, greet });",
  "",
  "  const [n, msg] = await Promise.all([",
  "    pool.call.square(8),",
  '    pool.call.greet("knitting"),',
  "  ]);",
  '  console.log({ n, msg }); // { n: 64, msg: "hello knitting" }',
  "}",
  "```",
].join("\n");

const SECTIONS: ReadonlyArray<{ dir: string; label: string }> = [
  { dir: "start", label: "Getting Started" },
  { dir: "guides", label: "Guides" },
  { dir: "examples", label: "Examples" },
  { dir: "benchmarks", label: "Benchmarks" },
  { dir: "extras", label: "Extras" },
];

const orderOf = (d: Doc): number => {
  const order = (d.data as { sidebar?: { order?: number } }).sidebar?.order;
  return typeof order === "number" ? order : 999;
};

// llms.txt / llms-full.txt mirror the sidebar: only pages under a navbar
// section directory are part of the guided, maintained docs. This drops the
// splash home page and any off-navbar top-level pages (e.g. browser.mdx,
// license.md) so stale or out-of-band content never leaks into the llms files.
const SECTION_DIRS = new Set(SECTIONS.map((s) => s.dir));

export async function loadDocs(): Promise<Doc[]> {
  const docs = await getCollection("docs");
  return docs.filter((d) => SECTION_DIRS.has(d.id.split("/")[0]));
}

export function groupDocs(docs: Doc[]): Array<{ label: string; docs: Doc[] }> {
  const buckets = new Map<string, Doc[]>();
  for (const s of SECTIONS) buckets.set(s.label, []);
  buckets.set("Other", []);

  for (const d of docs) {
    const seg = d.id.split("/")[0];
    const section = SECTIONS.find((s) => s.dir === seg);
    buckets.get(section ? section.label : "Other")!.push(d);
  }

  const groups: Array<{ label: string; docs: Doc[] }> = [];
  for (const [label, arr] of buckets) {
    if (arr.length === 0) continue;
    arr.sort((a, b) =>
      orderOf(a) - orderOf(b) || a.data.title.localeCompare(b.data.title)
    );
    groups.push({ label, docs: arr });
  }
  return groups;
}

export function docUrl(id: string, site?: URL): string {
  return fileUrl(id.toLowerCase() + "/", site);
}

export function fileUrl(name: string, site?: URL): string {
  const base = import.meta.env.BASE_URL || "/";
  const path = (base + "/" + name).replace(/\/{2,}/g, "/");
  return site ? new URL(path, site).href : path;
}

// Raw doc sources, used so the full text reflects exactly what's in the repo.
const rawDocs = import.meta.glob("/src/content/docs/**/*.{md,mdx}", {
  query: "?raw",
  eager: true,
  import: "default",
}) as Record<string, string>;

const rawById = new Map<string, string>();
for (const [path, src] of Object.entries(rawDocs)) {
  const id = path
    .replace(/^\/src\/content\/docs\//, "")
    .replace(/\.(md|mdx)$/, "");
  const body = stripFrontmatter(src);
  rawById.set(id, body);
  rawById.set(id.toLowerCase(), body);
}

export function rawBodyFor(id: string): string {
  return rawById.get(id) ?? rawById.get(id.toLowerCase()) ?? "";
}

function stripFrontmatter(src: string): string {
  const match = src.match(/^\uFEFF?---\r?\n[\s\S]*?\r?\n---\r?\n?/);
  return match ? src.slice(match[0].length) : src;
}

// Code snippets pulled in via getCode(), so we can inline them into the full text.
const rawCode = import.meta.glob("/src/assets/code/**/*", {
  query: "?raw",
  eager: true,
  import: "default",
}) as Record<string, string>;

function codeFor(path: string): string | undefined {
  const trimmed = path
    .replace(/^[./]+/, "")
    .replace(/^src\/assets\/code\//, "");
  return rawCode["/src/assets/code/" + trimmed];
}

const CODE_SENTINEL = "\u0000";

// Turn an MDX doc body into plain markdown: drop imports, inline getCode()
// snippets in place of <Code/> components, and strip the structural JSX
// (Tabs, Steps, Badge, custom components) while leaving fenced code untouched.
export function cleanBody(body: string): string {
  const codeMap = new Map<string, string>();
  let fence = false;
  for (const line of body.split("\n")) {
    if (/^\s*```/.test(line)) {
      fence = !fence;
      continue;
    }
    if (fence) continue;
    const m = line.match(
      /export const (\w+)\s*=\s*getCode\(\s*['"]([^'"]+)['"]\s*\)/,
    );
    if (m) codeMap.set(m[1], m[2]);
  }

  const out: string[] = [];
  let prose: string[] = [];
  fence = false;

  const flush = () => {
    if (prose.length === 0) return;
    let text = prose.join("\n");
    text = text.replace(/^import\s.+from\s+['"][^'"]+['"];?\s*$/gm, "");
    text = text.replace(/^export const \w+\s*=\s*getCode\([^)]*\);?\s*$/gm, "");

    // Inline <Code code={name} /> as a fenced block, protected by a sentinel
    // (a null char that can't occur in markdown) so the JSX-stripping below
    // can't touch the inlined source.
    const blocks: string[] = [];
    text = text.replace(
      /<Code\b[^>]*?\bcode=\{(\w+)\}[^>]*?\/>/g,
      (full, name) => {
        const path = codeMap.get(name);
        const code = path ? codeFor(path) : undefined;
        if (!code) return "";
        const lang = /\blang="([\w-]+)"/.exec(full)?.[1] ?? "ts";
        blocks.push("\n```" + lang + "\n" + code.trim() + "\n```\n");
        return CODE_SENTINEL + (blocks.length - 1) + CODE_SENTINEL;
      },
    );

    text = cleanMdx(text);
    text = text.replace(
      /\u0000(\d+)\u0000/g,
      (_, i) => blocks[Number(i)] ?? "",
    );

    out.push(text);
    prose = [];
  };

  for (const line of body.split("\n")) {
    if (/^\s*```/.test(line)) {
      if (!fence) {
        flush();
        fence = true;
        out.push(line);
      } else {
        fence = false;
        out.push(line);
      }
      continue;
    }
    if (fence) out.push(line);
    else prose.push(line);
  }
  flush();

  return out.join("\n").replace(/\n{3,}/g, "\n\n").trim();
}

function cleanMdx(text: string): string {
  text = text.replace(
    /<Badge\b[^>]*\btext=(?:"([^"]*)"|'([^']*)'|\{["']([^"']*)["']\})[^>]*\/>/g,
    (_, doubleQuoted, singleQuoted, braced) =>
      doubleQuoted ?? singleQuoted ?? braced ?? "",
  );
  text = htmlTablesToMarkdown(text);
  text = text.replace(/<[A-Z][A-Za-z0-9.]*\b[\s\S]*?\/>/g, "");
  text = text.replace(/<\/?[A-Z][A-Za-z0-9.]*\b[^>]*>/g, "");
  text = text.replace(/<br\s*\/?><\/br>/gi, "\n");
  text = text.replace(/<br\s*\/?>/gi, "\n");
  text = text.replace(/<img\b[^>]*>/gi, "");
  text = text.replace(
    /<a\b[^>]*\bhref=["']([^"']+)["'][^>]*>([\s\S]*?)<\/a>/gi,
    (_, href: string, label: string) => `[${cleanInlineHtml(label)}](${href})`,
  );
  text = text.replace(
    /<\/?(?:div|section|article|span|p|main|header|footer)\b[^>]*>/gi,
    "",
  );
  text = text.replace(
    /^:{3,4}(\w+)[^\n]*\n([\s\S]*?)^:{3,4}\s*$/gm,
    (_, kind: string, content: string) => {
      const body = content.trim();
      if (!body) return "";
      const label = calloutLabel(kind);
      const lines = body.split("\n");
      return lines
        .map((line, index) =>
          index === 0 ? `> ${label}: ${line}` : line ? `> ${line}` : ">"
        )
        .join("\n");
    },
  );
  return text;
}

function cleanInlineHtml(text: string): string {
  return text
    .replace(/<code\b[^>]*>([\s\S]*?)<\/code>/gi, "`$1`")
    .replace(/<[^>]+>/g, "")
    .replace(/\s+/g, " ")
    .trim();
}

function calloutLabel(kind: string): string {
  switch (kind.toLowerCase()) {
    case "caution":
      return "Caution";
    case "danger":
      return "Danger";
    case "info":
      return "Info";
    case "note":
      return "Note";
    case "tip":
      return "Tip";
    case "warning":
      return "Warning";
    default:
      return kind;
  }
}

function htmlTablesToMarkdown(text: string): string {
  return text.replace(/<table\b[^>]*>\s*([\s\S]*?)<\/table>/gi, (_, table) => {
    const rows = [...table.matchAll(/<tr\b[^>]*>\s*([\s\S]*?)<\/tr>/gi)]
      .map((match) => tableCells(match[1]))
      .filter((cells) => cells.length > 0);

    if (rows.length === 0) return "";

    const header = rows[0];
    const widths = header.length;
    const normalized = rows.map((row) =>
      Array.from({ length: widths }, (_, index) => row[index] ?? "")
    );
    const separator = Array.from({ length: widths }, () => "---");
    return [
      "",
      markdownRow(header),
      markdownRow(separator),
      ...normalized.slice(1).map(markdownRow),
      "",
    ].join("\n");
  });
}

function tableCells(row: string): string[] {
  return [...row.matchAll(/<t[dh]\b[^>]*>([\s\S]*?)<\/t[dh]>/gi)].map(
    (match) => cleanTableCell(match[1]),
  );
}

function cleanTableCell(cell: string): string {
  return cell
    .replace(/<code\b[^>]*>([\s\S]*?)<\/code>/gi, "`$1`")
    .replace(/<[^>]+>/g, "")
    .replace(/\s+/g, " ")
    .replace(/\|/g, "\\|")
    .trim();
}

function markdownRow(cells: string[]): string {
  return `| ${cells.join(" | ")} |`;
}
