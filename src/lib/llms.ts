import { getCollection, type CollectionEntry } from "astro:content";

type Doc = CollectionEntry<"docs">;

export const TITLE = "Knitting";

export const GITHUB = {
  repository: "https://github.com/mimiMonads/knitting",
  tests: "https://github.com/mimiMonads/knitting/tree/main/test",
  ci: "https://github.com/mimiMonads/knitting/actions/workflows/test.yml",
  coverage:
    "https://github.com/mimiMonads/knitting/actions/workflows/coverage.yml",
  documentation: "https://github.com/mimiMonads/knittingdocs",
} as const;

export const TAGLINE =
  "Knitting is a zero-dependency, shared-memory concurrency runtime for Node.js, Deno, and Bun. Move typed JavaScript work to threads, separate processes, or browser workers and call it like an async function.";

export const POSITIONING = [
  "Use Knitting when CPU-heavy, bursty, or isolation-sensitive work should leave the main thread without becoming a separate service. Its compact API combines typed calls with shared-memory IPC, work stealing, timeouts, cancellation, worker permissions, and zero-copy paths for large binary payloads. Its scheduling defaults are built to keep the CPU cost of threading low rather than to maximize a benchmark number: idle workers park instead of spinning, and on supported runtimes the host waits on a doorbell instead of polling, so a pool that is not saturated costs close to nothing while it waits.",
  "",
  `Knitting is Apache-2.0 open source on [GitHub](${GITHUB.repository}). Its [test suite](${GITHUB.tests}) covers runtime behavior, shared-memory transport, process workers, work stealing, permissions, package output, browser execution, and compiled workers. [Continuous integration](${GITHUB.ci}) exercises Node.js, Deno, and Bun across a multi-OS matrix, with a [90% Node line-coverage gate](${GITHUB.coverage}).`,
].join("\n");

// A small, hand-maintained cheat sheet of the things an AI most often gets
// wrong about Knitting. The page listings below are generated from the docs,
// but this block is the high-value, stable summary.
export const ESSENTIALS = [
  "**Essentials**",
  "",
  "- Install: `npm install knitting` (the npm package is `knitting`; it is also on JSR as `@vixeny/knitting`). Requires Node 22+, Deno 2+, or Bun 1+.",
  "- A task is an exported function at module scope. Wrap it with `task({ f })` only when you want options like a timeout or an abort signal.",
  "- Tasks take ONE argument. Use a tuple or object for multiple values: `([a, b]) => a + b`.",
  "- Guard host-only code with `isMain` — workers re-import the module.",
  "- Module loading: each worker re-imports the module that DEFINES your tasks, and its top-level `import`s run in every worker (they are hoisted — `isMain` does NOT gate them). Keep tasks in a lean module separate from your server/framework code. Tasks must be `export`ed or the loader can't find them and the call silently hangs. `importTask` targets must be plain functions, not `task()` wrappers.",
  "- Create a pool with `createPool(options)({ taskA, taskB })`, then call `await pool.call.taskA(args)`.",
  "- Scheduling: compatible multi-worker pools use native work stealing by default. Workers claim tasks from a shared submit region while keeping private return lanes; control it with `host.steal`, `host.stealRegionLanes`, and `host.doorbell`. The task API does not change, and unsupported runtimes fall back to private lanes or polling.",
  "- Idle cost is a design goal: waiting threads are not allowed to burn CPU. A single worker spins 50us before parking because it is on the request's critical path; multi-worker pools park immediately, since a peer is already awake to take the work. The host doorbell replaces polling wake-ups on Node and Bun thread pools. Expect a bigger pool to raise CPU per request without raising throughput when the host is the only producer (a server), so size `threads` from measurements, not from core count — see the Multi-threading guide.",
  "- Cleanup: `using pool = createPool(...)` disposes the pool at scope exit. `await pool.shutdown()` still exists to close it earlier or to await teardown.",
  '- Isolation: `importTask({ href, name })` keeps a task\'s code off the host (only the worker imports it). Set `worker.runtime: "process"` to run each worker as a separate process — including inside a bwrap sandbox or a container.',
  "- Security: `importTask` prevents the task module from being imported or evaluated at host scope, but it is not a sandbox. For genuinely untrusted code, use process workers with an OS sandbox or container and restrictive permissions; runtime permissions are guardrails, not a complete security boundary.",
  "- Zero-copy IN: `ProcessSharedBuffer` (`knitting/shared-memory`) shares bytes across processes; `SharedArrayBuffer` and `BufferReference` (`knitting/unsafe`) move bytes to thread workers without copying. Pick by boundary — process vs thread.",
  "- Binary results: for large results from a thread worker, RETURN a `BufferReference`; owning Node addons can move them back zero-copy, while the safe default may take one copy on Deno/Bun (use the explicit borrow mode only when its lifetime rules fit). `knitting/utils` converts string/JSON/number ↔ `SharedArrayBuffer`.",
  "- Optimized for HTTP: `call.*()` accepts `Promise<supported>` inputs, so forward `request.arrayBuffer()` (e.g. Hono `c.req.arrayBuffer()`) straight into a task without awaiting it on the request thread — UTF-8 decode / JSON parse then happens in the worker. Ideal for SSR, JWT, and upload routes.",
  "- Workers are quiet by default: in strict mode worker `console.*` does NOT reach the host — set `permission: { console: true }` to surface it. Common direct exit calls (`process.exit`, `process.kill`, `process.abort`, and `Deno.exit`) are blocked, but this is not a complete security boundary; resource exhaustion and runtime or native-code vulnerabilities still require OS-level isolation.",
  "- Debugging goes to STDERR: pass `debug: true` to `createPool` (or set the `KNITTING_DEBUG=*` env var) to stream diagnostics, each line tagged with the worker (`host`, `w0`, `w1`, …), the runtime, and a per-worker ms timer. Select namespaces instead of all — `host` (pool/task setup), `imports` (which modules each worker loaded), `lifecycle` (worker ready / process events), `signals` (per-dispatch traffic, very chatty), `globals` (`globalThis` pollution per load phase) — via `debug: { host: true, imports: true }` or `KNITTING_DEBUG=host,imports`. The option and the env var merge; either can enable a namespace. Zero-cost when off: the logger module isn't even imported.",
  "- Payload size: dynamic payloads are hard-capped at ~8 MiB by default (over-cap calls reject with `KNT_ERROR_3`). Raise it with `payload: { maxPayloadBytes, payloadMaxByteLength }` — `maxPayloadBytes` must be `<= payloadMaxByteLength >> 3`; the buffer growth cap defaults to 64 MiB.",
  "- Cancellation & timeouts: `task({ f, timeout: { time: 100 } })` bounds a call, `task({ f, abortSignal: true })` injects an abort toolkit (`signal.hasAborted()`, `signal.now()`) as the task's second argument — it is NOT a DOM `AbortSignal` (no `.aborted`, no `addEventListener`, cannot be passed to `fetch`) — and `worker.hardTimeoutMs` is a hard wall-clock kill for runaway CPU.",
  '- Browser: `knitting/browser` runs the same pool API on web workers. Two hard requirements: the page must be cross-origin isolated (`Cross-Origin-Opener-Policy: same-origin` plus `Cross-Origin-Embedder-Policy: require-corp`, or `createPool` throws), and every task module must call `setModuleUrl(import.meta.url)` before defining tasks, because stack-based module discovery needs V8\'s `Error.prepareStackTrace`, which Firefox and Safari do not have. Not available in a page: process workers, compiled/Porffor workers, `BufferReference`, `ProcessSharedBuffer`, and passing a `SharedArrayBuffer` as a task argument. `permission: {...}` is accepted but IGNORED — a web worker holds the full privileges of the page that started it.',
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
// splash home page and off-navbar top-level pages such as license.md, so stale
// or out-of-band content never leaks into the llms files.
const SECTION_DIRS = new Set(SECTIONS.map((s) => s.dir));

// Pages hidden from the sidebar are excluded for the same reason. They are live
// demos or scratch pages (e.g. the browser smoke test), and their prose says
// nothing an agent can act on.
const isHidden = (d: Doc): boolean =>
  (d.data as { sidebar?: { hidden?: boolean } }).sidebar?.hidden === true;

export async function loadDocs(): Promise<Doc[]> {
  const docs = await getCollection("docs");
  return docs.filter((d) => SECTION_DIRS.has(d.id.split("/")[0]) && !isHidden(d));
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

// Benchmark tables and other text data the docs pull in with
// `import x from "../../../assets/.../file.md?raw"`. Limited to text
// extensions so the glob can't inline the charts and logos next to them.
const rawAssets = import.meta.glob("/src/assets/**/*.{md,txt,sh,json,csv}", {
  query: "?raw",
  eager: true,
  import: "default",
}) as Record<string, string>;

// `?raw` specifiers are relative to the doc, so match on the path from
// `assets/` onwards, which is unique within the repo.
function assetFor(specifier: string): string | undefined {
  const match = /assets\/(.+)$/.exec(specifier.replace(/\?raw$/, ""));
  if (!match) return undefined;
  const key = "/src/assets/" + match[1];
  return rawAssets[key] ?? rawCode[key];
}

// A fence long enough to survive whatever fences the file itself contains.
function fenceFor(code: string): string {
  const runs = [...code.matchAll(/^\s*(`{3,})/gm)].map((m) => m[1].length);
  return "`".repeat(Math.max(3, ...runs.map((n) => n + 1)));
}

const CODE_SENTINEL = "\u0000";
const INLINE_SENTINEL = "\u0001";

// Turn an MDX doc body into plain markdown: drop imports, inline getCode()
// snippets in place of <Code/> components, and strip the structural JSX
// (Tabs, Steps, Badge, custom components) while leaving fenced code untouched.
export function cleanBody(body: string): string {
  const codeMap = new Map<string, string>();
  const assetMap = new Map<string, string>();
  const inlined = new Set<string>();
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
    const raw = line.match(/^import\s+(\w+)\s+from\s+['"]([^'"]+\?raw)['"]/);
    if (raw) assetMap.set(raw[1], raw[2]);
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
        const snippet = codeMap.get(name);
        const asset = assetMap.get(name);
        const code = snippet
          ? codeFor(snippet)
          : asset
          ? assetFor(asset)
          : undefined;
        if (!code) return "";
        const source = (snippet ?? asset)!;
        const title = /\btitle=\{?["']([^"']+)["']/.exec(full)?.[1];
        const push = (block: string) => {
          blocks.push(block);
          return CODE_SENTINEL + (blocks.length - 1) + CODE_SENTINEL;
        };

        // The same table is often shown in two tabs. Inline it once and
        // point at it after that, so the full text does not carry it twice.
        if (inlined.has(source)) {
          return title ? push(`\nSame data as \`${title}\` above.\n`) : "";
        }
        inlined.add(source);

        const lang = /\blang="([\w-]+)"/.exec(full)?.[1] ?? "ts";
        const fence = fenceFor(code);
        const caption = title ? `\n\`${title}\`\n` : "";
        return push(
          caption + "\n" + fence + lang + "\n" + code.trim() + "\n" + fence +
            "\n",
        );
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
  // `Arc<Vec<u8>>` and `Envelope<H, B>` are prose, not markup. Hide inline
  // code before the tag strippers run, or they match from the `<` to the end
  // of the paragraph and take the sentence with them.
  const spans: string[] = [];
  text = text.replace(/(`+)([^`]*?)\1/g, (span) => {
    spans.push(span);
    return INLINE_SENTINEL + (spans.length - 1) + INLINE_SENTINEL;
  });

  text = text.replace(
    /<Badge\b[^>]*\btext=(?:"([^"]*)"|'([^']*)'|\{["']([^"']*)["']\})[^>]*\/>/g,
    (_, doubleQuoted, singleQuoted, braced) =>
      doubleQuoted ?? singleQuoted ?? braced ?? "",
  );
  text = htmlTablesToMarkdown(text);
  // Stop at a sentinel: a multi-line component must not swallow an inlined
  // snippet that sits between it and the next `/>`.
  text = text.replace(
    /<[A-Z][A-Za-z0-9.]*\b[^\u0000\u0001]*?\/>/g,
    "",
  );
  text = text.replace(/<\/?[A-Z][A-Za-z0-9.]*\b[^>]*>/g, "");
  text = text.replace(/<br\s*\/?><\/br>/gi, "\n");
  text = text.replace(/<br\s*\/?>/gi, "\n");
  text = text.replace(/<img\b[^>]*>/gi, "");
  // Inline SVG is markup an agent cannot read. Keep the accessible label,
  // which is the one part that says what the diagram shows.
  text = text.replace(
    /<svg\b([^>]*)>[\s\S]*?<\/svg>/gi,
    (_, attrs: string) => {
      const label = /\baria-label=["']([^"']+)["']/.exec(attrs)?.[1];
      return label ? `_Diagram: ${label}_` : "";
    },
  );
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
  return text.replace(
    /\u0001(\d+)\u0001/g,
    (_, index) => spans[Number(index)] ?? "",
  );
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
