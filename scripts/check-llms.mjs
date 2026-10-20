import assert from "node:assert/strict";
import { readFileSync, existsSync, readdirSync } from "node:fs";
import { join } from "node:path";
import { fileURLToPath } from "node:url";

// Check built navigation artifacts; this does not measure agent implementation
// success. Real agent evaluations should record retrieval cost and run the code.
const root = new URL("../dist/", import.meta.url);
const index = readFileSync(new URL("llms.txt", root), "utf8");
const full = readFileSync(new URL("llms-full.txt", root), "utf8");
const version = JSON.parse(readFileSync(new URL("../node_modules/@vixeny/knitting/package.json", import.meta.url), "utf8")).version;
for (const text of [index, full]) assert.ok(text.includes(`Documentation baseline: Knitting ${version}`));
assert.ok(index.indexOf("## Start here") < index.indexOf("## Before writing code"));
assert.ok(index.indexOf("## Find documentation by task") < index.indexOf("## Documentation index"));
assert.ok(index.indexOf("## Optional") < index.indexOf("[llms-full.txt]"));
assert.ok(!index.includes("host.stealSingleClaimMicroseconds"));
assert.ok(full.includes("host.stealSingleClaimMicroseconds"));
assert.ok(index.includes("finally") && index.includes("await pool.shutdown()"));
assert.ok(!index.includes("browser-smoke-test"));

// Representative tasks must route directly to the relevant maintained pages.
const scenarios = [
  ["Add Knitting", ["start/quick-start/", "guides/defining-tasks/"]],
  ["Parallelize an HTTP route", ["examples/servers/hono_server/", "guides/multi-threading/"]],
  ["Move large binary payloads", ["guides/payloads/", "guides/buffer-reference/"]],
  ["Isolate untrusted work", ["guides/process-workers/", "guides/permissions/"]],
  ["Diagnose hangs", ["guides/defining-tasks/", "guides/creating-pools/#debug"]],
  ["Handle cancellation", ["guides/defining-tasks/", "guides/creating-pools/"]],
  ["Improve p99", ["guides/performance/", "guides/work-stealing/"]],
  ["Use browser workers", ["guides/browser/"]],
  ["Investigate the protocol", ["extras/architecture/", "guides/work-stealing/"]],
];
for (const [task, targets] of scenarios) {
  const line = index.split("\n").find((line) => line.startsWith(`- ${task}`));
  assert.ok(line, `Missing task route: ${task}`);
  for (const target of targets) assert.ok(line.includes(target), `${task} should route to ${target}`);
}

// Derive the deployment base from the index's own generated link.
const quickStart = /\[Quick Start\]\(([^)]+)\)/.exec(index)[1];
const base = new URL(quickStart, "https://example.test").pathname.replace(/start\/quick-start\/$/, "");
let markdownCount = 0;
for (const match of index.matchAll(/\[[^\]]+\]\(([^)]+)\)/g)) {
  const url = new URL(match[1], "https://example.test");
  if (!url.pathname.startsWith(base)) continue;
  const path = url.pathname.slice(base.length);
  if (!path.startsWith("documents/") && !path.endsWith("/") && path !== "llms-full.txt") continue;
  // External source links are not local site resources.
  if (url.host !== new URL(quickStart, "https://example.test").host) continue;
  const file = new URL(path.endsWith("/") ? `${path}index.html` : path, root);
  assert.ok(existsSync(file), `Broken generated link: ${match[1]}`);
  if (url.hash) assert.ok(readFileSync(file, "utf8").includes(`id="${url.hash.slice(1)}"`), `Missing anchor: ${match[1]}`);
  if (path.startsWith("documents/")) {
    markdownCount++;
    const body = readFileSync(file, "utf8");
    assert.ok(body.startsWith("# ") && body.includes("URL: "), `Invalid Markdown: ${path}`);
    assert.ok(!/^import .*from ['"]@astrojs\/starlight/m.test(body));
    assert.ok(!/<Code\b/.test(body), `Unexpanded snippet: ${path}`);
  }
}
const walk = (dir) => readdirSync(dir, { withFileTypes: true }).flatMap((entry) =>
  entry.isDirectory() ? walk(join(dir, entry.name)) : [join(dir, entry.name)]);
assert.equal(markdownCount, walk(fileURLToPath(new URL("documents/", root))).filter((file) => file.endsWith(".md") && readFileSync(file, "utf8").includes("Documentation baseline:")).length,
  "Every generated doc Markdown page must appear in the index");
const quickMarkdown = readFileSync(new URL("documents/start/quick-start.md", root), "utf8");
assert.ok(quickMarkdown.includes("createPool") && quickMarkdown.includes("```"));
console.log(`Validated ${scenarios.length} task routes, ${markdownCount} Markdown pages, generated links and debug anchor.`);
