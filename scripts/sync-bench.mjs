// Copy benchmark runs from a knitting-vs-tokio-bench checkout into
// src/data/bench/, where the benchmark pages read them.
//
//   node scripts/sync-bench.mjs <bench-repo> <runId...>
//   npm run bench:sync -- ../knitting-vs-tokio-bench 1789245992919
//
// Only files committed in the bench repo are copied, so every number on the
// site points at a run anyone can check out. A run recorded against
// uncommitted bench code is copied with a warning; the page shows that too.

import { execFileSync } from "node:child_process";
import { copyFile, mkdir, readFile, rm } from "node:fs/promises";
import { basename, join, resolve } from "node:path";

const [repoArg, ...runIds] = process.argv.slice(2);
if (!repoArg || runIds.length === 0) {
  console.error("usage: node scripts/sync-bench.mjs <bench-repo> <runId...>");
  process.exit(1);
}

const repo = resolve(repoArg);
const target = resolve("src/data/bench");

const tracked = (runId) => {
  const output = execFileSync("git", ["-C", repo, "ls-files", "--", `results/${runId}`], {
    encoding: "utf8",
  });
  return output.split("\n").filter(Boolean);
};

for (const runId of runIds) {
  if (!/^\d+$/.test(runId)) {
    console.error(`not a run id: ${runId}`);
    process.exit(1);
  }
  const files = tracked(runId);
  if (!files.some((file) => basename(file) === "env.json")) {
    console.error(`results/${runId} is not committed in ${repo}; commit the run first`);
    process.exit(1);
  }

  const destination = join(target, runId);
  await rm(destination, { recursive: true, force: true });
  await mkdir(destination, { recursive: true });
  for (const file of files) await copyFile(join(repo, file), join(destination, basename(file)));

  const env = JSON.parse(await readFile(join(destination, "env.json"), "utf8"));
  const dirty = env.benchDirty ? "  (recorded with uncommitted bench changes)" : "";
  console.log(`${runId}: ${files.length} files, knitting ${env.knittingVersion}, ${env.machine}${dirty}`);
}
