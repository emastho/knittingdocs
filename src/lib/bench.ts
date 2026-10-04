// Benchmark runs from mimiMonads/knitting-vs-tokio-bench.
//
// Each directory under src/data/bench/ is one run, copied unchanged from the
// bench repo's results/<runId>/ by `npm run bench:sync`. Pages render tables
// and charts from these files instead of carrying numbers of their own, so a
// value on the site can always be traced to a committed run.

import { readFileSync } from "node:fs";
import { join } from "node:path";

export const BENCH_REPO = "https://github.com/mimiMonads/knitting-vs-tokio-bench";

export type RuntimeId = "node" | "deno" | "bun";
export const RUNTIMES: RuntimeId[] = ["node", "deno", "bun"];
export const RUNTIME_NAMES: Record<RuntimeId, string> = {
  node: "Node.js",
  deno: "Deno",
  bun: "Bun",
};

export type RunEnv = {
  capturedAtUnixMs: number;
  machine: string;
  os: { platform: string; release: string; arch: string };
  memoryBytes: number;
  runtime: { id: string; version: string; engine: string };
  knittingVersion: string;
  benchCommit: string | null;
  benchDirty: boolean;
};

type Sample = {
  suite: string;
  benchmark: string;
  arm: string;
  axisValue: number;
  opsPerIteration: number;
  stats: { avgNs: number; minNs: number; p50Ns: number; p99Ns: number; maxNs: number };
};

type SuiteReport = {
  runId: string;
  suite: string;
  env: RunEnv;
  samples: Sample[];
};

const files = import.meta.glob<RunEnv | SuiteReport>("../data/bench/*/*.json", {
  eager: true,
  import: "default",
});

const runEnvs = new Map<string, RunEnv>();
const reports: SuiteReport[] = [];
for (const [path, data] of Object.entries(files)) {
  const [runId, file] = path.split("/").slice(-2);
  if (file === "env.json") runEnvs.set(runId, data as RunEnv);
  else reports.push(data as SuiteReport);
}

const median = (values: number[]) => {
  const sorted = [...values].sort((a, b) => a - b);
  const middle = Math.floor(sorted.length / 2);
  return sorted.length % 2 ? sorted[middle] : (sorted[middle - 1] + sorted[middle]) / 2;
};

export type Spread = { median: number; min: number; max: number; runs: number };

export type ArmResult = {
  arm: string;
  byRuntime: Partial<Record<RuntimeId, Spread>>;
};

/**
 * Time per call for every arm of one benchmark at one batch size, across all
 * runs of the suite. A batch's average time is divided by the calls in it, so
 * batch 1 and batch 100 read on the same scale.
 */
export function perCallNs(suite: string, benchmark: string, axisValue: number): ArmResult[] {
  const values = new Map<string, Map<RuntimeId, number[]>>();
  for (const report of reports) {
    if (report.suite !== suite) continue;
    const runtime = report.env.runtime.id as RuntimeId;
    for (const sample of report.samples) {
      if (sample.benchmark !== benchmark || sample.axisValue !== axisValue) continue;
      const byRuntime = values.get(sample.arm) ?? new Map<RuntimeId, number[]>();
      const list = byRuntime.get(runtime) ?? [];
      list.push(sample.stats.avgNs / sample.opsPerIteration);
      byRuntime.set(runtime, list);
      values.set(sample.arm, byRuntime);
    }
  }

  return [...values].map(([arm, byRuntime]) => ({
    arm,
    byRuntime: Object.fromEntries(
      [...byRuntime].map(([runtime, list]) => [
        runtime,
        { median: median(list), min: Math.min(...list), max: Math.max(...list), runs: list.length },
      ]),
    ),
  }));
}

export type SuiteSummary = {
  runIds: string[];
  machines: string[];
  knittingVersions: string[];
  runtimes: Partial<Record<RuntimeId, string>>;
  firstCapturedAt: Date;
  lastCapturedAt: Date;
  benchCommits: string[];
  dirty: boolean;
};

/** What the runs of one suite were measured on, for the line above a chart. */
export function suiteSummary(suite: string): SuiteSummary {
  const suiteReports = reports.filter((report) => report.suite === suite);
  const runIds = [...new Set(suiteReports.map((report) => report.runId))].sort();
  if (runIds.length === 0) throw new Error(`no committed runs of the "${suite}" suite in src/data/bench`);

  const envs = runIds.map((runId) => {
    const env = runEnvs.get(runId);
    if (!env) throw new Error(`src/data/bench/${runId} has no env.json`);
    return env;
  });
  const times = envs.map((env) => env.capturedAtUnixMs);
  const runtimes: Partial<Record<RuntimeId, string>> = {};
  for (const report of suiteReports) {
    runtimes[report.env.runtime.id as RuntimeId] = report.env.runtime.version;
  }

  return {
    runIds,
    machines: [...new Set(envs.map((env) => env.machine))],
    knittingVersions: [...new Set(suiteReports.map((report) => report.env.knittingVersion))].sort(),
    runtimes,
    firstCapturedAt: new Date(Math.min(...times)),
    lastCapturedAt: new Date(Math.max(...times)),
    benchCommits: [...new Set(envs.map((env) => env.benchCommit ?? "unknown"))],
    dirty: envs.some((env) => env.benchDirty),
  };
}

/**
 * The Knitting release these docs describe: the version the docs' own
 * dependency resolves to. Read at build time, so bumping the dependency is
 * enough to flag every benchmark page measured on an older release.
 */
export const docsKnittingVersion: string = (() => {
  const manifest = join(process.cwd(), "node_modules", "@vixeny", "knitting", "package.json");
  return (JSON.parse(readFileSync(manifest, "utf8")) as { version: string }).version;
})();

/** "Intel(R) Xeon(R) Platinum 8168 CPU @ 2.70GHz (8t)" -> "Intel Xeon Platinum 8168 @ 2.70GHz, 8 threads" */
export function machineName(machine: string): string {
  return machine
    .replace(/\((R|TM)\)/g, "")
    .replace(/\bCPU\b/g, "")
    .replace(/\((\d+)t\)$/, ", $1 threads")
    .replace(/\s+,/g, ",")
    .replace(/\s{2,}/g, " ")
    .trim();
}

export function formatNs(ns: number): string {
  if (ns >= 1e6) return `${(ns / 1e6).toFixed(2)} ms`;
  const micros = ns / 1e3;
  if (micros >= 100) return `${micros.toFixed(0)} µs`;
  if (micros >= 10) return `${micros.toFixed(1)} µs`;
  return `${micros.toFixed(2)} µs`;
}

export const runUrl = (runId: string) => `${BENCH_REPO}/tree/master/results/${runId}`;
