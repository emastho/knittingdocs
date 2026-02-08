import { createPool, isMain } from "@vixeny/knitting";
import { walkChunk } from "./walk2d.ts";

function intArg(name: string, fallback: number) {
  const i = process.argv.indexOf(`--${name}`);
  if (i !== -1 && i + 1 < process.argv.length) {
    const v = Number(process.argv[i + 1]);
    if (Number.isFinite(v) && v > 0) return Math.floor(v);
  }
  return fallback;
}
function numArg(name: string, fallback: number) {
  const i = process.argv.indexOf(`--${name}`);
  if (i !== -1 && i + 1 < process.argv.length) {
    const v = Number(process.argv[i + 1]);
    if (Number.isFinite(v) && v > 0) return v;
  }
  return fallback;
}

// Tunables (pick any data you like)
const THREADS = intArg("threads", 4);
const TOTAL_RUNS = intArg("runs", 5_000_000);
const RUNS_PER_JOB = intArg("batch", 5_000);
const MAX_STEPS = intArg("steps", 15_000);
const RADIUS = numArg("radius", 100);

const { call, send, shutdown } = createPool({
  threads: THREADS,
  balancer: "firstIdle",
  // Optional: inliner helps if each job is too small.
  // inliner: { position: "last", batchSize: 1 },
})({ walkChunk });

async function main() {
  const jobsCount = Math.ceil(TOTAL_RUNS / RUNS_PER_JOB);
  const jobs = new Array<
    Promise<
      {
        escaped: number;
        totalRuns: number;
        sumSteps: number;
        sumSteps2: number;
      }
    >
  >(jobsCount);

  const seedBase = ((Date.now() | 0) ^ 0x9e3779b9) | 0;

  for (let j = 0; j < jobsCount; j++) {
    const remaining = TOTAL_RUNS - j * RUNS_PER_JOB;
    const runs = remaining >= RUNS_PER_JOB ? RUNS_PER_JOB : remaining;

    // Spread seeds per job so streams differ
    const seed = (seedBase + (j * 0x6d2b79f5)) | 0;

    jobs[j] = call.walkChunk([seed, runs, MAX_STEPS, RADIUS]);
  }

  // Kick dispatcher once after enqueueing a batch
  send();

  const results = await Promise.all(jobs);

  let escaped = 0;
  let total = 0;
  let sumSteps = 0;
  let sumSteps2 = 0;

  for (const r of results) {
    escaped += r.escaped;
    total += r.totalRuns;
    sumSteps += r.sumSteps;
    sumSteps2 += r.sumSteps2;
  }

  const pEscape = escaped / total;

  let mean = NaN;
  let stdev = NaN;

  if (escaped > 0) {
    mean = sumSteps / escaped;
    const mean2 = sumSteps2 / escaped;
    const variance = Math.max(0, mean2 - mean * mean);
    stdev = Math.sqrt(variance);
  }

  console.log("Monte Carlo: 2D random-walk first-exit");
  console.log("threads     :", THREADS);
  console.log("total runs  :", total.toLocaleString());
  console.log("radius      :", RADIUS);
  console.log("max steps   :", MAX_STEPS.toLocaleString());
  console.log("escape prob :", pEscape);
  console.log("mean steps  :", mean);
  console.log("stdev steps :", stdev);
}

if (isMain) {
  main().finally(shutdown);
}
