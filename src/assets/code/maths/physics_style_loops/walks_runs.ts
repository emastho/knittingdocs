import { createPool, isMain } from "knitting";
import { walkChunk } from "./walk2d.ts";

type Options = {
  threads: number;
  runs: number;
  batch: number;
  maxSteps: number;
  radius: number;
};

type WalkResult = {
  escaped: number;
  totalRuns: number;
  sumSteps: number;
  sumSteps2: number;
};

function positiveIntArg(name: string, fallback: number): number {
  const index = process.argv.indexOf(`--${name}`);
  const value = index === -1 ? undefined : Number(process.argv[index + 1]);
  return Number.isInteger(value) && value > 0 ? value : fallback;
}

function readOptions(): Options {
  return {
    threads: positiveIntArg("threads", 4),
    runs: positiveIntArg("runs", 50_000),
    batch: positiveIntArg("batch", 2_500),
    maxSteps: positiveIntArg("steps", 3_000),
    radius: positiveIntArg("radius", 40),
  };
}

async function main() {
  const options = readOptions();
  const jobCount = Math.ceil(options.runs / options.batch);
  const seed = 0x1234_5678;

  using pool = createPool({ threads: options.threads })({ walkChunk });

  const started = performance.now();
  const jobs: Promise<WalkResult>[] = [];

  for (let job = 0; job < jobCount; job++) {
    const offset = job * options.batch;
    const runs = Math.min(options.batch, options.runs - offset);
    const jobSeed = (seed + job * 0x6d2b_79f5) | 0;

    jobs.push(
      pool.call.walkChunk([
        jobSeed,
        runs,
        options.maxSteps,
        options.radius,
      ]),
    );
  }

  const results = await Promise.all(jobs);
  const total = results.reduce(
    (summary, result) => ({
      escaped: summary.escaped + result.escaped,
      totalRuns: summary.totalRuns + result.totalRuns,
      sumSteps: summary.sumSteps + result.sumSteps,
      sumSteps2: summary.sumSteps2 + result.sumSteps2,
    }),
    { escaped: 0, totalRuns: 0, sumSteps: 0, sumSteps2: 0 },
  );

  const escapeProbability = total.escaped / total.totalRuns;
  const meanSteps = total.escaped ? total.sumSteps / total.escaped : 0;
  const meanStepsSquared = total.escaped
    ? total.sumSteps2 / total.escaped
    : 0;
  const standardDeviation = Math.sqrt(
    Math.max(0, meanStepsSquared - meanSteps * meanSteps),
  );
  const elapsed = performance.now() - started;

  console.log(`threads:           ${options.threads}`);
  console.log(`runs:              ${total.totalRuns.toLocaleString()}`);
  console.log(`batches:           ${jobCount.toLocaleString()}`);
  console.log(`radius:            ${options.radius}`);
  console.log(`max steps:         ${options.maxSteps.toLocaleString()}`);
  console.log(`escape probability: ${escapeProbability.toFixed(4)}`);
  console.log(`mean escape steps:  ${meanSteps.toFixed(1)}`);
  console.log(`stdev steps:       ${standardDeviation.toFixed(1)}`);
  console.log(`elapsed:           ${elapsed.toFixed(0)} ms`);
}

if (isMain) {
  await main();
}
