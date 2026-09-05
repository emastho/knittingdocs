import { createPool, isMain } from "knitting";
import { piChunk } from "./montecarlo_pi.ts";

type Options = {
  threads: number;
  samples: number;
  chunk: number;
};

function positiveIntArg(name: string, fallback: number): number {
  const index = process.argv.indexOf(`--${name}`);
  const value = index === -1 ? undefined : Number(process.argv[index + 1]);
  return Number.isInteger(value) && value > 0 ? value : fallback;
}

function readOptions(): Options {
  return {
    threads: positiveIntArg("threads", 4),
    samples: positiveIntArg("samples", 50_000_000),
    chunk: positiveIntArg("chunk", 1_000_000),
  };
}

async function main() {
  const options = readOptions();
  const jobCount = Math.ceil(options.samples / options.chunk);
  const seed = 0x1234_5678;

  using pool = createPool({ threads: options.threads })({ piChunk });

  const started = performance.now();
  const jobs: Promise<number>[] = [];

  for (let job = 0; job < jobCount; job++) {
    const samples = Math.min(
      options.chunk,
      options.samples - job * options.chunk,
    );
    jobs.push(pool.call.piChunk([seed + job, samples]));
  }

  const inside = (await Promise.all(jobs)).reduce(
    (total, count) => total + count,
    0,
  );
  const elapsed = performance.now() - started;
  const pi = (4 * inside) / options.samples;
  const error = Math.abs(Math.PI - pi);

  console.log(`threads: ${options.threads}`);
  console.log(`samples: ${options.samples.toLocaleString()}`);
  console.log(`chunks:  ${jobCount.toLocaleString()}`);
  console.log(`pi:      ${pi.toFixed(8)}`);
  console.log(`error:   ${error.toExponential(2)}`);
  console.log(`elapsed: ${elapsed.toFixed(0)} ms`);
}

if (isMain) {
  await main();
}
