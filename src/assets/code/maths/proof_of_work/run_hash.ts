import { createPool, isMain } from "knitting";
import { findHash, type HashResult } from "./find_hash.ts";

type Options = {
  threads: number;
  zeroes: number;
  region: number;
};

type AbortablePromise<T> = Promise<T> & {
  reject: (reason?: unknown) => void;
};

const PREFIX = "knitting-proof-of-work-v1";

function positiveIntArg(name: string, fallback: number): number {
  const index = process.argv.indexOf(`--${name}`);
  const value = index === -1 ? undefined : Number(process.argv[index + 1]);
  return Number.isSafeInteger(value) && value > 0 ? value : fallback;
}

function readOptions(): Options {
  return {
    threads: positiveIntArg("threads", 4),
    zeroes: Math.min(positiveIntArg("zeroes", 4), 64),
    region: positiveIntArg("region", 50_000_000),
  };
}

function waitForFirstHash(
  jobs: AbortablePromise<HashResult>[],
): Promise<HashResult | null> {
  return new Promise((resolve, reject) => {
    let remaining = jobs.length;

    for (const job of jobs) {
      job.then(
        (result) => {
          if (result.nonce !== null) {
            resolve(result);
            return;
          }

          remaining--;
          if (remaining === 0) resolve(null);
        },
        reject,
      );
    }
  });
}

async function main() {
  const options = readOptions();
  const workerCount = Math.min(options.threads, options.region);

  using pool = createPool({
    threads: options.threads,
    abortSignalCapacity: workerCount,
  })({ findHash });

  const started = performance.now();
  const jobs: AbortablePromise<HashResult>[] = [];

  for (let worker = 0; worker < workerCount; worker++) {
    const count = Math.ceil((options.region - worker) / options.threads);

    jobs.push(
      pool.call.findHash([
        PREFIX,
        worker,
        count,
        options.threads,
        options.zeroes,
      ]),
    );
  }

  let winner: HashResult | null;
  try {
    winner = await waitForFirstHash(jobs);
    if (winner !== null) {
      for (const job of jobs) job.reject();
    }

    const results = await Promise.all(jobs);
    const tested = results.reduce((total, result) => total + result.tested, 0);
    const cancelled = results.some((result) => result.aborted);
    const elapsed = performance.now() - started;

    console.log(`threads:    ${options.threads}`);
    console.log(`prefix:     ${PREFIX}`);
    console.log(`zeroes:     ${options.zeroes}`);
    console.log(`region:     ${options.region.toLocaleString()} nonces`);
    console.log(`workers:    ${workerCount}`);
    console.log(`tested:     ${tested.toLocaleString()}`);
    console.log(`nonce:      ${winner?.nonce ?? "not found"}`);
    console.log(`hash:       ${winner?.hash ?? "-"}`);
    console.log(`cancelled:  ${cancelled ? "yes" : "no"}`);
    console.log(`elapsed:    ${elapsed.toFixed(0)} ms`);
  } catch (error) {
    for (const job of jobs) job.reject();
    await Promise.allSettled(jobs);
    throw error;
  }
}

if (isMain) {
  await main();
}
