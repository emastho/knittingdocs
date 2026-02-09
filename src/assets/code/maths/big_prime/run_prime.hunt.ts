import { createPool, isMain } from "@vixeny/knitting";
import { scanForProbablePrime } from "./prime_scan.ts";

function intArg(name: string, fallback: number) {
  const i = process.argv.indexOf(`--${name}`);
  if (i !== -1 && i + 1 < process.argv.length) {
    const v = Number(process.argv[i + 1]);
    if (Number.isFinite(v) && v > 0) return Math.floor(v);
  }
  return fallback;
}

const THREADS = intArg("threads", 4);
const BITS = intArg("bits", 1500);
const WINDOW = intArg("window", 10_000_000);
const CHUNK = intArg("chunk", 500_000);
const ROUNDS = intArg("rounds", 10);

function xorshift32(s: number): number {
  s |= 0;
  s ^= s << 13;
  s ^= s >>> 17;
  s ^= s << 5;
  return s | 0;
}

function makeRandomOdd(bits: number, seed: number): bigint {
  // Build a BigInt from 3x 32-bit chunks, mask to bits, set top bit, make odd.
  let s = seed | 0;
  let x = 0n;
  for (let k = 0; k < 3; k++) {
    s = xorshift32(s);
    x = (x << 32n) | BigInt(s >>> 0);
  }
  const mask = (1n << BigInt(bits)) - 1n;
  x &= mask;
  x |= 1n << BigInt(bits - 1);
  x |= 1n;
  return x;
}

const seedBase = (Date.now() | 0) ^ 0x9e3779b9;
let windowStartOdd = makeRandomOdd(BITS, seedBase);

const { call, shutdown } = createPool({
  threads: THREADS,
  balancer: "firstIdle",
})({ scanForProbablePrime });

let stopping = false;
process.on("SIGINT", () => {
  if (stopping) return;
  stopping = true;
  console.log("\nCtrl+C received. Shutting down...");
  shutdown();
  process.exit(0);
});

function splitCounts(total: number, parts: number): number[] {
  const base = Math.floor(total / parts);
  const rem = total % parts;
  const out = new Array(parts);
  for (let i = 0; i < parts; i++) out[i] = base + (i < rem ? 1 : 0);
  return out;
}

async function scanOneWindow(): Promise<
  { hit: string | null; tested: number }
> {
  // We interleave odds across threads: thread i tests start+2i, start+2i+2T, ...
  const stepNum = 2 * THREADS;

  // Divide WINDOW across threads, and within each thread further divide into CHUNK-sized tasks.
  const perThread = splitCounts(WINDOW, THREADS);

  let bestHit: string | null = null;
  let tested = 0;

  // For each thread, we run sequential “subtasks” so each thread covers its share of WINDOW.
  // But all threads run in parallel each wave.
  const subTasksPerThread = perThread.map((c) => Math.ceil(c / CHUNK));
  const maxSubs = Math.max(...subTasksPerThread);

  for (let sub = 0; sub < maxSubs; sub++) {
    const jobs: Promise<[number, string, number]>[] = [];

    for (let t = 0; t < THREADS; t++) {
      const threadTotal = perThread[t];
      const startAt = sub * CHUNK;
      if (startAt >= threadTotal) continue;

      const count = Math.min(CHUNK, threadTotal - startAt);

      // offset in "odd steps": 2*t + 2*THREADS*startAt
      const offsetNum = 2 * t + stepNum * startAt;

      jobs.push(
        call.scanForProbablePrime([
          windowStartOdd.toString(),
          count,
          stepNum,
          offsetNum,
          ROUNDS,
        ]),
      );

      tested += count;
    }

    const results = await Promise.all(jobs);

    // If any job found a hit, keep the smallest hit (nice for consistency)
    for (const [found, primeStr] of results) {
      if (found) {
        if (bestHit === null) bestHit = primeStr;
        else {
          // compare as BigInt safely
          const a = BigInt(bestHit);
          const b = BigInt(primeStr);
          if (b < a) bestHit = primeStr;
        }
      }
    }
  }

  return { hit: bestHit, tested };
}

async function main() {
  console.log("Prime hunt (probable primes via Miller–Rabin)");
  console.log(
    "threads:",
    THREADS,
    "bits:",
    BITS,
    "window:",
    WINDOW.toLocaleString(),
    "chunk:",
    CHUNK.toLocaleString(),
    "rounds:",
    ROUNDS,
  );
  console.log("start  :", windowStartOdd.toString());
  console.log("mode   : infinite windows (Ctrl+C to stop)");

  let windowsDone = 0;
  let totalTested = 0n;

  while (true) {
    const { hit, tested } = await scanOneWindow();
    windowsDone++;
    totalTested += BigInt(tested);

    if (hit) {
      console.log(
        `[window ${windowsDone}] +${tested.toLocaleString()} tested (total ${totalTested.toString()}) | HIT: ${hit}`,
      );
    } else {
      console.log(
        `[window ${windowsDone}] +${tested.toLocaleString()} tested (total ${totalTested.toString()}) | no hit (Ctrl+C to stop)`,
      );
    }

    // Move start forward by WINDOW odd candidates (i.e., +2*WINDOW)
    windowStartOdd += 2n * BigInt(WINDOW);
  }
}

if (isMain) {
  main().finally(shutdown);
}
