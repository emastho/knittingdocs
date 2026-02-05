import { createPool, isMain } from "@vixeny/knitting";
import { piChunk } from "./montecarlo_pi.ts";

function intArg(name: string, fallback: number) {
  const idx = process.argv.indexOf(`--${name}`);
  if (idx !== -1 && idx + 1 < process.argv.length) {
    const v = Number(process.argv[idx + 1]);
    if (Number.isFinite(v) && v > 0) return Math.floor(v);
  }
  return fallback;
}

// Tunables (pick any numbers you like)
const TOTAL_SAMPLES = intArg("samples", 50_000_000_000);
const CHUNK_SAMPLES = intArg("chunk", 10_000_000);
const THREADS = intArg("threads", 6);

const { call, shutdown } = createPool({
  threads: THREADS,
  inliner: {
    position: "last",
    batchSize: 8,
  },
  balancer: "firstIdle",
})({ piChunk });

async function main() {
  const jobCount = Math.ceil(TOTAL_SAMPLES / CHUNK_SAMPLES);
  const jobs = new Array<Promise<{ inside: number; samples: number }>>(
    jobCount,
  );

  // Seed base: stable-ish, different each run
  const seedBase = ((Date.now() | 0) ^ 0x9e3779b9) | 0;

  // Queue one worker task per chunk.
  for (let i = 0; i < jobCount; i++) {
    const remaining = TOTAL_SAMPLES - i * CHUNK_SAMPLES;
    const samples = remaining >= CHUNK_SAMPLES ? CHUNK_SAMPLES : remaining;

    // Spread seeds so chunks don’t reuse the same random stream
    const seed = (seedBase + (i * 0x6d2b79f5)) | 0;

    jobs[i] = call.piChunk([seed, samples]);
  }

  const time = performance.now();
  const results = await Promise.all(jobs);
  const finished = performance.now();

  let inside = 0;
  let total = 0;
  for (const r of results) {
    inside += r.inside;
    total += r.samples;
  }

  const pi = (4 * inside) / total;

  // Quick sanity: expected sampling error scales like ~1/sqrt(N)
  const approxStdErr = 1 / Math.sqrt(total);

  console.log("Monte Carlo π estimate");
  console.log("threads      :", THREADS + 1);
  console.log("total samples:", total.toLocaleString());
  console.log("chunk size   :", CHUNK_SAMPLES.toLocaleString());
  console.log("pi           :", pi);
  console.log("took         :", (finished - time).toFixed(3), " ms");
  console.log("rough ±err   :", `~${(approxStdErr * 4).toExponential(2)}`);
}

if (isMain) {
  main().finally(shutdown);
}
