import { createPool, isMain } from "@vixeny/knitting";
import {
  buildDemoHashPackets,
  type HashBatchSummary,
  hashPasswordPacketBatchFast,
  hashPasswordPacketBatchFastHost,
} from "./salt_hashing.ts";

const THREADS = 2;
const REQUESTS = 2_000;
const BATCH = 32;
const ITERATIONS = 120_000;
const KEY_BYTES = 32;
const SALT_BYTES = 16;

function makeBatches(packets: Uint8Array[], batchSize: number): Uint8Array[][] {
  const out: Uint8Array[][] = [];
  for (let i = 0; i < packets.length; i += batchSize) {
    out.push(packets.slice(i, i + batchSize));
  }
  return out;
}

function merge(a: HashBatchSummary, b: HashBatchSummary): HashBatchSummary {
  return {
    count: a.count + b.count,
    outputBytes: a.outputBytes + b.outputBytes,
    digestXor: a.digestXor ^ b.digestXor,
  };
}

async function runHostBatches(
  batches: Uint8Array[][],
): Promise<HashBatchSummary> {
  let totals: HashBatchSummary = { count: 0, outputBytes: 0, digestXor: 0 };
  for (let i = 0; i < batches.length; i++) {
    totals = merge(totals, await hashPasswordPacketBatchFastHost(batches[i]!));
  }
  return totals;
}

async function runWorkerBatches(
  callBatch: (packets: Uint8Array[]) => Promise<HashBatchSummary>,
  batches: Uint8Array[][],
): Promise<HashBatchSummary> {
  const jobs: Promise<HashBatchSummary>[] = [];
  for (let i = 0; i < batches.length; i++) jobs.push(callBatch(batches[i]!));
  const results = await Promise.all(jobs);

  let totals: HashBatchSummary = { count: 0, outputBytes: 0, digestXor: 0 };
  for (let i = 0; i < results.length; i++) totals = merge(totals, results[i]!);
  return totals;
}

function same(a: HashBatchSummary, b: HashBatchSummary): boolean {
  return a.count === b.count &&
    a.outputBytes === b.outputBytes &&
    a.digestXor === b.digestXor;
}

function printMetrics(name: string, ms: number): void {
  const seconds = Math.max(1e-9, ms / 1000);
  const rps = REQUESTS / seconds;
  console.log(`${name} took       : ${ms.toFixed(2)} ms`);
  console.log(`${name} throughput : ${rps.toFixed(0)} req/s`);
}

async function main() {
  const packets = buildDemoHashPackets({
    count: REQUESTS,
    iterations: ITERATIONS,
    keyBytes: KEY_BYTES,
    saltBytes: SALT_BYTES,
  });
  const batches = makeBatches(packets, BATCH);

  const pool = createPool({ threads: THREADS })({
    hashPasswordPacketBatchFast,
  });

  try {
    const hostStart = performance.now();
    const hostTotals = await runHostBatches(batches);
    const hostMs = performance.now() - hostStart;

    const workerStart = performance.now();
    const workerTotals = await runWorkerBatches(
      pool.call.hashPasswordPacketBatchFast,
      batches,
    );
    const workerMs = performance.now() - workerStart;

    if (!same(hostTotals, workerTotals)) {
      throw new Error("Host and worker hashing summaries differ.");
    }

    const uplift = (hostMs / Math.max(1e-9, workerMs) - 1) * 100;

    console.log("Salt+hash quick bench");
    console.log("workload: PBKDF2-SHA256 on Uint8Array request packets");
    console.log("requests:", REQUESTS.toLocaleString());
    console.log("iterations:", ITERATIONS.toLocaleString());
    console.log("batch:", BATCH);
    console.log("threads:", THREADS);
    console.log("");
    printMetrics("host", hostMs);
    printMetrics("knitting", workerMs);
    console.log(`uplift         : ${uplift.toFixed(1)}%`);
    console.log(
      "verified sink  :",
      `${hostTotals.outputBytes ^ hostTotals.digestXor} / ${
        workerTotals.outputBytes ^ workerTotals.digestXor
      }`,
    );
  } finally {
    pool.shutdown();
  }
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
