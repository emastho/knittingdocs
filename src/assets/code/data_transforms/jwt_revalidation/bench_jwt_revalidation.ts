import { createPool, isMain } from "@vixeny/knitting";
import {
  buildDemoRevalidateRequests,
  type RenewalSummary,
  revalidateTokenBatchFast,
  revalidateTokenBatchFastHost,
} from "./jwt_revalidation.ts";

const THREADS = 2;
const REQUESTS = 50_000;
const INVALID_PERCENT = 10;
const BATCH = 64;

function makeBatches(rawRequests: string[], batchSize: number): string[][] {
  const batches: string[][] = [];
  for (let i = 0; i < rawRequests.length; i += batchSize) {
    batches.push(rawRequests.slice(i, i + batchSize));
  }
  return batches;
}

function mergeSummary(a: RenewalSummary, b: RenewalSummary): RenewalSummary {
  return {
    ok: a.ok + b.ok,
    renewed: a.renewed + b.renewed,
    rejected: a.rejected + b.rejected,
    outputBytes: a.outputBytes + b.outputBytes,
  };
}

async function runHostBatches(rawBatches: string[][]): Promise<RenewalSummary> {
  let totals: RenewalSummary = {
    ok: 0,
    renewed: 0,
    rejected: 0,
    outputBytes: 0,
  };

  for (let i = 0; i < rawBatches.length; i++) {
    totals = mergeSummary(
      totals,
      await revalidateTokenBatchFastHost(rawBatches[i]!),
    );
  }

  return totals;
}

async function runWorkerBatches(
  callBatch: (rawRequests: string[]) => Promise<RenewalSummary>,
  rawBatches: string[][],
): Promise<RenewalSummary> {
  const jobs: Promise<RenewalSummary>[] = [];
  for (let i = 0; i < rawBatches.length; i++) {
    jobs.push(callBatch(rawBatches[i]!));
  }

  const results = await Promise.all(jobs);

  let totals: RenewalSummary = {
    ok: 0,
    renewed: 0,
    rejected: 0,
    outputBytes: 0,
  };
  for (let i = 0; i < results.length; i++) {
    totals = mergeSummary(totals, results[i]!);
  }
  return totals;
}

function sameSummary(a: RenewalSummary, b: RenewalSummary): boolean {
  return a.ok === b.ok &&
    a.renewed === b.renewed &&
    a.rejected === b.rejected &&
    a.outputBytes === b.outputBytes;
}

function printMetrics(name: string, ms: number): void {
  const seconds = Math.max(1e-9, ms / 1000);
  const rps = REQUESTS / seconds;
  console.log(`${name} took       : ${ms.toFixed(2)} ms`);
  console.log(`${name} throughput : ${rps.toFixed(0)} req/s`);
}

async function main() {
  const rawRequests = await buildDemoRevalidateRequests({
    count: REQUESTS,
    invalidPercent: INVALID_PERCENT,
  });
  const rawBatches = makeBatches(rawRequests, BATCH);

  const pool = createPool({ threads: THREADS })({ revalidateTokenBatchFast });

  try {
    const hostCheck = await runHostBatches(rawBatches);
    const workerCheck = await runWorkerBatches(
      pool.call.revalidateTokenBatchFast,
      rawBatches,
    );
    if (!sameSummary(hostCheck, workerCheck)) {
      throw new Error("Host and worker JWT summaries differ.");
    }

    const hostStart = performance.now();
    const hostTotals = await runHostBatches(rawBatches);
    const hostMs = performance.now() - hostStart;

    const workerStart = performance.now();
    const workerTotals = await runWorkerBatches(
      pool.call.revalidateTokenBatchFast,
      rawBatches,
    );
    const workerMs = performance.now() - workerStart;

    const uplift = (hostMs / Math.max(1e-9, workerMs) - 1) * 100;

    console.log("JWT revalidation quick bench");
    console.log(
      "workload: verify token -> renew when allowed -> JSON.stringify",
    );
    console.log("requests:", REQUESTS.toLocaleString());
    console.log("invalid rate:", `${INVALID_PERCENT}%`);
    console.log("batch:", BATCH);
    console.log("threads:", THREADS);
    console.log("");
    printMetrics("host", hostMs);
    printMetrics("knitting", workerMs);
    console.log(`uplift         : ${uplift.toFixed(1)}%`);
    console.log(
      "verified bytes :",
      `${hostTotals.outputBytes.toLocaleString()} / ${
        workerTotals.outputBytes.toLocaleString()
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
