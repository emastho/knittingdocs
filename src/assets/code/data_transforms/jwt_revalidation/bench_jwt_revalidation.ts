import { createPool, isMain } from "@vixeny/knitting";
import { bench, boxplot, run, summary } from "mitata";
import {
  buildDemoRevalidateRequests,
  makeBatches,
  mergeRenewalSummary,
  type RenewalSummary,
  revalidateTokenBatchFast,
  revalidateTokenBatchFastHost,
  sameRenewalSummary,
} from "./utils.ts";

const THREADS = 2;
const REQUESTS = 25_000;
const INVALID_PERCENT = 10;
const BATCH = 64;

async function runHostBatches(rawBatches: string[][]): Promise<RenewalSummary> {
  let totals: RenewalSummary = {
    ok: 0,
    renewed: 0,
    rejected: 0,
    outputBytes: 0,
  };

  for (let i = 0; i < rawBatches.length; i++) {
    totals = mergeRenewalSummary(
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
    totals = mergeRenewalSummary(totals, results[i]!);
  }
  return totals;
}

async function main() {
  const rawRequests = await buildDemoRevalidateRequests({
    count: REQUESTS,
    invalidPercent: INVALID_PERCENT,
  });
  const rawBatches = makeBatches(rawRequests, BATCH);

  const pool = createPool({ threads: THREADS })({ revalidateTokenBatchFast });
  let sink = 0;

  try {
    const hostCheck = await runHostBatches(rawBatches);
    const workerCheck = await runWorkerBatches(
      pool.call.revalidateTokenBatchFast,
      rawBatches,
    );
    if (!sameRenewalSummary(hostCheck, workerCheck)) {
      throw new Error("Host and worker JWT summaries differ.");
    }

    console.log("JWT revalidation benchmark (mitata)");
    console.log(
      "workload: verify token -> renew when allowed -> JSON.stringify",
    );
    console.log("requests per iteration:", REQUESTS.toLocaleString());
    console.log("invalid rate:", `${INVALID_PERCENT}%`);
    console.log("batch size:", BATCH);
    console.log("threads:", THREADS);

    boxplot(() => {
      summary(() => {
        bench(`host (${REQUESTS.toLocaleString()} req, batch ${BATCH})`, async () => {
          const totals = await runHostBatches(rawBatches);
          sink = totals.outputBytes;
        });

        bench(
          `knitting (${THREADS} thread${
            THREADS === 1 ? "" : "s"
          }, ${REQUESTS.toLocaleString()} req, batch ${BATCH})`,
          async () => {
            const totals = await runWorkerBatches(
              pool.call.revalidateTokenBatchFast,
              rawBatches,
            );
            sink = totals.outputBytes;
          },
        );
      });
    });

    await run();
    console.log("last output bytes:", sink.toLocaleString());
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
