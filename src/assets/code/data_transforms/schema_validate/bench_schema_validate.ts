import { createPool, isMain } from "@vixeny/knitting";
import { bench, boxplot, run, summary } from "mitata";
import {
  buildPayloads,
  makeBatches,
  mergeValidationSummary,
  parseAndValidateBatchFast,
  parseAndValidateBatchFastHost,
  sameValidationSummary,
  type ValidationSummary,
} from "./utils.ts";

const THREADS = 2;
const REQUESTS = 20_000;
const INVALID_PERCENT = 15;
const BATCH = 64;

async function main() {
  const payloads = buildPayloads(REQUESTS, INVALID_PERCENT);
  const payloadBatches = makeBatches(payloads, BATCH);

  const pool = createPool({
    threads: THREADS,
  })({ parseAndValidateBatchFast });
  let sink = 0;

  try {
    const hostCheck = runHostBatches(payloadBatches);
    const workerCheck = await runWorkerBatches(
      pool.call.parseAndValidateBatchFast,
      payloadBatches,
    );

    if (!sameValidationSummary(hostCheck, workerCheck)) {
      throw new Error("Host and worker validation counts differ.");
    }

    console.log("Schema validation benchmark (mitata)");
    console.log("workload: JSON.parse + UserSchema.safeParse");
    console.log("requests per iteration:", REQUESTS.toLocaleString());
    console.log("invalid rate:", `${INVALID_PERCENT}%`);
    console.log("batch size:", BATCH);
    console.log("threads:", THREADS);

    boxplot(() => {
      summary(() => {
        bench(`host (${REQUESTS.toLocaleString()} req, batch ${BATCH})`, () => {
          const totals = runHostBatches(payloadBatches);
          sink = totals.valid;
        });

        bench(
          `knitting (${THREADS} thread${
            THREADS === 1 ? "" : "s"
          }, ${REQUESTS.toLocaleString()} req, batch ${BATCH})`,
          async () => {
            const totals = await runWorkerBatches(
              pool.call.parseAndValidateBatchFast,
              payloadBatches,
            );
            sink = totals.valid;
          },
        );
      });
    });

    await run();
    console.log("last valid count:", sink.toLocaleString());
  } finally {
    pool.shutdown();
  }
}

function runHostBatches(payloadBatches: string[][]): ValidationSummary {
  let totals: ValidationSummary = { valid: 0, invalid: 0 };

  for (let i = 0; i < payloadBatches.length; i++) {
    totals = mergeValidationSummary(
      totals,
      parseAndValidateBatchFastHost(payloadBatches[i]!),
    );
  }

  return totals;
}

async function runWorkerBatches(
  callBatch: (payloads: string[]) => Promise<ValidationSummary>,
  payloadBatches: string[][],
): Promise<ValidationSummary> {
  const jobs: Promise<ValidationSummary>[] = [];
  for (let i = 0; i < payloadBatches.length; i++) {
    jobs.push(callBatch(payloadBatches[i]!));
  }

  const results = await Promise.all(jobs);

  let totals: ValidationSummary = { valid: 0, invalid: 0 };
  for (let i = 0; i < results.length; i++) {
    totals = mergeValidationSummary(totals, results[i]!);
  }
  return totals;
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
