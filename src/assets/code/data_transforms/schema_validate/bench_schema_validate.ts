import { createPool, isMain } from "@vixeny/knitting";
import {
  parseAndValidateBatchFast,
  parseAndValidateBatchFastHost,
  type ValidationSummary,
} from "./parse_validate.ts";

const THREADS = 2;
const REQUESTS = 50_000;
const INVALID_PERCENT = 15;
const BATCH = 64;

function makeValidPayload(i: number): string {
  const short = i.toString(36);
  const role = i % 9 === 0 ? "admin" : "user";

  return JSON.stringify({
    id: `u_${short}`,
    email: `${short}@knitting.dev`,
    displayName: `User ${short.toUpperCase()}`,
    age: 18 + (i % 60),
    roles: [role],
    marketingOptIn: i % 2 === 0,
  });
}

function makePayload(i: number): string {
  if (i % 100 >= INVALID_PERCENT) return makeValidPayload(i);

  switch (i % 4) {
    case 0:
      return '{"id":"broken"';
    case 1:
      return JSON.stringify({
        id: `u_${i}`,
        displayName: `User ${i}`,
        age: 33,
        roles: ["user"],
        marketingOptIn: true,
      });
    case 2:
      return JSON.stringify({
        id: `u_${i}`,
        email: `u_${i}@knitting.dev`,
        displayName: "x",
        age: "unknown",
        roles: ["user"],
      });
    default:
      return JSON.stringify({
        id: `u_${i}`,
        email: `u_${i}@knitting.dev`,
        displayName: `User ${i}`,
        age: 31,
        roles: ["owner"],
      });
  }
}

function makeBatches(payloads: string[], batchSize: number): string[][] {
  const batches: string[][] = [];
  for (let i = 0; i < payloads.length; i += batchSize) {
    batches.push(payloads.slice(i, i + batchSize));
  }
  return batches;
}

function mergeSummary(
  a: ValidationSummary,
  b: ValidationSummary,
): ValidationSummary {
  return {
    valid: a.valid + b.valid,
    invalid: a.invalid + b.invalid,
  };
}

function runHostBatches(payloadBatches: string[][]): ValidationSummary {
  let totals: ValidationSummary = { valid: 0, invalid: 0 };

  for (let i = 0; i < payloadBatches.length; i++) {
    totals = mergeSummary(
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
    totals = mergeSummary(totals, results[i]!);
  }
  return totals;
}

function sameSummary(a: ValidationSummary, b: ValidationSummary): boolean {
  return a.valid === b.valid && a.invalid === b.invalid;
}

function printMetrics(name: string, ms: number): void {
  const secs = Math.max(1e-9, ms / 1000);
  const rps = REQUESTS / secs;
  console.log(`${name} took       : ${ms.toFixed(2)} ms`);
  console.log(`${name} throughput : ${rps.toFixed(0)} req/s`);
}

async function main() {
  const payloads = new Array<string>(REQUESTS);
  for (let i = 0; i < REQUESTS; i++) {
    payloads[i] = makePayload(i);
  }
  const payloadBatches = makeBatches(payloads, BATCH);

  const pool = createPool({
    threads: THREADS,
  })({ parseAndValidateBatchFast });

  try {
    const hostStart = performance.now();
    const hostTotals = runHostBatches(payloadBatches);
    const hostMs = performance.now() - hostStart;

    const workerStart = performance.now();
    const workerTotals = await runWorkerBatches(
      pool.call.parseAndValidateBatchFast,
      payloadBatches,
    );
    const workerMs = performance.now() - workerStart;

    if (!sameSummary(hostTotals, workerTotals)) {
      throw new Error("Host and worker validation counts differ.");
    }

    const uplift = (hostMs / Math.max(1e-9, workerMs) - 1) * 100;

    console.log("Zod parse+validate quick bench");
    console.log("workload: JSON.parse + UserSchema.safeParse");
    console.log("requests:", REQUESTS.toLocaleString());
    console.log("invalid rate:", `${INVALID_PERCENT}%`);
    console.log("batch:", BATCH);
    console.log("threads:", THREADS);
    console.log("");
    printMetrics("host", hostMs);
    printMetrics("knitting", workerMs);
    console.log(`uplift         : ${uplift.toFixed(1)}%`);
    console.log(
      "verified counts:",
      `${hostTotals.valid}/${hostTotals.invalid} / ${workerTotals.valid}/${workerTotals.invalid}`,
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
