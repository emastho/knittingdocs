import { createPool, isMain } from "@vixeny/knitting";
import {
  buildDemoRevalidateRequests,
  type RenewalSummary,
  revalidateToken,
  revalidateTokenHost,
  summarizeJsonResponses,
} from "./jwt_revalidation.ts";

const THREADS = 2;
const REQUESTS = 25_000;
const INVALID_PERCENT = 10;

async function runHost(rawRequests: string[]): Promise<RenewalSummary> {
  const outputs = new Array<string>(rawRequests.length);
  for (let i = 0; i < rawRequests.length; i++) {
    outputs[i] = await revalidateTokenHost(rawRequests[i]!);
  }
  return summarizeJsonResponses(outputs);
}

async function runWorkers(rawRequests: string[]): Promise<RenewalSummary> {
  const pool = createPool({ threads: THREADS })({ revalidateToken });
  try {
    const jobs: Promise<string>[] = [];
    for (let i = 0; i < rawRequests.length; i++) {
      jobs.push(pool.call.revalidateToken(rawRequests[i]!));
    }

    const outputs = await Promise.all(jobs);
    return summarizeJsonResponses(outputs);
  } finally {
    pool.shutdown();
  }
}

function printSummary(mode: string, totals: RenewalSummary, ms: number): void {
  const seconds = Math.max(1e-9, ms / 1000);
  const rps = REQUESTS / seconds;

  console.log(mode);
  console.log("requests      :", REQUESTS.toLocaleString());
  console.log("invalid rate  :", `${INVALID_PERCENT}%`);
  console.log("accepted      :", totals.ok.toLocaleString());
  console.log("renewed       :", totals.renewed.toLocaleString());
  console.log("rejected      :", totals.rejected.toLocaleString());
  console.log("output bytes  :", totals.outputBytes.toLocaleString());
  console.log("took          :", `${ms.toFixed(2)} ms`);
  console.log("throughput    :", `${rps.toFixed(0)} req/s`);
}

async function main() {
  const rawRequests = await buildDemoRevalidateRequests({
    count: REQUESTS,
    invalidPercent: INVALID_PERCENT,
  });

  const hostStart = performance.now();
  const hostTotals = await runHost(rawRequests);
  const hostMs = performance.now() - hostStart;

  const workerStart = performance.now();
  const workerTotals = await runWorkers(rawRequests);
  const workerMs = performance.now() - workerStart;

  const uplift = (hostMs / Math.max(1e-9, workerMs) - 1) * 100;

  console.log("JWT token revalidation");
  console.log(`threads: ${THREADS}`);
  console.log("");
  printSummary("host", hostTotals, hostMs);
  console.log("");
  printSummary("knitting", workerTotals, workerMs);
  console.log("");
  console.log(`uplift: ${uplift.toFixed(1)}%`);
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
