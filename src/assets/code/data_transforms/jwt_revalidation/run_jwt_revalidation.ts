import { createPool, isMain } from "@vixeny/knitting";
import {
  buildDemoRevalidateRequests,
  type RenewalSummary,
  revalidateToken,
  revalidateTokenHost,
  summarizeJsonResponses,
} from "./jwt_revalidation.ts";

function intArg(name: string, fallback: number): number {
  const i = process.argv.indexOf(`--${name}`);
  if (i !== -1 && i + 1 < process.argv.length) {
    const value = Number(process.argv[i + 1]);
    if (Number.isFinite(value)) return Math.floor(value);
  }
  return fallback;
}

function strArg(name: string, fallback: string): string {
  const i = process.argv.indexOf(`--${name}`);
  if (i !== -1 && i + 1 < process.argv.length) {
    return String(process.argv[i + 1]);
  }
  return fallback;
}

const THREADS = Math.max(1, intArg("threads", 2));
const REQUESTS = Math.max(1, intArg("requests", 25_000));
const INVALID_PERCENT = Math.max(0, Math.min(95, intArg("invalid", 10)));
const MODE = strArg("mode", "knitting");

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

async function main() {
  const rawRequests = await buildDemoRevalidateRequests({
    count: REQUESTS,
    invalidPercent: INVALID_PERCENT,
  });

  const started = performance.now();
  const totals = MODE === "host"
    ? await runHost(rawRequests)
    : await runWorkers(rawRequests);
  const finished = performance.now();

  const tookMs = finished - started;
  const seconds = Math.max(1e-9, tookMs / 1000);
  const rps = REQUESTS / seconds;

  console.log("JWT token revalidation");
  console.log("mode          :", MODE);
  console.log("threads       :", MODE === "host" ? 0 : THREADS);
  console.log("requests      :", REQUESTS.toLocaleString());
  console.log("invalid rate  :", `${INVALID_PERCENT}%`);
  console.log("accepted      :", totals.ok.toLocaleString());
  console.log("renewed       :", totals.renewed.toLocaleString());
  console.log("rejected      :", totals.rejected.toLocaleString());
  console.log("output bytes  :", totals.outputBytes.toLocaleString());
  console.log("took          :", tookMs.toFixed(2), "ms");
  console.log("throughput    :", rps.toFixed(0), "req/s");
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
