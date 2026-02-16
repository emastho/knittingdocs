import { createPool, isMain } from "@vixeny/knitting";
import {
  buildPayloads,
  parseAndValidate,
  parseAndValidateHost,
  type ParseValidateResult,
} from "./utils.ts";

const THREADS = 2;
const REQUESTS = 20_000;
const INVALID_PERCENT = 15;

type Summary = {
  valid: number;
  invalid: number;
  sampleIssues: string[];
};

function summarize(results: ParseValidateResult[]): Summary {
  let valid = 0;
  let invalid = 0;
  const sampleIssues: string[] = [];

  for (let i = 0; i < results.length; i++) {
    const result = results[i]!;
    if (result.ok) {
      valid++;
      continue;
    }

    invalid++;
    if (sampleIssues.length < 3 && result.issues.length > 0) {
      sampleIssues.push(result.issues[0]!);
    }
  }

  return { valid, invalid, sampleIssues };
}

function runHost(payloads: string[]): Summary {
  const results = payloads.map((payload) => parseAndValidateHost(payload));
  return summarize(results);
}

async function runWorkers(payloads: string[]): Promise<Summary> {
  const pool = createPool({ threads: THREADS })({ parseAndValidate });

  try {
    const jobs: Promise<ParseValidateResult>[] = [];
    for (let i = 0; i < payloads.length; i++) {
      jobs.push(pool.call.parseAndValidate(payloads[i]!));
    }

    const results = await Promise.all(jobs);
    return summarize(results);
  } finally {
    pool.shutdown();
  }
}

function printSummary(mode: string, summary: Summary, ms: number): void {
  const secs = Math.max(1e-9, ms / 1000);
  const rps = REQUESTS / secs;

  console.log(mode);
  console.log("requests    :", REQUESTS.toLocaleString());
  console.log("invalidRate :", `${INVALID_PERCENT}%`);
  console.log("valid       :", summary.valid.toLocaleString());
  console.log("invalid     :", summary.invalid.toLocaleString());
  console.log("took        :", `${ms.toFixed(2)} ms`);
  console.log("throughput  :", `${rps.toFixed(0)} req/s`);

  if (summary.sampleIssues.length > 0) {
    console.log("sampleIssues:", summary.sampleIssues.join(" | "));
  }
}

async function main() {
  const payloads = buildPayloads(REQUESTS, INVALID_PERCENT);

  const hostStart = performance.now();
  const hostSummary = runHost(payloads);
  const hostMs = performance.now() - hostStart;

  const workerStart = performance.now();
  const workerSummary = await runWorkers(payloads);
  const workerMs = performance.now() - workerStart;

  const uplift = (hostMs / Math.max(1e-9, workerMs) - 1) * 100;

  console.log("JSON parse + schema validation");
  console.log(`threads: ${THREADS}`);
  console.log("");
  printSummary("host", hostSummary, hostMs);
  console.log("");
  printSummary("knitting", workerSummary, workerMs);
  console.log("");
  console.log(`uplift: ${uplift.toFixed(1)}%`);
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
