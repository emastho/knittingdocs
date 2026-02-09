import { createPool, isMain } from "@vixeny/knitting";
import {
  parseAndValidate,
  parseAndValidateHost,
  type ParseValidateResult,
} from "./parse_validate.ts";

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
const REQUESTS = Math.max(1, intArg("requests", 50_000));
const INVALID_PERCENT = Math.max(0, Math.min(95, intArg("invalid", 15)));
const MODE = strArg("mode", "knitting");

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
      return '{"id":"broken"'; // Invalid JSON.
    case 1:
      return JSON.stringify({
        id: `u_${i}`,
        displayName: `User ${i}`,
        age: 33,
        roles: ["user"],
        marketingOptIn: true,
      }); // Missing email.
    case 2:
      return JSON.stringify({
        id: `u_${i}`,
        email: `u_${i}@knitting.dev`,
        displayName: "x",
        age: "unknown",
        roles: ["user"],
      }); // Invalid displayName + age.
    default:
      return JSON.stringify({
        id: `u_${i}`,
        email: `u_${i}@knitting.dev`,
        displayName: `User ${i}`,
        age: 31,
        roles: ["owner"],
      }); // Invalid role.
  }
}

type Summary = {
  valid: number;
  invalid: number;
  sampleIssues: string[];
};

function summarize(results: ParseValidateResult[]): Summary {
  let valid = 0;
  let invalid = 0;
  const sampleIssues: string[] = [];

  for (const result of results) {
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

    pool.send();
    const results = await Promise.all(jobs);
    return summarize(results);
  } finally {
    pool.shutdown();
  }
}

async function main() {
  const payloads = new Array<string>(REQUESTS);
  for (let i = 0; i < REQUESTS; i++) payloads[i] = makePayload(i);

  const started = performance.now();
  const summary = MODE === "host"
    ? runHost(payloads)
    : await runWorkers(payloads);
  const finished = performance.now();

  const tookMs = finished - started;
  const secs = Math.max(1e-9, tookMs / 1000);
  const rps = REQUESTS / secs;

  console.log("JSON parse + schema validation");
  console.log("mode        :", MODE);
  console.log("threads     :", MODE === "host" ? 0 : THREADS);
  console.log("requests    :", REQUESTS.toLocaleString());
  console.log("invalidRate :", `${INVALID_PERCENT}%`);
  console.log("valid       :", summary.valid.toLocaleString());
  console.log("invalid     :", summary.invalid.toLocaleString());
  console.log("took        :", tookMs.toFixed(2), "ms");
  console.log("throughput  :", rps.toFixed(0), "req/s");

  if (summary.sampleIssues.length > 0) {
    console.log("sampleIssues:", summary.sampleIssues.join(" | "));
  }
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
