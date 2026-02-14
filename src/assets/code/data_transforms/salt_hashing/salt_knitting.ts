import { createPool, isMain } from "@vixeny/knitting";
import {
  decodeHashResultPacket,
  hashPassword,
  hashPasswordHost,
  hashPasswordPacketHost,
  makeHashPacketForIndex,
  verifyPassword,
  verifyPasswordHost,
} from "./salt_hashing.ts";

const THREADS = 2;
const REQUESTS = 2_000;
const ITERATIONS = 120_000;
const MISMATCH_PERCENT = 5;

type Summary = {
  hashed: number;
  verified: number;
  mismatched: number;
};

function passwordFor(i: number): string {
  return `user-${i.toString(36)}-password`;
}

function expectedPassword(i: number): string {
  if (i % 100 < MISMATCH_PERCENT) return `wrong-${i.toString(36)}-password`;
  return passwordFor(i);
}

async function runHost(): Promise<Summary> {
  let verified = 0;
  let mismatched = 0;

  for (let i = 0; i < REQUESTS; i++) {
    const password = passwordFor(i);
    const hashed = await hashPasswordHost({ password, iterations: ITERATIONS });
    const checked = await verifyPasswordHost({
      password: expectedPassword(i),
      record: hashed.record,
    });

    if (checked.ok) verified++;
    else mismatched++;
  }

  return { hashed: REQUESTS, verified, mismatched };
}

async function runWorkers(): Promise<Summary> {
  const pool = createPool({ threads: THREADS })({
    hashPassword,
    verifyPassword,
  });

  try {
    const hashJobs: Promise<{ record: string }>[] = [];
    for (let i = 0; i < REQUESTS; i++) {
      hashJobs.push(pool.call.hashPassword({
        password: passwordFor(i),
        iterations: ITERATIONS,
      }));
    }

    const hashes = await Promise.all(hashJobs);
    const verifyJobs: Promise<{ ok: boolean }>[] = [];
    for (let i = 0; i < REQUESTS; i++) {
      verifyJobs.push(pool.call.verifyPassword({
        password: expectedPassword(i),
        record: hashes[i]!.record,
      }));
    }

    const checks = await Promise.all(verifyJobs);
    let verified = 0;
    for (let i = 0; i < checks.length; i++) {
      if (checks[i]!.ok) verified++;
    }
    const mismatched = REQUESTS - verified;
    return { hashed: REQUESTS, verified, mismatched };
  } finally {
    pool.shutdown();
  }
}

function printSummary(mode: string, summary: Summary, ms: number): void {
  const seconds = Math.max(1e-9, ms / 1000);
  const ops = REQUESTS / seconds;
  console.log(mode);
  console.log("requests      :", REQUESTS.toLocaleString());
  console.log("iterations    :", ITERATIONS.toLocaleString());
  console.log("mismatch rate :", `${MISMATCH_PERCENT}%`);
  console.log("hashed        :", summary.hashed.toLocaleString());
  console.log("verified      :", summary.verified.toLocaleString());
  console.log("mismatched    :", summary.mismatched.toLocaleString());
  console.log("took          :", `${ms.toFixed(2)} ms`);
  console.log("throughput    :", `${ops.toFixed(0)} req/s`);
}

async function printPacketSample() {
  const packet = makeHashPacketForIndex(7, ITERATIONS, 32, 16);
  const result = await hashPasswordPacketHost(packet);
  const decoded = decodeHashResultPacket(result);
  console.log("packet sample  : iterations", decoded.iterations);
  console.log("salt(base64)   :", decoded.saltBase64);
  console.log("hash(base64)   :", decoded.hashBase64);
}

async function main() {
  const hostStart = performance.now();
  const host = await runHost();
  const hostMs = performance.now() - hostStart;

  const workerStart = performance.now();
  const knitting = await runWorkers();
  const workerMs = performance.now() - workerStart;

  const uplift = (hostMs / Math.max(1e-9, workerMs) - 1) * 100;

  console.log("Password salting + hashing");
  console.log(`threads: ${THREADS}`);
  console.log("");
  printSummary("host", host, hostMs);
  console.log("");
  printSummary("knitting", knitting, workerMs);
  console.log("");
  console.log(`uplift: ${uplift.toFixed(1)}%`);
  await printPacketSample();
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
