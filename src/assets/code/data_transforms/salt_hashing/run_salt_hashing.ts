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
const REQUESTS = Math.max(1, intArg("requests", 4_000));
const ITERATIONS = Math.max(10_000, intArg("iterations", 120_000));
const MISMATCH_PERCENT = Math.max(0, Math.min(95, intArg("mismatch", 5)));
const MODE = strArg("mode", "knitting");

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

async function printPacketSample() {
  const packet = makeHashPacketForIndex(7, ITERATIONS, 32, 16);
  const result = await hashPasswordPacketHost(packet);
  const decoded = decodeHashResultPacket(result);
  console.log("packet sample  : iterations", decoded.iterations);
  console.log("salt(base64)   :", decoded.saltBase64);
  console.log("hash(base64)   :", decoded.hashBase64);
}

async function main() {
  const started = performance.now();
  const summary = MODE === "host" ? await runHost() : await runWorkers();
  const finished = performance.now();

  const tookMs = finished - started;
  const seconds = Math.max(1e-9, tookMs / 1000);
  const ops = REQUESTS / seconds;

  console.log("Password salting + hashing");
  console.log("mode          :", MODE);
  console.log("threads       :", MODE === "host" ? 0 : THREADS);
  console.log("requests      :", REQUESTS.toLocaleString());
  console.log("iterations    :", ITERATIONS.toLocaleString());
  console.log("mismatch rate :", `${MISMATCH_PERCENT}%`);
  console.log("hashed        :", summary.hashed.toLocaleString());
  console.log("verified      :", summary.verified.toLocaleString());
  console.log("mismatched    :", summary.mismatched.toLocaleString());
  console.log("took          :", tookMs.toFixed(2), "ms");
  console.log("throughput    :", ops.toFixed(0), "req/s");

  await printPacketSample();
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
