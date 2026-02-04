import { createPool, isMain } from "@vixeny/knitting";
import { solveTspGsa } from "./tsp_gsa.ts";

function intArg(name: string, fallback: number) {
  const i = process.argv.indexOf(`--${name}`);
  if (i !== -1 && i + 1 < process.argv.length) {
    const v = Number(process.argv[i + 1]);
    if (Number.isFinite(v) && v > 0) return Math.floor(v);
  }
  return fallback;
}

const THREADS = intArg("threads", 7);
const RESTARTS = intArg("restarts", 64);
const N = intArg("cities", 64);
const POP = intArg("pop", 10);
const ITERS = intArg("iters", 10);

const worldSeed = intArg("worldSeed", 123456);
const seedBase = (Date.now() | 0) ^ 0x9e3779b9;

const { call, send, shutdown } = createPool({
  threads: THREADS,
  balancer: "firstIdle",
})({ solveTspGsa });

function validateTour(tour: number[], n: number) {
  if (tour.length !== n) throw new Error(`tour length ${tour.length} != ${n}`);
  const seen = new Uint8Array(n);
  for (const v of tour) {
    if ((v | 0) !== v) throw new Error(`non-int city id: ${v}`);
    if (v < 0 || v >= n) throw new Error(`bad city id: ${v}`);
    if (seen[v]) throw new Error(`duplicate city: ${v}`);
    seen[v] = 1;
  }
}

/* ---------- Host recompute must match worker exactly ---------- */

function xorshift32(s: number): number {
  s |= 0;
  s ^= s << 13;
  s ^= s >>> 17;
  s ^= s << 5;
  return s | 0;
}

const INV_U32 = 2.3283064365386963e-10; // 1 / 2^32

function makeCities(worldSeed: number, n: number): Float64Array {
  // coords: [x0,y0,x1,y1,...] in [0,1)
  const coords = new Float64Array(n * 2);
  let s = worldSeed | 0;
  for (let i = 0; i < n; i++) {
    s = xorshift32(s);
    coords[i * 2 + 0] = (s >>> 0) * INV_U32;
    s = xorshift32(s);
    coords[i * 2 + 1] = (s >>> 0) * INV_U32;
  }
  return coords;
}

function makeDistMatrix(coords: Float64Array, n: number): Float32Array {
  const d = new Float32Array(n * n);
  for (let i = 0; i < n; i++) {
    const xi = coords[i * 2 + 0];
    const yi = coords[i * 2 + 1];
    for (let j = i + 1; j < n; j++) {
      const dx = xi - coords[j * 2 + 0];
      const dy = yi - coords[j * 2 + 1];
      const dist = Math.hypot(dx, dy);
      d[i * n + j] = dist;
      d[j * n + i] = dist;
    }
  }
  return d;
}

function recomputeLen(tour: number[], dist: Float32Array, n: number): number {
  let s = 0;
  let prev = tour[0];
  for (let i = 1; i < n; i++) {
    const cur = tour[i];
    s += dist[prev * n + cur];
    prev = cur;
  }
  s += dist[prev * n + tour[0]];
  return s;
}

/* ---------- Random pick + random baseline tour ---------- */

function pickRandomIndex(len: number, seed: number): number {
  // deterministic “random” based on seed
  const s = xorshift32(seed | 0);
  return (s >>> 0) % len;
}

function makeRandomTour(n: number, seed: number): number[] {
  // Fisher–Yates shuffle
  const tour = new Array<number>(n);
  for (let i = 0; i < n; i++) tour[i] = i;

  let s = seed | 0;
  for (let i = n - 1; i > 0; i--) {
    s = xorshift32(s);
    const j = (s >>> 0) % (i + 1);
    const tmp = tour[i];
    tour[i] = tour[j];
    tour[j] = tmp;
  }
  return tour;
}

/* ------------------------------------------------------------ */

async function main() {
  const jobs: Promise<{ bestLen: number; bestTour: number[] }>[] = [];

  for (let r = 0; r < RESTARTS; r++) {
    const runSeed = (seedBase + r * 0x6d2b79f5) | 0;
    jobs.push(call.solveTspGsa([worldSeed, runSeed, N, POP, ITERS]));
  }

  // Batch dispatch
  send();

  const results = await Promise.all(jobs);
  if (results.length === 0) throw new Error("no results (unexpected)");

  // Find best + worst correctly
  let best = results[0];
  let worst = results[0];
  for (const res of results) {
    if (res.bestLen < best.bestLen) best = res;
    if (res.bestLen > worst.bestLen) worst = res;
  }

  // Build world once on host for verification
  const coords = makeCities(worldSeed, N);
  const dist = makeDistMatrix(coords, N);

  function checkResult(label: string, res: { bestLen: number; bestTour: number[] }) {
    validateTour(res.bestTour, N);
    const recomputed = recomputeLen(res.bestTour, dist, N);
    const delta = recomputed - res.bestLen;

    if (!Number.isFinite(res.bestLen) || res.bestLen < 0) {
      throw new Error(`${label}: bestLen invalid: ${res.bestLen}`);
    }
    if (Math.abs(delta) > 1e-6) {
      throw new Error(`${label}: length mismatch (delta=${delta}). Host generator != worker generator?`);
    }

    return { recomputed, delta };
  }

  // Randomly choose ONE run result and verify it too (not just the best)
  const randIdx = pickRandomIndex(results.length, seedBase ^ 0xA5A5A5A5);
  const randomRes = results[randIdx];

  const bestCheck = checkResult("best", best);
  const worstCheck = checkResult("worst", worst);
  const randomCheck = checkResult(`randomRun[#${randIdx}]`, randomRes);

  // Random baseline tour (not from solver)
  const randomTour = makeRandomTour(N, seedBase ^ 0xC0FFEE);
  validateTour(randomTour, N);
  const randomLen = recomputeLen(randomTour, dist, N);

  console.log("TSP via gravity (GSA) + 2-opt");
  console.log("threads      :", THREADS);
  console.log("restarts     :", RESTARTS);
  console.log("cities       :", N);
  console.log("pop          :", POP);
  console.log("iters        :", ITERS);
  console.log("worldSeed    :", worldSeed);
  console.log("---");
  console.log("bestLen      :", best.bestLen);
  console.log("worstLen     :", worst.bestLen);
  console.log(`randomRunLen :`, randomRes.bestLen, `(picked index ${randIdx})`);
  console.log("randomTourLen:", randomLen);
  console.log("---");
  console.log("best delta   :", bestCheck.delta);
  console.log("worst delta  :", worstCheck.delta);
  console.log("random delta :", randomCheck.delta);

  console.log(
    "tour head    :",
    best.bestTour.slice(0, Math.min(16, best.bestTour.length)).join(", "),
    "..."
  );
}

if (isMain) {
  main().finally(shutdown);
}
