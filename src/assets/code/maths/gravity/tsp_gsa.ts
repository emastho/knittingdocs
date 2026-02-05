import { task } from "@vixeny/knitting";

type Args = readonly [
  worldSeed: number, // generates the same city map for all runs
  runSeed: number, // controls the optimizer randomness
  nCities: number,
  popSize: number,
  iters: number,
];

type Result = {
  bestLen: number;
  bestTour: number[];
};

function xorshift32(s: number): number {
  s |= 0;
  s ^= s << 13;
  s ^= s >>> 17;
  s ^= s << 5;
  return s | 0;
}
const INV_U32 = 2.3283064365386963e-10; // 1 / 2^32

function rand01(stateRef: { s: number }): number {
  stateRef.s = xorshift32(stateRef.s);
  return (stateRef.s >>> 0) * INV_U32;
}

function makeCities(worldSeed: number, n: number): Float64Array {
  // coords: [x0,y0,x1,y1,...] in [0,1)
  const coords = new Float64Array(n * 2);
  const st = { s: worldSeed | 0 };
  for (let i = 0; i < n; i++) {
    coords[i * 2 + 0] = rand01(st);
    coords[i * 2 + 1] = rand01(st);
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

function tourLen(dist: Float32Array, n: number, tour: Int32Array): number {
  let sum = 0;
  let prev = tour[0];
  for (let i = 1; i < n; i++) {
    const cur = tour[i];
    sum += dist[prev * n + cur];
    prev = cur;
  }
  sum += dist[prev * n + tour[0]];
  return sum;
}

function decodeKeysToTour(
  keys: Float64Array,
  n: number,
  scratchIdx: number[],
  outTour: Int32Array,
) {
  // scratchIdx contains 0..n-1 and is reused
  scratchIdx.sort((a, b) => keys[a] - keys[b]);
  for (let i = 0; i < n; i++) outTour[i] = scratchIdx[i];
}

const eps = 1e-12;

function twoOpt(dist: Float32Array, n: number, tour: Int32Array): number {
  let best = tourLen(dist, n, tour);

  while (true) {
    let improved = false;

    outer: for (let i = 0; i < n - 1; i++) {
      for (let k = i + 2; k < n; k++) {
        const a = tour[i];
        const b = tour[(i + 1) % n];
        const c = tour[k];
        const d = tour[(k + 1) % n];

        const before = dist[a * n + b] + dist[c * n + d];
        const after = dist[a * n + c] + dist[b * n + d];

        if (after + eps < before) {
          // reverse segment (i+1..k)
          for (let l = i + 1, r = k; l < r; l++, r--) {
            const tmp = tour[l];
            tour[l] = tour[r];
            tour[r] = tmp;
          }

          // delta update is valid because we restart scanning immediately
          best += after - before;

          improved = true;
          break outer;
        }
      }
    }

    if (!improved) break;
  }

  // Safety: compute the true length once (guaranteed non-negative if dist is)
  return tourLen(dist, n, tour);
}

export const solveTspGsa = task<Args, Result>({
  f: ([worldSeed, runSeed, nCities, popSize, iters]) => {
    const n = nCities | 0;
    const pop = popSize | 0;
    const T = iters | 0;

    const coords = makeCities(worldSeed | 0, n);
    const dist = makeDistMatrix(coords, n);

    // Agent states
    const X = new Float64Array(pop * n);
    const V = new Float64Array(pop * n);
    const fit = new Float64Array(pop);
    const mass = new Float64Array(pop);

    const st = { s: runSeed | 0 };

    // Init positions and velocities
    for (let i = 0; i < pop * n; i++) {
      X[i] = rand01(st); // [0,1)
      V[i] = (rand01(st) - 0.5) * 0.1; // small initial velocity
    }

    const scratchIdx: number[] = new Array(n);
    for (let i = 0; i < n; i++) scratchIdx[i] = i;

    const tmpTour = new Int32Array(n);
    const bestTour = new Int32Array(n);
    let bestLen = Infinity;

    // Helpers
    const idxPop: number[] = new Array(pop);
    for (let i = 0; i < pop; i++) idxPop[i] = i;

    const eps = 1e-9;
    const G0 = 100.0;
    const alpha = 20.0;

    // Main loop
    for (let t = 0; t < T; t++) {
      // Evaluate fitness (tour length)
      for (let i = 0; i < pop; i++) {
        const base = i * n;
        decodeKeysToTour(X.subarray(base, base + n), n, scratchIdx, tmpTour);
        const L = tourLen(dist, n, tmpTour);
        fit[i] = L;

        if (L < bestLen) {
          bestLen = L;
          bestTour.set(tmpTour);
        }
      }

      // Sort agents by fitness (ascending)
      idxPop.sort((a, b) => fit[a] - fit[b]);

      const bestF = fit[idxPop[0]];
      const worstF = fit[idxPop[pop - 1]];
      const denom = Math.max(eps, worstF - bestF);

      // Mass for minimization: better fitness => larger mass
      let sumM = 0;
      for (let r = 0; r < pop; r++) {
        const i = idxPop[r];
        const m = (worstF - fit[i]) / denom;
        mass[i] = m;
        sumM += m;
      }
      const invSumM = 1 / Math.max(eps, sumM);
      for (let i = 0; i < pop; i++) mass[i] *= invSumM;

      // K-best shrinks over time
      const K = Math.max(2, (pop * (1 - t / T)) | 0);
      const G = G0 * Math.exp(-alpha * (t / T));

      // Update each agent via gravitational attraction
      for (let ii = 0; ii < pop; ii++) {
        const i = idxPop[ii];
        const Mi = Math.max(eps, mass[i]);
        const baseI = i * n;

        for (let d = 0; d < n; d++) {
          let Fi = 0;

          // Pull from top-K agents
          for (let kk = 0; kk < K; kk++) {
            const j = idxPop[kk];
            if (j === i) continue;

            // Distance between agent vectors (cheap L2)
            const baseJ = j * n;
            let r2 = 0;
            for (let q = 0; q < n; q++) {
              const diff = X[baseJ + q] - X[baseI + q];
              r2 += diff * diff;
            }
            const R = Math.sqrt(r2) + eps;

            const Mj = mass[j];
            const rij = X[baseJ + d] - X[baseI + d];

            // random factor to avoid lockstep collapse
            Fi += rand01(st) * G * (Mi * Mj) * (rij / R);
          }

          // a = F / Mi
          const a = Fi / Mi;

          // velocity + position update
          const idx = baseI + d;
          V[idx] = rand01(st) * V[idx] + a;
          X[idx] = X[idx] + V[idx];

          // keep keys in a reasonable range
          if (X[idx] < -2) X[idx] = -2;
          else if (X[idx] > 3) X[idx] = 3;
        }
      }
    }

    // Local refinement: 2-opt on best tour
    const refined = bestTour.slice() as Int32Array;
    const refinedLen = twoOpt(dist, n, refined);
    if (refinedLen < bestLen) bestLen = refinedLen;

    // Return as plain JS array for safe payload compatibility
    const out: number[] = new Array(n);
    for (let i = 0; i < n; i++) out[i] = refined[i];

    return { bestLen, bestTour: out };
  },
});
