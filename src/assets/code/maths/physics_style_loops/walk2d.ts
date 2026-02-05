import { task } from "@vixeny/knitting";

type Args = readonly [
  seed: number,
  runs: number,
  maxSteps: number,
  radius: number,
  dirPow2?: number, // optional: directions table size = 2^dirPow2 (default 10 => 1024)
];

type Result = {
  escaped: number;
  totalRuns: number;
  sumSteps: number; // sum of steps taken until escape (only for escaped runs)
  sumSteps2: number; // sum of steps^2 (only for escaped runs)
};

// Fast deterministic RNG (xorshift32)
function xorshift32(state: number): number {
  state |= 0;
  state ^= state << 13;
  state ^= state >>> 17;
  state ^= state << 5;
  return state | 0;
}

// Precompute direction tables (module-scope = done once per worker)
function makeDirs(pow2: number) {
  const n = 1 << pow2;
  const xs = new Float64Array(n);
  const ys = new Float64Array(n);
  const twoPi = Math.PI * 2;
  for (let i = 0; i < n; i++) {
    const a = (i * twoPi) / n;
    xs[i] = Math.cos(a);
    ys[i] = Math.sin(a);
  }
  return { xs, ys, mask: n - 1 };
}

// Default table: 1024 directions
const DEFAULT_DIR_POW2 = 10;
let DIRS = makeDirs(DEFAULT_DIR_POW2);

export const walkChunk = task<Args, Result>({
  f: ([seed, runs, maxSteps, radius, dirPow2]) => {
    if (dirPow2 && dirPow2 !== DEFAULT_DIR_POW2) {
      // Rare path: allow custom resolution if you want
      DIRS = makeDirs(dirPow2 | 0);
    }

    const r2Limit = radius * radius;

    let s = seed | 0;
    let escaped = 0;
    let sumSteps = 0;
    let sumSteps2 = 0;

    const xs = DIRS.xs;
    const ys = DIRS.ys;
    const mask = DIRS.mask;

    for (let run = 0; run < runs; run++) {
      let x = 0.0;
      let y = 0.0;

      for (let step = 1; step <= maxSteps; step++) {
        s = xorshift32(s);
        const idx = s & mask;

        x += xs[idx];
        y += ys[idx];

        const r2 = x * x + y * y;
        if (r2 >= r2Limit) {
          escaped++;
          sumSteps += step;
          sumSteps2 += step * step;
          break;
        }
      }
    }

    return { escaped, totalRuns: runs, sumSteps, sumSteps2 };
  },
});
