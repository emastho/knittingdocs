import { task } from "@vixeny/knitting";

type ChunkArgs = readonly [seed: number, samples: number];
type ChunkResult = { inside: number; samples: number };

/**
 * Fast, deterministic RNG: xorshift32.
 * (Good enough for Monte Carlo demos, and much faster than Math.random in tight loops.)
 */
function xorshift32(state: number): number {
  state |= 0;
  state ^= state << 13;
  state ^= state >>> 17;
  state ^= state << 5;
  return state | 0;
}

const INV_2_POW_32 = 2.3283064365386963e-10; // 1 / 2^32

export const piChunk = task<ChunkArgs, ChunkResult>({
  f: ([seed, samples]) => {
    let s = seed | 0;
    let inside = 0;

    for (let i = 0; i < samples; i++) {
      s = xorshift32(s);
      const x = ((s >>> 0) * INV_2_POW_32) * 2 - 1;

      s = xorshift32(s);
      const y = ((s >>> 0) * INV_2_POW_32) * 2 - 1;

      const r2 = x * x + y * y;
      if (r2 <= 1) inside++;
    }

    return { inside, samples };
  },
});
