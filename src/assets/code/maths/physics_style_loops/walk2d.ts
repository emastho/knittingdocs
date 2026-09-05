import { task } from "knitting";

type WalkJob = readonly [
  seed: number,
  runs: number,
  maxSteps: number,
  radius: number,
];

type WalkResult = {
  escaped: number;
  totalRuns: number;
  sumSteps: number;
  sumSteps2: number;
};

function xorshift32(state: number): number {
  state |= 0;
  state ^= state << 13;
  state ^= state >>> 17;
  state ^= state << 5;
  return state | 0;
}

export const walkChunk = task<WalkJob, WalkResult>({
  f: ([seed, runs, maxSteps, radius]) => {
    let state = seed | 0;
    let escaped = 0;
    let sumSteps = 0;
    let sumSteps2 = 0;
    const radiusSquared = radius * radius;

    for (let run = 0; run < runs; run++) {
      let x = 0;
      let y = 0;

      for (let step = 1; step <= maxSteps; step++) {
        state = xorshift32(state);

        switch (state & 3) {
          case 0:
            x++;
            break;
          case 1:
            x--;
            break;
          case 2:
            y++;
            break;
          default:
            y--;
        }

        if (x * x + y * y >= radiusSquared) {
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
