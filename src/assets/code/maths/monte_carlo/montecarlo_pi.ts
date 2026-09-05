import { task } from "knitting";

type PiJob = readonly [seed: number, samples: number];

function nextRandom(state: { value: number }): number {
  let value = state.value | 0;
  value ^= value << 13;
  value ^= value >>> 17;
  value ^= value << 5;
  state.value = value;
  return (value >>> 0) / 2 ** 32;
}

export const piChunk = task<PiJob, number>({
  f: ([seed, samples]) => {
    const state = { value: seed };
    let inside = 0;

    for (let i = 0; i < samples; i++) {
      const x = nextRandom(state) * 2 - 1;
      const y = nextRandom(state) * 2 - 1;
      if (x * x + y * y <= 1) inside++;
    }

    return inside;
  },
});
