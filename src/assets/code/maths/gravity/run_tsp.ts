import { createPool, isMain } from "knitting";
import { solveTspGsa } from "./tsp_gsa.ts";

type Options = {
  threads: number;
  restarts: number;
  cities: number;
  population: number;
  iterations: number;
  worldSeed: number;
};

type TspResult = {
  bestLen: number;
  bestTour: number[];
};

function positiveIntArg(name: string, fallback: number): number {
  const index = process.argv.indexOf(`--${name}`);
  const value = index === -1 ? undefined : Number(process.argv[index + 1]);
  return Number.isSafeInteger(value) && value > 0 ? value : fallback;
}

function readOptions(): Options {
  return {
    threads: positiveIntArg("threads", 4),
    restarts: positiveIntArg("restarts", 16),
    cities: positiveIntArg("cities", 32),
    population: positiveIntArg("population", 8),
    iterations: positiveIntArg("iterations", 40),
    worldSeed: positiveIntArg("worldSeed", 123_456),
  };
}

function xorshift32(state: number): number {
  state |= 0;
  state ^= state << 13;
  state ^= state >>> 17;
  state ^= state << 5;
  return state | 0;
}

function makeCities(worldSeed: number, cities: number): Float64Array {
  const coords = new Float64Array(cities * 2);
  let state = worldSeed | 0;

  for (let city = 0; city < cities; city++) {
    state = xorshift32(state);
    coords[city * 2] = (state >>> 0) / 2 ** 32;
    state = xorshift32(state);
    coords[city * 2 + 1] = (state >>> 0) / 2 ** 32;
  }

  return coords;
}

function makeDistances(coords: Float64Array, cities: number): Float32Array {
  const distances = new Float32Array(cities * cities);

  for (let left = 0; left < cities; left++) {
    const leftX = coords[left * 2];
    const leftY = coords[left * 2 + 1];

    for (let right = left + 1; right < cities; right++) {
      const dx = leftX - coords[right * 2];
      const dy = leftY - coords[right * 2 + 1];
      const distance = Math.hypot(dx, dy);
      distances[left * cities + right] = distance;
      distances[right * cities + left] = distance;
    }
  }

  return distances;
}

function tourLength(
  tour: number[],
  distances: Float32Array,
  cities: number,
): number {
  let length = 0;

  for (let index = 0; index < cities; index++) {
    const from = tour[index];
    const to = tour[(index + 1) % cities];
    length += distances[from * cities + to];
  }

  return length;
}

function validateTour(tour: number[], cities: number): void {
  if (tour.length !== cities) {
    throw new Error(`expected ${cities} cities, got ${tour.length}`);
  }

  const seen = new Uint8Array(cities);
  for (const city of tour) {
    if (!Number.isInteger(city) || city < 0 || city >= cities) {
      throw new Error(`invalid city index: ${city}`);
    }
    if (seen[city]) throw new Error(`city appears twice: ${city}`);
    seen[city] = 1;
  }
}

async function main() {
  const options = readOptions();
  const worldSeed = options.worldSeed | 0;
  const runSeed = 0x51f15e5;

  using pool = createPool({ threads: options.threads })({ solveTspGsa });

  const started = performance.now();
  const jobs: Promise<TspResult>[] = [];

  for (let restart = 0; restart < options.restarts; restart++) {
    const seed = (runSeed + restart * 0x6d2b_79f5) | 0;
    jobs.push(
      pool.call.solveTspGsa([
        worldSeed,
        seed,
        options.cities,
        options.population,
        options.iterations,
      ]),
    );
  }

  const results = await Promise.all(jobs);
  const best = results.reduce((current, result) =>
    result.bestLen < current.bestLen ? result : current,
  );

  const distances = makeDistances(
    makeCities(worldSeed, options.cities),
    options.cities,
  );
  validateTour(best.bestTour, options.cities);

  const recomputed = tourLength(best.bestTour, distances, options.cities);
  if (Math.abs(recomputed - best.bestLen) > 1e-5) {
    throw new Error(
      `worker length mismatch: ${best.bestLen} vs ${recomputed}`,
    );
  }

  const elapsed = performance.now() - started;

  console.log(`threads:     ${options.threads}`);
  console.log(`cities:      ${options.cities}`);
  console.log(`restarts:    ${options.restarts}`);
  console.log(`population:  ${options.population}`);
  console.log(`iterations:  ${options.iterations}`);
  console.log(`best length: ${best.bestLen.toFixed(3)}`);
  console.log(`tour valid:  yes`);
  console.log(`recomputed:  ${recomputed.toFixed(3)}`);
  console.log(`elapsed:     ${elapsed.toFixed(0)} ms`);
}

if (isMain) {
  await main();
}
