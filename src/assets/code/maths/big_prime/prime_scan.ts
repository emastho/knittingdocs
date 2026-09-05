import { task } from "knitting";

type PrimeJob = readonly [
  start: string,
  count: number,
  step: number,
  rounds: number,
];

export type ScanResult = {
  prime: string | null;
  tested: number;
  aborted: boolean;
};

export const scanForProbablePrime = task<
  PrimeJob,
  ScanResult,
  { readonly hasAborted: true }
>({
  abortSignal: { hasAborted: true },
  f: ([start, count, step, rounds], signal) => {
    let candidate = BigInt(start);
    const increment = BigInt(step);

    for (let i = 0; i < count; i++) {
      if (signal.hasAborted()) {
        return { prime: null, tested: i, aborted: true };
      }

      if (isProbablePrime(candidate, rounds)) {
        return { prime: candidate.toString(), tested: i + 1, aborted: false };
      }

      candidate += increment;
    }

    return { prime: null, tested: count, aborted: false };
  },
});

function modPow(base: bigint, exponent: bigint, modulus: bigint): bigint {
  let result = 1n;
  let value = base % modulus;
  let power = exponent;

  while (power > 0n) {
    if ((power & 1n) === 1n) result = (result * value) % modulus;
    value = (value * value) % modulus;
    power >>= 1n;
  }

  return result;
}

const smallPrimes = [
  3n,
  5n,
  7n,
  11n,
  13n,
  17n,
  19n,
  23n,
  29n,
  31n,
  37n,
];

const bases = [
  2n,
  325n,
  9_375n,
  28_178n,
  450_775n,
  9_780_504n,
  1_795_265_022n,
];

function isProbablePrime(candidate: bigint, rounds: number): boolean {
  if (candidate < 2n) return false;
  if (candidate === 2n || candidate === 3n) return true;
  if ((candidate & 1n) === 0n) return false;

  for (const prime of smallPrimes) {
    if (candidate === prime) return true;
    if (candidate % prime === 0n) return false;
  }

  let oddPart = candidate - 1n;
  let powersOfTwo = 0;
  while ((oddPart & 1n) === 0n) {
    oddPart >>= 1n;
    powersOfTwo++;
  }

  for (let round = 0; round < rounds; round++) {
    const base = (bases[round % bases.length] % (candidate - 3n)) + 2n;
    let value = modPow(base, oddPart, candidate);

    if (value === 1n || value === candidate - 1n) continue;

    let passed = false;
    for (let power = 1; power < powersOfTwo; power++) {
      value = (value * value) % candidate;
      if (value === candidate - 1n) {
        passed = true;
        break;
      }
    }

    if (!passed) return false;
  }

  return true;
}
