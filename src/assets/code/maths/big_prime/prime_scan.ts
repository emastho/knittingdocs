import { task } from "@vixeny/knitting";

/**
 * Payload-safe:
 * - args: strings + numbers only
 * - return: numbers + strings only
 * This avoids any accidental BigInt/number mixing at the transport boundary.
 */

// args: [startOddStr, count, stepNum, offsetNum, rounds]
export const scanForProbablePrime = task<
  [string, number, number, number, number],
  // ret: [found(0/1), primeStrOrEmpty, tested]
  [number, string, number]
>({
  f: ([startOddStr, count, stepNum, offsetNum, rounds]) => {
    // Convert once, keep everything BigInt inside.
    let x = BigInt(startOddStr) + BigInt(offsetNum);
    if ((x & 1n) === 0n) x += 1n;

    const step = BigInt(stepNum);
    const rds = rounds | 0;

    for (let i = 0; i < count; i++) {
      if (isProbablePrime(x, rds)) return [1, x.toString(), i + 1];
      x += step;
    }
    return [0, "", count];
  },
});

function modPow(base: bigint, exp: bigint, mod: bigint): bigint {
  let r = 1n;
  let b = base % mod;
  let e = exp; // must be bigint

  while (e > 0n) {
    if ((e & 1n) === 1n) r = (r * b) % mod;
    e >>= 1n;
    if (e) b = (b * b) % mod;
  }
  return r;
}

const small = [3n, 5n, 7n, 11n, 13n, 17n, 19n, 23n, 29n, 31n, 37n];
const bases = [2n, 325n, 9375n, 28178n, 450775n, 9780504n, 1795265022n];

function isProbablePrime(n: bigint, rounds: number): boolean {
  if (n < 2n) return false;
  if (n === 2n || n === 3n) return true;
  if ((n & 1n) === 0n) return false;

  // quick small-prime filter
  for (const p of small) {
    if (n === p) return true;
    if (n % p === 0n) return false;
  }

  // n-1 = d * 2^s
  let d = n - 1n;
  let s = 0;
  while ((d & 1n) === 0n) {
    d >>= 1n;
    s++;
  }

  // good practical bases (still "probable prime" for 65-bit+)

  const rds = rounds | 0;
  for (let i = 0; i < rds; i++) {
    const a = (bases[i % bases.length] % (n - 3n)) + 2n; // [2, n-2]
    let x = modPow(a, d, n);

    if (x === 1n || x === n - 1n) continue;

    let composite = true;
    for (let r = 1; r < s; r++) {
      x = (x * x) % n;
      if (x === n - 1n) {
        composite = false;
        break;
      }
    }
    if (composite) return false;
  }

  return true;
}
