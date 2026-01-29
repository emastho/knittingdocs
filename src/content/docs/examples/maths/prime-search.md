---
title: Prime search
description: Split a range across workers and merge results.
sidebar:
  order: 5
---

```ts
import { createPool, isMain, task } from "@vixeny/knitting";

export const primesInRange = task<[number, number], number[]>({
  f: async ([start, end]) => {
    const primes: number[] = [];
    if (end < 2) return primes;
    if (start <= 2) primes.push(2);

    let n = Math.max(3, start + (start % 2 === 0 ? 1 : 0));
    for (; n <= end; n += 2) {
      const sqrt = Math.floor(Math.sqrt(n));
      let isPrime = true;
      for (let i = 3; i <= sqrt; i += 2) {
        if (n % i === 0) {
          isPrime = false;
          break;
        }
      }
      if (isPrime) primes.push(n);
    }

    return primes;
  },
});

const { call, fastCall, send, shutdown } = createPool({
  threads: 3,
})({ primesInRange });

if (isMain) {
  const LIMIT = 1_000_000;
  const CHUNK = 10_000;
  const tasks: Promise<number[]>[] = [];

  for (let start = 2; start <= LIMIT; start += CHUNK) {
    const end = Math.min(start + CHUNK - 1, LIMIT);
    tasks.push(call.primesInRange([start, end]));
  }

  send();

  const t0 = performance.now();
  const chunked = await Promise.all(tasks);
  const primes = chunked.flat().sort((a, b) => a - b);

  console.log(`Found ${primes.length} primes <= ${LIMIT}`);
  console.log(`Elapsed: ${performance.now() - t0} ms`);
  console.log("Largest prime:", primes.at(-1));

  const small = await fastCall.primesInRange([2, 30]);
  console.log("Primes between 2 and 30:", small);

  shutdown();
}
```
