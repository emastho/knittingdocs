import { createPool, isMain } from "knitting";

// Several tasks share one pool. Calls are promises, so you can chain them.
export const double = (n: number) => n * 2;
export const square = (n: number) => n * n;

if (isMain) {
  using pool = createPool({ threads: 2 })({ double, square });

  const results = await Promise.all(
    [1, 2, 3, 4, 5].map(async (n) => pool.call.square(await pool.call.double(n))),
  );

  console.log(results); // [4, 16, 36, 64, 100]
}
