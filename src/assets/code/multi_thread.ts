import { createPool, isMain } from "knitting";

export const hello = () => "hello ";
export const world = (prefix: string) => `${prefix}world!`;

if (isMain) {
  using pool = createPool({ threads: 2 })({ hello, world });

  // call.hello() returns a promise; Knitting resolves it before world runs.
  const lines = await Promise.all(
    Array.from({ length: 3 }, () => pool.call.world(pool.call.hello())),
  );

  console.log(lines.join(" ")); // hello world! hello world! hello world!
}
