import { createPool, isMain, task } from "@vixeny/knitting";

export const hello = task({
  f: () => "hello ",
});

export const world = task({
  f: (prefix: string) => `${prefix}world!`,
});

const { call, shutdown } = createPool({ threads: 2 })({
  hello,
  world,
});

if (isMain) {
  Promise.all(Array.from({ length: 5 }, () => call.world(call.hello())))
    .then((results) => console.log(results.join(" ")))
    .finally(shutdown);
}
