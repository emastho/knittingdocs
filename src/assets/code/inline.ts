import { createPool, isMain, task } from "@vixeny/knitting";

export const add = task({
  f: ([a, b]: [number, number]) => a + b,
});

const { call, send, shutdown } = createPool({
  threads: 2,
  inliner: { position: "last", batchSize: 4 },
})({ add });

if (isMain) {
  const jobs = Array.from({ length: 8 }, () => call.add([1, 2]));
  send();
  Promise.all(jobs)
    .then((results) => console.log(results))
    .finally(shutdown);
}
