import { createPool, isMain, task } from "@vixeny/knitting";

export const double = task({
  f: (n: number) => n * 2,
});

export const square = task({
  f: (n: number) => n * n,
});

const { call, shutdown } = createPool({
  threads: 2,
  inliner: { position: "first", batchSize: 2 },
})({ double, square });

if (isMain) {
  const jobs = Array.from({ length: 5 }, (_, i) => i + 1).map(async (n) => {
    const d = await call.double(n);
    return call.square(d);
  });

  Promise.all(jobs)
    .then((results) => console.log(results))
    .finally(shutdown);
}
