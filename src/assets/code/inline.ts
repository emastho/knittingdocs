import { isMain, task } from "@vixeny/knitting";

export const world = task({
  f: (args: string) => args + " world",
}).createPool({
  threads: 2,
  inliner: {
    position: "last",
  },
});

if (isMain) {
  Promise.all(
    Array.from({
      length: 4,
    }).map(() => world.call("hello")),
  )
    .then(console.log)
    .finally(world.shutdown);
}
