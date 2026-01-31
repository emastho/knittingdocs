import { isMain, task } from "@vixeny/knitting";

export const world = task({
  f: (args: string) => args + " world",
}).createPool();

if (isMain) {
  world.call("hello")
    .then(console.log).finally(world.shutdown);
}
