import { createPool, isMain, task } from "knitting";

// Wrap a function with task() when you want options like a timeout.
// This call is too slow, so it falls back to the default instead of hanging.
export const slow = task({
  timeout: { time: 100, default: "timed out" },
  f: async (name: string) => {
    await new Promise((resolve) => setTimeout(resolve, 1_000));
    return `hello ${name}`;
  },
});

if (isMain) {
  using pool = createPool({ threads: 1 })({ slow });

  console.log(await pool.call.slow("knitting")); // timed out
}
