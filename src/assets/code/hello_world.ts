import { createPool, isMain } from "knitting";

// A task is just an exported function the workers can run.
export const greet = (name: string) => `hello ${name}`;

if (isMain) {
  // `using` shuts the pool down automatically when this block ends.
  using pool = createPool({ threads: 1 })({ greet });

  console.log(await pool.call.greet("knitting")); // hello knitting
}
