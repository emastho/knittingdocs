import { transform } from "esbuild";
import { minify } from "terser";
import { createPool, isMain } from "knitting";

export const build = async (source: string): Promise<string> => {
  const { code } = await transform(source, { loader: "ts" });
  return (await minify(code)).code ?? "";
};

if (isMain) {
  const pool = createPool({
    threads: 4,
    permission: { mode: "strict", allowImport: true, run: true },
    worker: { maxAwaitingTasks: 2 },
  })({ build });

  const sources = [33, 42, 73, 99].map((answer) =>
    "const answer: number = " + answer + "; console.log(answer);"
  );

  try {
    const output = await Promise.all(
      sources.map((source) => pool.call.build(source)),
    );
    console.log(output);
  } finally {
    await pool.shutdown();
  }
}
