import { createPool, isMain } from "knitting";

export const countWords = (text: string) => {
  return text.match(/\S+/g)?.length ?? 0;
};

if (isMain) {
  using pool = createPool({ threads: 2 })({ countWords });

  // Small fixtures here; try this with your own documents.
  const counts = await Promise.all([
    pool.call.countWords("workers keep apps responsive"),
    pool.call.countWords("one function, another thread"),
  ]);

  console.log(counts); // [4, 4]
}
