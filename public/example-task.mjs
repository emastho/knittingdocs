import { task } from "@vixeny/knitting";

// Example CPU-oriented task: safe single-argument tuple input.
export const add = task({
  f: ([a, b]) => a + b,
});

// Example text-transform task: object input and object output.
export const wordStats = task({
  f: ({ text }) => {
    const cleaned = String(text ?? "").trim();
    if (!cleaned) return { words: 0, chars: 0 };

    const words = cleaned.split(/\s+/).length;
    const chars = cleaned.length;
    return { words, chars };
  },
});
