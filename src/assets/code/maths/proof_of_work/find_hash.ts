import { task } from "knitting";

type HashJob = readonly [
  prefix: string,
  start: number,
  count: number,
  step: number,
  zeroes: number,
];

export type HashResult = {
  nonce: number | null;
  hash: string | null;
  tested: number;
  aborted: boolean;
};

const encoder = new TextEncoder();

export const findHash = task<
  HashJob,
  HashResult,
  { readonly hasAborted: true }
>({
  abortSignal: { hasAborted: true },
  f: async ([prefix, start, count, step, zeroes], signal) => {
    let nonce = start;

    for (let i = 0; i < count; i++, nonce += step) {
      if (signal.hasAborted()) {
        return { nonce: null, hash: null, tested: i, aborted: true };
      }

      const input = encoder.encode(`${prefix}:${nonce}`);
      const bytes = new Uint8Array(
        await crypto.subtle.digest("SHA-256", input),
      );

      if (signal.hasAborted()) {
        return { nonce: null, hash: null, tested: i + 1, aborted: true };
      }

      if (hasLeadingZeroes(bytes, zeroes)) {
        return {
          nonce,
          hash: toHex(bytes),
          tested: i + 1,
          aborted: false,
        };
      }
    }

    return { nonce: null, hash: null, tested: count, aborted: false };
  },
});

function hasLeadingZeroes(bytes: Uint8Array, zeroes: number): boolean {
  const fullBytes = Math.floor(zeroes / 2);

  for (let index = 0; index < fullBytes; index++) {
    if (bytes[index] !== 0) return false;
  }

  return zeroes % 2 === 0 || (bytes[fullBytes]! & 0xf0) === 0;
}

function toHex(bytes: Uint8Array): string {
  return Array.from(bytes, (byte) => byte.toString(16).padStart(2, "0")).join(
    "",
  );
}
