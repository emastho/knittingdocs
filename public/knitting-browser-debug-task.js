import { task } from "./knitting.js";

const isWorkerScope = () => {
  const scopeCtor = globalThis.WorkerGlobalScope;
  if (typeof scopeCtor !== "function") return false;

  try {
    return globalThis instanceof scopeCtor;
  } catch {
    return false;
  }
};

export const browserRoundTrip = task({
  f: async (payload) => {
    const text = typeof payload?.text === "string" ? payload.text : "";
    const numbers = Array.isArray(payload?.numbers)
      ? payload.numbers.map((value) => {
          const parsed = Number(value);
          return Number.isFinite(parsed) ? parsed : 0;
        })
      : [];

    return {
      ok: true,
      receivedAt: new Date().toISOString(),
      worker: {
        inWorker: isWorkerScope(),
        crossOriginIsolated: globalThis.crossOriginIsolated === true,
        hasSharedArrayBuffer: typeof SharedArrayBuffer === "function",
        hasAtomics: typeof Atomics === "object",
        locationHref:
          typeof globalThis.location?.href === "string"
            ? globalThis.location.href
            : null,
      },
      payload: {
        ...payload,
        text,
        numbers,
      },
      transformed: {
        upper: text.toUpperCase(),
        reversed: text.split("").reverse().join(""),
        sum: numbers.reduce((total, value) => total + value, 0),
      },
    };
  },
});
