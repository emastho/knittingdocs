const isWorkerScope = () => {
  const scopeCtor = globalThis.WorkerGlobalScope;
  if (typeof scopeCtor !== "function") return false;

  try {
    return globalThis instanceof scopeCtor;
  } catch {
    return false;
  }
};

const workerSnapshot = () => ({
  inWorker: isWorkerScope(),
  crossOriginIsolated: globalThis.crossOriginIsolated === true,
  hasSharedArrayBuffer: typeof SharedArrayBuffer === "function",
  hasAtomics: typeof Atomics === "object",
  locationHref:
    typeof globalThis.location?.href === "string"
      ? globalThis.location.href
      : null,
});

export const browserRoundTripImported = async (payload) => {
  const text = typeof payload?.text === "string" ? payload.text : "";
  const numbers = Array.isArray(payload?.numbers)
    ? payload.numbers.map((value) => {
        const parsed = Number(value);
        return Number.isFinite(parsed) ? parsed : 0;
      })
    : [];

  return {
    ok: true,
    api: "importTask",
    moduleHref: import.meta.url,
    receivedAt: new Date().toISOString(),
    worker: workerSnapshot(),
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
};
