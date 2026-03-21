import { importTask, task } from "./knitting.js";

const TASK_MODULE_HREF = import.meta.url;
const IMPORTED_TASK_MODULE_HREF = new URL(
  "./knitting-browser-debug-imported.js",
  import.meta.url,
).href;

const setStableTaskIdentity = (taskDefinition, at, meta = {}) => {
  taskDefinition.importedFrom = TASK_MODULE_HREF;
  taskDefinition.at = at;
  Object.assign(taskDefinition, meta);
  return taskDefinition;
};

const toUint8Array = (value) => {
  if (value instanceof Uint8Array) return value;

  if (ArrayBuffer.isView(value)) {
    return new Uint8Array(value.buffer, value.byteOffset, value.byteLength);
  }

  if (value instanceof ArrayBuffer) {
    return new Uint8Array(value);
  }

  if (Array.isArray(value)) {
    return Uint8Array.from(value);
  }

  return new Uint8Array(0);
};

export const browserRoundTrip = setStableTaskIdentity(importTask({
  href: IMPORTED_TASK_MODULE_HREF,
  name: "browserRoundTripImported",
}), 0, {
  api: "importTask",
  loadsFrom: IMPORTED_TASK_MODULE_HREF,
});

export const browserNumberRoundTrip = setStableTaskIdentity(task({
  href: TASK_MODULE_HREF,
  f: async (value) => {
    const parsed = Number(value);
    return Number.isFinite(parsed) ? parsed + 1 : Number.NaN;
  },
}), 1, {
  api: "task",
  loadsFrom: TASK_MODULE_HREF,
});

export const browserUint8RoundTrip = setStableTaskIdentity(task({
  href: TASK_MODULE_HREF,
  f: async (value) => {
    const bytes = toUint8Array(value);
    let sum = 0;

    for (const byte of bytes) {
      sum += byte;
    }

    return sum;
  },
}), 2, {
  api: "task",
  loadsFrom: TASK_MODULE_HREF,
});
