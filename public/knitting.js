var __defProp = Object.defineProperty;
var __returnValue = (v) => v;
function __exportSetter(name, newValue) {
  this[name] = __returnValue.bind(null, newValue);
}
var __export = (target, all) => {
  for (var name in all)
    __defProp(target, name, {
      get: all[name],
      enumerable: true,
      configurable: true,
      set: __exportSetter.bind(all, name)
    });
};
var __esm = (fn, res) => () => (fn && (res = fn(fn = 0)), res);

// src/debug/env-diff.ts
var snapshotGlobals = () => ({
  keys: new Set(Reflect.ownKeys(globalThis))
}), diffGlobals = (before, after) => {
  const added = [];
  const removed = [];
  for (const key of after.keys) {
    if (!before.keys.has(key))
      added.push(key);
  }
  for (const key of before.keys) {
    if (!after.keys.has(key))
      removed.push(key);
  }
  return { added, removed };
}, describeGlobalKey = (key) => {
  const name = typeof key === "symbol" ? key.toString() : key;
  let descriptor;
  try {
    descriptor = Object.getOwnPropertyDescriptor(globalThis, key);
  } catch {
    return name;
  }
  if (descriptor === undefined)
    return name;
  const kind = descriptor.get !== undefined || descriptor.set !== undefined ? "accessor" : typeof descriptor.value;
  const flags = `${descriptor.writable === false ? "" : "w"}${descriptor.configurable ? "c" : ""}${descriptor.enumerable ? "e" : ""}`;
  return flags.length > 0 ? `${name} (${kind} ${flags})` : `${name} (${kind})`;
};

// src/debug/handle.ts
var exports_handle = {};
__export(exports_handle, {
  initDebug: () => initDebug
});
var initDebug = ({ name, runtime, namespaces }) => {
  const all = namespaces.has("*");
  const enabled = (namespace) => all || namespaces.has(namespace);
  const base = performance.now();
  const tag = `${name}·${runtime}`;
  const log = (namespace, message) => {
    if (!enabled(namespace))
      return;
    const elapsed = (performance.now() - base).toFixed(1);
    console.error(`[${tag}·+${elapsed}ms] ${namespace}: ${message}`);
  };
  let previous = enabled("globals") ? snapshotGlobals() : undefined;
  const envPhase = (label) => {
    if (previous === undefined)
      return;
    const current = snapshotGlobals();
    const { added, removed } = diffGlobals(previous, current);
    previous = current;
    if (added.length === 0 && removed.length === 0) {
      log("globals", `${label}: no new globals`);
      return;
    }
    if (added.length > 0) {
      log("globals", `${label} +${added.length}: ${added.map(describeGlobalKey).join("  ")}`);
    }
    if (removed.length > 0) {
      log("globals", `${label} -${removed.length}: ${removed.map(String).join("  ")}`);
    }
  };
  return { enabled, log, envPhase };
};
var init_handle = () => {};

// src/common/node-compat.ts
var nodeProcess = (() => {
  const candidate = globalThis.process;
  return typeof candidate?.versions?.node === "string" ? candidate : undefined;
})();
var getNodeProcess = () => nodeProcess;
var getNodeBuiltinModule = (specifier) => {
  const getter = nodeProcess?.getBuiltinModule;
  if (typeof getter !== "function")
    return;
  try {
    return getter.call(nodeProcess, specifier);
  } catch {}
  if (!specifier.startsWith("node:"))
    return;
  try {
    return getter.call(nodeProcess, specifier.slice(5));
  } catch {
    return;
  }
};

// src/common/runtime.ts
var globals = globalThis;
var nodeProcess2 = getNodeProcess();
var IS_DENO = typeof globals.Deno?.version?.deno === "string";
var IS_BUN = typeof globals.Bun?.version === "string";
var IS_NODE = typeof nodeProcess2?.versions?.node === "string";
var IS_ANDROMEDA = typeof globals.__andromeda__ !== "undefined";
var IS_BROWSER = !IS_DENO && !IS_BUN && !IS_NODE && !IS_ANDROMEDA && (typeof globals.document !== "undefined" || typeof globals.WorkerGlobalScope === "function");
var RUNTIME = IS_DENO ? "deno" : IS_BUN ? "bun" : IS_NODE ? "node" : IS_ANDROMEDA ? "andromeda" : IS_BROWSER ? "browser" : "unknown";
var WebAssemblyRef = globals.WebAssembly;
var SET_IMMEDIATE = typeof globals.setImmediate === "function" ? globals.setImmediate : undefined;
var WASM_MEMORY_PAGE_BYTES = 64 * 1024;
var wasmSharedBufferMemory = new WeakMap;
var wasmSharedBufferMaxByteLength = new WeakMap;
var hasSharedWasmMemory = (() => {
  if (typeof WebAssemblyRef?.Memory !== "function")
    return false;
  try {
    new WebAssemblyRef.Memory({ initial: 0, maximum: 1, shared: true });
    return true;
  } catch {
    return false;
  }
})();
var roundupWasmPages = (byteLength) => Math.ceil(Math.max(0, byteLength) / WASM_MEMORY_PAGE_BYTES);
var createSharedWasmBuffer = (byteLength, maxByteLength) => {
  const memory = new WebAssemblyRef.Memory({
    initial: roundupWasmPages(byteLength),
    maximum: Math.max(roundupWasmPages(byteLength), roundupWasmPages(maxByteLength)),
    shared: true
  });
  const buffer = memory.buffer;
  wasmSharedBufferMemory.set(buffer, memory);
  wasmSharedBufferMaxByteLength.set(buffer, maxByteLength);
  return buffer;
};
var createWasmSharedArrayBuffer = (byteLength, maxByteLength = byteLength) => {
  if (hasSharedWasmMemory) {
    return createSharedWasmBuffer(byteLength, maxByteLength);
  }
  return new SharedArrayBuffer(byteLength);
};
var HAS_NATIVE_SAB_GROW = typeof SharedArrayBuffer === "function" && typeof SharedArrayBuffer.prototype.grow === "function";
var HAS_SAB_GROW = HAS_NATIVE_SAB_GROW || hasSharedWasmMemory;
var createSharedArrayBuffer = (byteLength, maxByteLength) => {
  if (HAS_NATIVE_SAB_GROW && typeof maxByteLength === "number") {
    return new SharedArrayBuffer(byteLength, { maxByteLength });
  }
  if (hasSharedWasmMemory && typeof maxByteLength === "number") {
    return createSharedWasmBuffer(byteLength, maxByteLength);
  }
  return new SharedArrayBuffer(byteLength);
};
var isGrowableSharedArrayBuffer = (sab) => {
  const value = sab;
  return HAS_NATIVE_SAB_GROW && typeof value.grow === "function" && value.growable === true || wasmSharedBufferMemory.has(sab);
};
var sharedArrayBufferMaxByteLength = (sab) => {
  const value = sab;
  if (typeof value.maxByteLength === "number") {
    return value.maxByteLength;
  }
  return wasmSharedBufferMaxByteLength.get(sab) ?? sab.byteLength;
};
var growSharedArrayBuffer = (sab, byteLength) => {
  const native = sab;
  if (typeof native.grow === "function") {
    native.grow(byteLength);
    return sab;
  }
  const memory = wasmSharedBufferMemory.get(sab);
  if (memory == null) {
    throw new TypeError("SharedArrayBuffer is not growable");
  }
  const currentBuffer = memory.buffer;
  if (currentBuffer.byteLength >= byteLength) {
    return currentBuffer;
  }
  const targetPages = roundupWasmPages(byteLength);
  const currentPages = roundupWasmPages(currentBuffer.byteLength);
  memory.grow(targetPages - currentPages);
  const nextBuffer = memory.buffer;
  const maxByteLength = wasmSharedBufferMaxByteLength.get(sab) ?? currentBuffer.byteLength;
  wasmSharedBufferMemory.set(nextBuffer, memory);
  wasmSharedBufferMaxByteLength.set(nextBuffer, maxByteLength);
  return nextBuffer;
};

// src/common/worker-runtime.ts
var RUNTIME_PROCESS_WORKER_ENV = "KNITTING_PROCESS_WORKER";
var RUNTIME_POOL_DEPTH_ENV = "KNITTING_POOL_DEPTH";
var nodeProcess3 = getNodeProcess();
var RUNTIME_IS_PROCESS_WORKER = nodeProcess3?.env?.[RUNTIME_PROCESS_WORKER_ENV] === "1";
var readPoolDepth = () => {
  const raw = nodeProcess3?.env?.[RUNTIME_POOL_DEPTH_ENV];
  if (typeof raw !== "string")
    return 0;
  const parsed = Number.parseInt(raw, 10);
  return Number.isFinite(parsed) && parsed > 0 ? parsed : 0;
};
var RUNTIME_POOL_DEPTH = readPoolDepth();
var workerThreads = getNodeBuiltinModule("node:worker_threads");
var isWorkerGlobalScope = () => {
  const scopeCtor = globalThis.WorkerGlobalScope;
  if (typeof scopeCtor === "function") {
    try {
      if (globalThis instanceof scopeCtor) {
        return true;
      }
    } catch {}
  }
  if (IS_ANDROMEDA && typeof globalThis.self !== "undefined") {
    return true;
  }
  return false;
};
var RUNTIME_WORKER = workerThreads?.Worker ?? globalThis.Worker;
var RUNTIME_MESSAGE_CHANNEL = workerThreads?.MessageChannel ?? globalThis.MessageChannel;
var HAS_NODE_WORKER_THREADS = workerThreads != null;
var RUNTIME_IS_MAIN_THREAD = RUNTIME_IS_PROCESS_WORKER ? false : workerThreads?.isMainThread ?? !isWorkerGlobalScope();
var RUNTIME_WORKER_DATA = workerThreads?.workerData;
var RUNTIME_PARENT_PORT = workerThreads?.parentPort ?? (RUNTIME_IS_PROCESS_WORKER && typeof nodeProcess3?.send === "function" ? {
  postMessage: (message) => nodeProcess3.send(message)
} : undefined);
var createRuntimeMessageChannel = () => {
  if (typeof RUNTIME_MESSAGE_CHANNEL !== "function") {
    throw new Error("MessageChannel is not available in this runtime");
  }
  return new RUNTIME_MESSAGE_CHANNEL;
};
var addRuntimeDataListener = (target, handler) => {
  if (typeof target.on === "function") {
    target.on("message", handler);
    return;
  }
  if (typeof target.addEventListener === "function") {
    target.addEventListener("message", (event) => handler(event?.data));
    return;
  }
  target.onmessage = (event) => handler(event?.data);
};

// src/common/shared-buffer-region.ts
var isSharedBuffer = (value) => value instanceof SharedArrayBuffer || value instanceof ArrayBuffer;
var isSharedBufferRegion = (value) => {
  if (!value || typeof value !== "object")
    return false;
  const candidate = value;
  return isSharedBuffer(candidate.sab) && typeof candidate.byteOffset === "number" && Number.isInteger(candidate.byteOffset) && candidate.byteOffset >= 0 && typeof candidate.byteLength === "number" && Number.isInteger(candidate.byteLength) && candidate.byteLength >= 0;
};
var isSharedBufferSource = (value) => isSharedBuffer(value) || isSharedBufferRegion(value);
var toSharedBufferRegion = (value) => isSharedBuffer(value) ? {
  sab: value,
  byteOffset: 0,
  byteLength: value.byteLength
} : value;

// src/common/shared-buffer-text.ts
var textEncode = new TextEncoder;
var textDecode = new TextDecoder;
var isSharedBufferTextCompatTypeError = (error) => error instanceof TypeError;
var makeProbeView = (source) => {
  const region = toSharedBufferRegion(source);
  const probeLength = Math.min(1, region.byteLength);
  return new Uint8Array(region.sab, region.byteOffset, probeLength);
};
var isSharedBufferTextCompat = (value) => {
  if (!value || typeof value !== "object")
    return false;
  const candidate = value;
  return typeof candidate.encodeInto === "boolean" && typeof candidate.decode === "boolean";
};
var isLockBufferTextCompat = (value) => {
  if (!value || typeof value !== "object")
    return false;
  const candidate = value;
  return isSharedBufferTextCompat(candidate.headers) && isSharedBufferTextCompat(candidate.payload);
};
var probeSharedBufferTextCompat = (source) => {
  const view = makeProbeView(source);
  const encodeInto = (() => {
    if (typeof textEncode.encodeInto !== "function")
      return false;
    const probe = view.byteLength > 0 ? view : view.subarray(0, 0);
    const restoredByte = probe.byteLength > 0 ? probe[0] : undefined;
    try {
      textEncode.encodeInto(probe.byteLength > 0 ? "a" : "", probe);
      return true;
    } catch (error) {
      if (!isSharedBufferTextCompatTypeError(error))
        throw error;
      return false;
    } finally {
      if (restoredByte !== undefined) {
        probe[0] = restoredByte;
      }
    }
  })();
  const decode = (() => {
    try {
      textDecode.decode(view);
      return true;
    } catch (error) {
      if (!isSharedBufferTextCompatTypeError(error))
        throw error;
      return false;
    }
  })();
  return {
    encodeInto,
    decode
  };
};
var probeLockBufferTextCompat = ({
  headers,
  payload
}) => ({
  headers: probeSharedBufferTextCompat(headers),
  payload: probeSharedBufferTextCompat(payload)
});

// src/ipc/tools/ring-queue.ts
class RingQueue {
  #buf;
  #mask;
  #head = 0;
  #tail = 0;
  #size = 0;
  constructor(capacity = 512) {
    let cap = 2;
    while (cap < capacity)
      cap <<= 1;
    this.#buf = new Array(cap).fill(null);
    this.#mask = cap - 1;
  }
  get size() {
    return this.#size;
  }
  get isEmpty() {
    return this.#size === 0;
  }
  get capacity() {
    return this.#mask + 1;
  }
  clear() {
    this.#head = 0;
    this.#tail = 0;
    this.#size = 0;
  }
  peek() {
    return this.#size === 0 ? undefined : this.#buf[this.#head];
  }
  reserve(minCapacity) {
    if (minCapacity <= this.capacity)
      return;
    let cap = this.capacity;
    while (cap < minCapacity)
      cap <<= 1;
    this.#growTo(cap);
  }
  #growIfFull() {
    if (this.#size !== this.#mask + 1)
      return;
    this.#growTo(this.#mask + 1 << 1);
  }
  #growTo(newCap) {
    const oldBuf = this.#buf;
    const oldCap = this.#mask + 1;
    const n = this.#size;
    const next = new Array(newCap).fill(null);
    const head = this.#head;
    const firstLen = Math.min(n, oldCap - head);
    for (let i = 0;i < firstLen; i++) {
      next[i] = oldBuf[head + i];
    }
    for (let i = firstLen;i < n; i++) {
      next[i] = oldBuf[i - firstLen];
    }
    this.#buf = next;
    this.#mask = newCap - 1;
    this.#head = 0;
    this.#tail = n;
  }
  push(value) {
    this.#growIfFull();
    const buf = this.#buf;
    const mask = this.#mask;
    const tail = this.#tail;
    buf[tail] = value;
    this.#tail = tail + 1 & mask;
    this.#size++;
    return true;
  }
  unshift(value) {
    this.#growIfFull();
    const buf = this.#buf;
    const mask = this.#mask;
    const head = this.#head - 1 & mask;
    this.#head = head;
    buf[head] = value;
    this.#size++;
    return true;
  }
  shift() {
    const size = this.#size;
    if (size === 0)
      return;
    const head = this.#head;
    const buf = this.#buf;
    const v = buf[head];
    buf[head] = null;
    this.#head = head + 1 & this.#mask;
    this.#size = size - 1;
    return v;
  }
  shiftNoClear() {
    const size = this.#size;
    if (size === 0)
      return;
    const head = this.#head;
    const v = this.#buf[head];
    this.#head = head + 1 & this.#mask;
    this.#size = size - 1;
    return v;
  }
  *[Symbol.iterator]() {
    const buf = this.#buf;
    const mask = this.#mask;
    let idx = this.#head;
    let i = 0;
    const n = this.#size;
    while (i < n) {
      const v = buf[idx];
      if (v !== null)
        yield v;
      idx = idx + 1 & mask;
      i++;
    }
  }
  toArray() {
    const out = new Array(this.#size);
    const buf = this.#buf;
    const mask = this.#mask;
    let idx = this.#head;
    for (let i = 0;i < out.length; i++) {
      out[i] = buf[idx];
      idx = idx + 1 & mask;
    }
    return out;
  }
  get [Symbol.toStringTag]() {
    return `RingQueue(size=${this.#size}, cap=${this.capacity})`;
  }
}

// src/memory/payload-config.ts
var PAYLOAD_DEFAULT_MAX_BYTE_LENGTH = 64 * 1024 * 1024;
var PAYLOAD_DEFAULT_INITIAL_BYTES = 4 * 1024 * 1024;
var toPositiveInteger = (value) => {
  if (!Number.isFinite(value))
    return;
  const int = Math.floor(value);
  return int > 0 ? int : undefined;
};
var canGrowSharedBuffer = (sab) => {
  if (sab == null)
    return false;
  return sab instanceof SharedArrayBuffer && HAS_SAB_GROW && isGrowableSharedArrayBuffer(sab);
};
var sharedBufferMaxByteLength = (sab) => {
  if (sab == null)
    return;
  if (sab instanceof SharedArrayBuffer) {
    return toPositiveInteger(sharedArrayBufferMaxByteLength(sab));
  }
  return toPositiveInteger(sab.byteLength);
};
var resolvePayloadBufferOptions = ({
  options,
  sab
}) => {
  const sabRegion = sab === undefined ? undefined : toSharedBufferRegion(sab);
  const backing = sabRegion?.sab;
  const requestedMode = options?.mode;
  const modeDefault = HAS_SAB_GROW ? "growable" : "fixed";
  let mode = requestedMode ?? modeDefault;
  if (mode === "growable" && backing != null && !canGrowSharedBuffer(backing)) {
    mode = "fixed";
  }
  if (mode === "growable" && !HAS_SAB_GROW) {
    mode = "fixed";
  }
  const payloadMaxByteLength = toPositiveInteger(options?.payloadMaxByteLength) ?? toPositiveInteger(sabRegion?.byteLength) ?? sharedBufferMaxByteLength(backing) ?? PAYLOAD_DEFAULT_MAX_BYTE_LENGTH;
  const requestedInitialBytes = toPositiveInteger(options?.payloadInitialBytes);
  const payloadInitialBytes = mode === "fixed" ? payloadMaxByteLength : Math.min(requestedInitialBytes ?? PAYLOAD_DEFAULT_INITIAL_BYTES, payloadMaxByteLength);
  const maxPayloadCeiling = payloadMaxByteLength >> 3;
  if (maxPayloadCeiling <= 0) {
    throw new RangeError("payloadMaxByteLength is too small; must be at least 8 bytes.");
  }
  const rawMaxPayloadBytes = options?.maxPayloadBytes;
  if (rawMaxPayloadBytes !== undefined) {
    const normalized = Math.floor(rawMaxPayloadBytes);
    if (!Number.isFinite(normalized) || normalized <= 0) {
      throw new RangeError(`maxPayloadBytes must be > 0 and <= ${maxPayloadCeiling}.`);
    }
  }
  const maxPayloadBytes = toPositiveInteger(rawMaxPayloadBytes) ?? maxPayloadCeiling;
  if (maxPayloadBytes <= 0 || maxPayloadBytes > maxPayloadCeiling) {
    throw new RangeError(`maxPayloadBytes must be > 0 and <= ${maxPayloadCeiling}.`);
  }
  return {
    mode,
    payloadInitialBytes,
    payloadMaxByteLength,
    maxPayloadBytes
  };
};

// src/memory/lock.ts
var registeredEncodePayload;
var registeredDecodePayload;
var registerLockPayloadCodec = (encode, decode) => {
  registeredEncodePayload = encode;
  registeredDecodePayload = decode;
};
var PayloadSignal = {
  UNREACHABLE: 0,
  BigInt: 2,
  True: 3,
  False: 4,
  Undefined: 5,
  NaN: 6,
  Float64: 9,
  Null: 10
};
var PayloadBuffer = {
  BORDER_SIGNAL_BUFFER: 11,
  String: 11,
  Json: 12,
  StaticString: 15,
  StaticJson: 16,
  Binary: 17,
  StaticBinary: 18,
  Int32Array: 19,
  Float64Array: 20,
  BigInt64Array: 21,
  BigUint64Array: 22,
  DataView: 23,
  Error: 24,
  Date: 25,
  Symbol: 26,
  StaticSymbol: 27,
  BigInt: 28,
  StaticBigInt: 29,
  StaticInt32Array: 31,
  StaticFloat64Array: 32,
  StaticBigInt64Array: 33,
  StaticBigUint64Array: 34,
  StaticDataView: 35,
  ArrayBuffer: 36,
  StaticArrayBuffer: 37,
  Buffer: 38,
  StaticBuffer: 39,
  EnvelopeStaticHeader: 40,
  EnvelopeDynamicHeader: 41,
  EnvelopeStaticHeaderString: 42,
  EnvelopeDynamicHeaderString: 43,
  ExternalPayload: 44,
  StaticExternalPayload: 45,
  ProcessSharedBuffer: 46,
  BufferReference: 47,
  SharedArrayBuffer: 48,
  EnvelopeStaticHeaderExternal: 49,
  EnvelopeDynamicHeaderExternal: 50,
  EnvelopeStaticHeaderStringExternal: 51,
  EnvelopeDynamicHeaderStringExternal: 52,
  NumericArray: 53,
  StaticNumericArray: 54
};
var PayloadBufferName = {};
for (const key of Object.keys(PayloadBuffer)) {
  PayloadBufferName[PayloadBuffer[key]] = key;
}
var payloadBufferName = (value) => PayloadBufferName[value] ?? String(value);
var LockBound = {
  paddingLock: 0,
  padding: 0,
  slots: 32,
  header: 0
};
var LOCK_CACHE_LINE_BYTES = 64;
var LOCK_SECTOR_BYTES = 256;
var PayloadTransportFinalizer = Symbol.for("knitting.payloadCodec.transportFinalizer");
var PromisePayloadMarker = Symbol.for("knitting.promise.payload");
var TASK_LOCAL_FLAGS_INDEX = 7;
var TASK_LOCAL_PROMISE_PENDING_FLAG = 1 << 0;
var TASK_LOCAL_PROMISE_TRACKED_FLAG = 1 << 1;
var beginPromisePayload = (task) => {
  const flags = task[TASK_LOCAL_FLAGS_INDEX];
  if ((flags & TASK_LOCAL_PROMISE_PENDING_FLAG) !== 0)
    return false;
  task[TASK_LOCAL_FLAGS_INDEX] = (flags | TASK_LOCAL_PROMISE_PENDING_FLAG) >>> 0;
  return true;
};
var finishPromisePayload = (task) => {
  task[TASK_LOCAL_FLAGS_INDEX] = (task[TASK_LOCAL_FLAGS_INDEX] & ~TASK_LOCAL_PROMISE_PENDING_FLAG) >>> 0;
};
var isPromisePayloadPending = (task) => (task[TASK_LOCAL_FLAGS_INDEX] & TASK_LOCAL_PROMISE_PENDING_FLAG) !== 0;
var resetTaskLocalFlags = (task) => {
  task[TASK_LOCAL_FLAGS_INDEX] = 0;
};
var addTaskFinalizer = (task, finalizer) => {
  const previous = task.finalize;
  task.finalize = previous === undefined ? finalizer : () => {
    try {
      previous();
    } finally {
      finalizer();
    }
  };
};
var attachPayloadTransportFinalizer = (task, value) => {
  if (task.finalize !== undefined || value === null || typeof value !== "object") {
    return;
  }
  const finalizer = value[PayloadTransportFinalizer]?.();
  if (typeof finalizer === "function")
    addTaskFinalizer(task, finalizer);
};
var runTaskFinalizers = (task) => {
  const finalizer = task.finalize;
  task.finalize = undefined;
  if (finalizer !== undefined) {
    try {
      finalizer();
    } catch {}
  }
};
var TaskIndex = {
  FlagsToHost: 0,
  FunctionID: 0,
  ID: 1,
  Type: 2,
  Start: 3,
  End: 4,
  PayloadLen: 5,
  slotBuffer: 6,
  Size: 8,
  TotalBuff: 144
};
var TASK_SLOT_INDEX_BITS = 5;
var TASK_SLOT_INDEX_MASK = (1 << TASK_SLOT_INDEX_BITS) - 1;
var TASK_SLOT_META_BITS = 32 - TASK_SLOT_INDEX_BITS;
var TASK_SLOT_META_VALUE_MASK = 4294967295 >>> TASK_SLOT_INDEX_BITS;
var TASK_SLOT_META_PACKED_MASK = ~TASK_SLOT_INDEX_MASK >>> 0;
var TASK_FUNCTION_ID_BITS = 16;
var TASK_FUNCTION_ID_MASK = (1 << TASK_FUNCTION_ID_BITS) - 1;
var TASK_FUNCTION_META_BITS = 32 - TASK_FUNCTION_ID_BITS;
var TASK_FUNCTION_META_VALUE_MASK = 4294967295 >>> TASK_FUNCTION_ID_BITS;
var TASK_FUNCTION_META_PACKED_MASK = ~TASK_FUNCTION_ID_MASK >>> 0;
var getTaskFunctionMeta = (task) => task[TaskIndex.FunctionID] >>> TASK_FUNCTION_ID_BITS & TASK_FUNCTION_META_VALUE_MASK;
var getTaskSlotIndex = (task) => task[TaskIndex.slotBuffer] & TASK_SLOT_INDEX_MASK;
var getTaskSlotMeta = (task) => task[TaskIndex.slotBuffer] >>> TASK_SLOT_INDEX_BITS & TASK_SLOT_META_VALUE_MASK;
var TaskFlag = {
  Reject: 1
};
var LOCK_WORD_BYTES = Int32Array.BYTES_PER_ELEMENT;
var LOCK_HOST_BITS_OFFSET_BYTES = LockBound.paddingLock;
var LOCK_WORKER_BITS_OFFSET_BYTES = LOCK_CACHE_LINE_BYTES;
var LOCK_SECTOR_BYTE_LENGTH = LOCK_SECTOR_BYTES;
var PAYLOAD_LOCK_HOST_BITS_OFFSET_BYTES = LOCK_CACHE_LINE_BYTES * 2;
var PAYLOAD_LOCK_WORKER_BITS_OFFSET_BYTES = LOCK_CACHE_LINE_BYTES * 3;
var HEADER_SLOT_STRIDE_U32 = LockBound.header + TaskIndex.TotalBuff;
var HEADER_SLOT_STRIDE_BYTES = HEADER_SLOT_STRIDE_U32 * Uint32Array.BYTES_PER_ELEMENT;
var HEADER_TASK_LINE_U32 = LOCK_CACHE_LINE_BYTES / Uint32Array.BYTES_PER_ELEMENT;
var HEADER_STATIC_PAYLOAD_U32 = TaskIndex.TotalBuff - HEADER_TASK_LINE_U32;
var HEADER_TASK_OFFSET_IN_SLOT_U32 = HEADER_STATIC_PAYLOAD_U32;
var STEAL_ACK_SLOT_OFFSET_U32 = HEADER_TASK_OFFSET_IN_SLOT_U32 + TaskIndex.Size;
var STEAL_WANT_SLOT_OFFSET_U32 = STEAL_ACK_SLOT_OFFSET_U32 + 1;
var STEAL_PAYLOAD_ACK_SLOT_OFFSET_U32 = STEAL_ACK_SLOT_OFFSET_U32 + 2;
var STEAL_LIVE_SLOT_OFFSET_U32 = STEAL_PAYLOAD_ACK_SLOT_OFFSET_U32 + 1;
var DOORBELL_ARMED_SLOT_OFFSET_U32 = STEAL_LIVE_SLOT_OFFSET_U32 + 1;
var HEADER_U32_LENGTH = LockBound.header + HEADER_SLOT_STRIDE_U32 * LockBound.slots;
var HEADER_BYTE_LENGTH = HEADER_U32_LENGTH * Uint32Array.BYTES_PER_ELEMENT;
var INDEX_ID = 0;
var INIT_VAL = PayloadSignal.UNREACHABLE;
var def = (_) => {};
var createTaskShell = () => {
  const task = new Uint32Array(TaskIndex.Size);
  task.value = null;
  task.finalize = undefined;
  task.resolve = def;
  task.reject = def;
  task[TASK_LOCAL_FLAGS_INDEX] = 0;
  return task;
};
var makeTask = () => {
  const task = createTaskShell();
  task[TaskIndex.ID] = INDEX_ID++;
  return task;
};
var fillTaskFrom = (task, array, at) => {
  task[0] = array[at];
  task[1] = array[at + 1];
  task[2] = array[at + 2];
  task[3] = array[at + 3];
  task[4] = array[at + 4];
  task[5] = array[at + 5];
  task[6] = array[at + 6];
  task[TASK_LOCAL_FLAGS_INDEX] = 0;
};
var makeTaskFrom = (array, at) => {
  const task = createTaskShell();
  fillTaskFrom(task, array, at);
  return task;
};
var settleTask = (task) => {
  if (task[TaskIndex["FlagsToHost"]] === 0) {
    task.resolve(task.value);
  } else {
    task.reject(task.value);
    task[TaskIndex["FlagsToHost"]] = 0;
  }
};
var lock2 = ({
  headers,
  headerSlotStrideU32,
  LockBoundSector,
  payload,
  payloadConfig,
  payloadSector,
  textCompat,
  resultList,
  toSentList,
  recycleList,
  processBoundary,
  consumers,
  consumerId,
  regionLanes,
  notifyOnHostPublish
}) => {
  const lockSectorRegion = toSharedBufferRegion(LockBoundSector ?? createWasmSharedArrayBuffer(LOCK_SECTOR_BYTE_LENGTH));
  const LockBoundSAB = lockSectorRegion.sab;
  const hostBits = new Int32Array(LockBoundSAB, lockSectorRegion.byteOffset + LOCK_HOST_BITS_OFFSET_BYTES, 1);
  const workerBits = new Int32Array(LockBoundSAB, lockSectorRegion.byteOffset + LOCK_WORKER_BITS_OFFSET_BYTES, 1);
  const headersRegion = toSharedBufferRegion(headers ?? createWasmSharedArrayBuffer(HEADER_BYTE_LENGTH));
  const headersBuffer = new Uint32Array(headersRegion.sab, headersRegion.byteOffset, headersRegion.byteLength >>> 2);
  const headersSlotStride = headerSlotStrideU32 ?? HEADER_SLOT_STRIDE_U32;
  const doorbellArmed = new Int32Array(headersRegion.sab, headersRegion.byteOffset + DOORBELL_ARMED_SLOT_OFFSET_U32 * Uint32Array.BYTES_PER_ELEMENT, 1);
  const resolvedPayloadConfig = resolvePayloadBufferOptions({
    sab: payload,
    options: payloadConfig
  });
  const payloadSAB = payload ?? (resolvedPayloadConfig.mode === "growable" ? createSharedArrayBuffer(resolvedPayloadConfig.payloadInitialBytes, resolvedPayloadConfig.payloadMaxByteLength) : createSharedArrayBuffer(resolvedPayloadConfig.payloadInitialBytes));
  const payloadLockRegion = toSharedBufferRegion(payloadSector ?? lockSectorRegion);
  const resolvedTextCompat = textCompat ?? probeLockBufferTextCompat({
    headers: headersRegion,
    payload: payloadSAB
  });
  const stealConsumers = Math.max(1, (consumers ?? 1) | 0);
  const stealEnabled = stealConsumers > 1;
  const stealIsProducer = consumerId === undefined;
  const stealId = (consumerId ?? 0) | 0;
  const stealRegionLanes = (regionLanes ?? 8) | 0;
  const stealRegions = LockBound.slots / stealRegionLanes | 0;
  if (stealEnabled) {
    if (stealRegionLanes < 1 || (stealRegionLanes & stealRegionLanes - 1) !== 0) {
      throw new RangeError("regionLanes must be a power of two");
    }
    if (stealRegions < stealConsumers) {
      throw new RangeError(`regionLanes=${stealRegionLanes} yields ${stealRegions} regions, ` + `too few for ${stealConsumers} consumers`);
    }
    if (stealId < 0 || stealId >= stealConsumers) {
      throw new RangeError(`consumerId ${stealId} out of range`);
    }
  }
  const stealView = new Int32Array(headersRegion.sab, headersRegion.byteOffset, headersRegion.byteLength >>> 2);
  const stealAckIndex = new Int32Array(stealConsumers);
  const stealWantIndex = new Int32Array(stealConsumers);
  for (let c = 0;c < stealConsumers; c++) {
    const slotBase = c * headersSlotStride + LockBound.header;
    stealAckIndex[c] = slotBase + STEAL_ACK_SLOT_OFFSET_U32;
    stealWantIndex[c] = slotBase + STEAL_WANT_SLOT_OFFSET_U32;
  }
  const stealLiveIndex = LockBound.header + STEAL_LIVE_SLOT_OFFSET_U32;
  const stealAllLiveMask = stealConsumers === 32 ? -1 : (1 << stealConsumers) - 1 | 0;
  if (stealEnabled && stealIsProducer) {
    Atomics.store(stealView, stealLiveIndex, stealAllLiveMask);
  }
  const stealIsLive = (mask, consumer) => (mask & 1 << consumer) !== 0;
  const stealAckXorAll = () => {
    let x = 0 | 0;
    for (let c = 0;c < stealConsumers; c++) {
      x = x ^ a_load(stealView, stealAckIndex[c]) | 0;
    }
    return x;
  };
  let promiseHandler;
  if (registeredEncodePayload === undefined || registeredDecodePayload === undefined) {
    throw new Error("Payload codec not registered before lock2(). Ensure the module that " + 'builds locks imports "./payloadCodec.ts" (it self-registers on load).');
  }
  const encodeTask = registeredEncodePayload({
    payload: {
      sab: payloadSAB,
      config: resolvedPayloadConfig
    },
    headersBuffer,
    headerSlotStrideU32: headersSlotStride,
    lockSector: payloadLockRegion,
    textCompat: resolvedTextCompat,
    processBoundary,
    onPromise: (task, isRejected, value) => {
      if ((task[TASK_LOCAL_FLAGS_INDEX] & TASK_LOCAL_PROMISE_TRACKED_FLAG) !== 0 && pendingPromiseCount > 0) {
        task[TASK_LOCAL_FLAGS_INDEX] = (task[TASK_LOCAL_FLAGS_INDEX] & ~TASK_LOCAL_PROMISE_TRACKED_FLAG) >>> 0;
        pendingPromiseCount = pendingPromiseCount - 1 | 0;
      }
      promiseHandler(task, isRejected, value);
    }
  });
  const decodeTask = registeredDecodePayload({
    payload: {
      sab: payloadSAB,
      config: resolvedPayloadConfig
    },
    headersBuffer,
    headerSlotStrideU32: headersSlotStride,
    lockSector: payloadLockRegion,
    textCompat: resolvedTextCompat,
    processBoundary
  });
  let LastLocal = 0 | 0;
  let LastWorker = 0 | 0;
  let lastTake = 32 | 0;
  const toBeSent = toSentList ?? new RingQueue;
  const recyclecList = recycleList ?? new RingQueue;
  const resolved = resultList ?? new RingQueue;
  let deferredCount = 0 | 0;
  let pendingPromiseCount = 0 | 0;
  const a_load = Atomics.load;
  const a_store = Atomics.store;
  const a_notify = Atomics.notify;
  const shouldNotifyHostPublish = notifyOnHostPublish === true;
  const a_waitAsync = typeof Atomics.waitAsync === "function" ? Atomics.waitAsync.bind(Atomics) : undefined;
  let workerShadow = 0 | 0;
  const refreshWorkerShadow = stealEnabled ? () => workerShadow = stealAckXorAll() : () => workerShadow = a_load(workerBits, 0) | 0;
  refreshWorkerShadow();
  const ensureSenderStateHasFree = (state) => ~state !== 0 ? state : LastLocal ^ refreshWorkerShadow() | 0;
  const toBeSentPush = (task) => toBeSent.push(task);
  const toBeSentShift = () => toBeSent.shiftNoClear();
  const toBeSentUnshift = (task) => toBeSent.unshift(task);
  const recycleShift = () => recyclecList.shiftNoClear();
  const resolvedPush = (task) => resolved.push(task);
  const clz32 = Math.clz32;
  const slotBaseU32 = LockBound.header + HEADER_TASK_OFFSET_IN_SLOT_U32;
  const takeTask = ({ queue }) => (at) => {
    const off = at * headersSlotStride + slotBaseU32;
    const task = queue[headersBuffer[off + TaskIndex.ID]];
    fillTaskFrom(task, headersBuffer, off);
    return task;
  };
  const enlist = (task) => toBeSentPush(task);
  const trackDeferredTask = (task) => {
    const flags = task[TASK_LOCAL_FLAGS_INDEX];
    if ((flags & TASK_LOCAL_PROMISE_TRACKED_FLAG) !== 0)
      return;
    task[TASK_LOCAL_FLAGS_INDEX] = (flags | TASK_LOCAL_PROMISE_TRACKED_FLAG) >>> 0;
    pendingPromiseCount = pendingPromiseCount + 1 | 0;
  };
  const encodeTaskValue = (task, slotIndex) => encodeTask(task, slotIndex);
  let selectedSlotIndex = 0 | 0, selectedSlotBit = 0 >>> 0;
  const encodeWithState = (task, state) => {
    const free = ~state;
    if (free === 0)
      return 0;
    if (!encodeTaskValue(task, selectedSlotIndex = 31 - clz32(free)))
      return 0;
    encodeAt(task, selectedSlotIndex, selectedSlotBit = 1 << selectedSlotIndex);
    return selectedSlotBit;
  };
  const encodeManyFrom = (list) => {
    let state = ensureSenderStateHasFree(LastLocal ^ workerShadow | 0);
    let encoded = 0 | 0;
    if (list === toBeSent) {
      while (true) {
        const task = toBeSentShift();
        if (!task)
          break;
        state = ensureSenderStateHasFree(state);
        const bit = encodeWithState(task, state) | 0;
        if (bit === 0) {
          toBeSentUnshift(task);
          break;
        }
        state = state ^ bit | 0;
        encoded = encoded + 1 | 0;
      }
    } else {
      while (true) {
        const task = list.shiftNoClear();
        if (!task)
          break;
        state = ensureSenderStateHasFree(state);
        const bit = encodeWithState(task, state) | 0;
        if (bit === 0) {
          list.unshift(task);
          break;
        }
        state = state ^ bit | 0;
        encoded = encoded + 1 | 0;
      }
    }
    return encoded;
  };
  const encodeManyTrackedFrom = (list) => {
    let state = ensureSenderStateHasFree(LastLocal ^ workerShadow | 0);
    let encoded = 0 | 0;
    deferredCount = 0 | 0;
    if (list === toBeSent) {
      while (true) {
        const task = toBeSentShift();
        if (!task)
          break;
        state = ensureSenderStateHasFree(state);
        const bit = encodeWithState(task, state) | 0;
        if (bit === 0) {
          if (isPromisePayloadPending(task)) {
            deferredCount = deferredCount + 1 | 0;
            trackDeferredTask(task);
            continue;
          }
          toBeSentUnshift(task);
          break;
        }
        state = state ^ bit | 0;
        encoded = encoded + 1 | 0;
      }
    } else {
      while (true) {
        const task = list.shiftNoClear();
        if (!task)
          break;
        state = ensureSenderStateHasFree(state);
        const bit = encodeWithState(task, state) | 0;
        if (bit === 0) {
          if (isPromisePayloadPending(task)) {
            deferredCount = deferredCount + 1 | 0;
            trackDeferredTask(task);
            continue;
          }
          list.unshift(task);
          break;
        }
        state = state ^ bit | 0;
        encoded = encoded + 1 | 0;
      }
    }
    return encoded;
  };
  const encodeAll = () => {
    if (toBeSent.isEmpty)
      return true;
    encodeManyTrackedFrom(toBeSent);
    deferredCount = 0 | 0;
    return toBeSent.isEmpty;
  };
  const storeHost = (bit) => {
    a_store(hostBits, 0, LastLocal = LastLocal ^ bit | 0);
    if (shouldNotifyHostPublish && a_load(doorbellArmed, 0) !== 0) {
      a_notify(hostBits, 0, 1);
    }
  };
  const storeWorker = (bit) => a_store(workerBits, 0, LastWorker = LastWorker ^ bit | 0);
  const encode = (task, state = LastLocal ^ workerShadow | 0) => {
    state = ensureSenderStateHasFree(state);
    const free = ~state;
    if (free === 0)
      return false;
    if (!encodeTaskValue(task, selectedSlotIndex = 31 - clz32(free))) {
      return false;
    }
    return encodeAt(task, selectedSlotIndex, selectedSlotBit = 1 << selectedSlotIndex);
  };
  const encodeTracked = (task, state = LastLocal ^ workerShadow | 0) => {
    deferredCount = 0 | 0;
    state = ensureSenderStateHasFree(state);
    const free = ~state;
    if (free === 0)
      return false;
    if (!encodeTaskValue(task, selectedSlotIndex = 31 - clz32(free))) {
      if (isPromisePayloadPending(task)) {
        deferredCount = 1;
        trackDeferredTask(task);
      }
      return false;
    }
    return encodeAt(task, selectedSlotIndex, selectedSlotBit = 1 << selectedSlotIndex);
  };
  const encodeAt = (task, at, bit) => {
    const off = at * headersSlotStride + slotBaseU32;
    headersBuffer[off] = task[0];
    headersBuffer[off + 1] = task[1];
    headersBuffer[off + 2] = task[2];
    headersBuffer[off + 3] = task[3];
    headersBuffer[off + 4] = task[4];
    headersBuffer[off + 5] = task[5];
    headersBuffer[off + 6] = task[6];
    headersBuffer[off + TASK_LOCAL_FLAGS_INDEX] = 0;
    storeHost(bit);
    return true;
  };
  const hasSpace = () => (hostBits[0] ^ LastWorker) !== 0;
  const decode = () => {
    let diff = a_load(hostBits, 0) ^ LastWorker | 0;
    if (diff === 0)
      return false;
    let last = lastTake;
    let consumedBits = 0 | 0;
    try {
      if (last === 32) {
        decodeAt(selectedSlotIndex = 31 - clz32(diff));
        selectedSlotBit = 1 << (last = selectedSlotIndex);
        diff ^= selectedSlotBit;
        consumedBits = consumedBits ^ selectedSlotBit | 0;
      }
      while (diff !== 0) {
        let pick = diff & (1 << last) - 1;
        if (pick === 0)
          pick = diff;
        decodeAt(selectedSlotIndex = 31 - clz32(pick));
        selectedSlotBit = 1 << (last = selectedSlotIndex);
        diff ^= selectedSlotBit;
        consumedBits = consumedBits ^ selectedSlotBit | 0;
      }
    } finally {
      if (consumedBits !== 0)
        storeWorker(consumedBits);
    }
    lastTake = last;
    return true;
  };
  const stealLaneMask = (region) => stealRegionLanes === 32 ? -1 : (1 << stealRegionLanes) - 1 << region * stealRegionLanes | 0;
  const stealPeerAcks = () => {
    let x = 0 | 0;
    for (let c = 0;c < stealConsumers; c++) {
      if (c !== stealId)
        x = x ^ a_load(stealView, stealAckIndex[c]) | 0;
    }
    return x;
  };
  const stealJuniorWants = (intent) => {
    const live = a_load(stealView, stealLiveIndex) | 0;
    for (let c = stealId + 1;c < stealConsumers; c++) {
      if (!stealIsLive(live, c))
        continue;
      if ((a_load(stealView, stealWantIndex[c]) & intent) !== 0)
        return true;
    }
    return false;
  };
  let stealCursor = stealRegions * stealId / stealConsumers | 0;
  const decodeSteal = () => {
    const pending = a_load(hostBits, 0) ^ LastWorker ^ stealPeerAcks() | 0;
    if (pending === 0)
      return false;
    let pendingRegions = 0 | 0;
    if (stealRegions === 1)
      pendingRegions = 1;
    else {
      for (let r = 0;r < stealRegions; r++) {
        if ((pending & stealLaneMask(r)) !== 0)
          pendingRegions |= 1 << r;
      }
    }
    const liveBeforeClaim = a_load(stealView, stealLiveIndex) | 0;
    let peerIntent = 0 | 0;
    let seniorIntent = 0 | 0;
    for (let c = 0;c < stealConsumers; c++) {
      if (c === stealId || !stealIsLive(liveBeforeClaim, c))
        continue;
      const value = a_load(stealView, stealWantIndex[c]) | 0;
      peerIntent |= value;
      if (c < stealId)
        seniorIntent |= value;
    }
    const notSenior = pendingRegions & ~seniorIntent;
    if (notSenior === 0)
      return false;
    const clean = pendingRegions & ~peerIntent;
    const candidates = clean !== 0 ? clean : notSenior;
    let region = -1;
    for (let step = 0;step < stealRegions; step++) {
      const candidate = (stealCursor + step) % stealRegions;
      if ((candidates & 1 << candidate) !== 0) {
        region = candidate;
        break;
      }
    }
    if (region < 0)
      return false;
    const intent = 1 << region | 0;
    a_store(stealView, stealWantIndex[stealId], intent);
    let seniorConflict = false;
    let juniorConflict = false;
    for (let c = 0;c < stealConsumers; c++) {
      if (c === stealId || !stealIsLive(liveBeforeClaim, c))
        continue;
      if ((a_load(stealView, stealWantIndex[c]) & intent) === 0)
        continue;
      if (c < stealId)
        seniorConflict = true;
      else
        juniorConflict = true;
    }
    if (seniorConflict) {
      a_store(stealView, stealWantIndex[stealId], 0);
      return false;
    }
    if (juniorConflict) {
      while (stealJuniorWants(intent)) {}
    }
    const take = (a_load(hostBits, 0) ^ LastWorker ^ stealPeerAcks()) & stealLaneMask(region) | 0;
    if (take === 0) {
      a_store(stealView, stealWantIndex[stealId], 0);
      return false;
    }
    let lanes = take;
    while (lanes !== 0) {
      decodeAt(31 - clz32((lanes & -lanes) >>> 0));
      lanes = lanes & lanes - 1 | 0;
    }
    LastWorker = LastWorker ^ take | 0;
    a_store(stealView, stealAckIndex[stealId], LastWorker);
    a_store(stealView, stealWantIndex[stealId], 0);
    stealCursor = (region + 1) % stealRegions;
    return true;
  };
  const resolveHost = ({
    queue,
    onResolved,
    shouldSettle,
    activeRejectPlaceholder
  }) => {
    const getTask = takeTask({ queue });
    let lastResolved = 32;
    if (activeRejectPlaceholder !== undefined && onResolved) {
      const onResolvedTask2 = onResolved;
      const inactiveReject = activeRejectPlaceholder;
      return () => {
        let diff = a_load(hostBits, 0) ^ LastWorker | 0;
        if (diff === 0)
          return 0;
        let modified = 0;
        let consumedBits = 0 | 0;
        let last = lastResolved;
        if (last === 32) {
          const idx = 31 - clz32(diff);
          const selectedBit = 1 << idx;
          const task = getTask(idx);
          decodeTask(task, idx);
          consumedBits = consumedBits ^ selectedBit | 0;
          if (task.reject !== inactiveReject) {
            settleTask(task);
            onResolvedTask2(task);
          }
          diff ^= selectedBit;
          modified++;
          if ((modified & 7) === 0 && consumedBits !== 0) {
            LastWorker = LastWorker ^ consumedBits | 0;
            a_store(workerBits, 0, LastWorker);
            consumedBits = 0 | 0;
          }
          last = idx;
        }
        while (diff !== 0) {
          const lowerMask = last === 31 ? 2147483647 : (1 << last) - 1;
          let pick = diff & lowerMask;
          if (pick === 0)
            pick = diff;
          const idx = 31 - clz32(pick);
          const selectedBit = 1 << idx;
          const task = getTask(idx);
          decodeTask(task, idx);
          consumedBits = consumedBits ^ selectedBit | 0;
          if (task.reject !== inactiveReject) {
            settleTask(task);
            onResolvedTask2(task);
          }
          diff ^= selectedBit;
          modified++;
          if ((modified & 7) === 0 && consumedBits !== 0) {
            LastWorker = LastWorker ^ consumedBits | 0;
            a_store(workerBits, 0, LastWorker);
            consumedBits = 0 | 0;
          }
          last = idx;
        }
        if (consumedBits !== 0) {
          LastWorker = LastWorker ^ consumedBits | 0;
          a_store(workerBits, 0, LastWorker);
        }
        lastResolved = last;
        return modified;
      };
    }
    const hasOnResolved = onResolved !== undefined;
    const onResolvedTask = onResolved ?? def;
    const shouldSettleTask = shouldSettle;
    return () => {
      let diff = a_load(hostBits, 0) ^ LastWorker | 0;
      if (diff === 0)
        return 0;
      let modified = 0;
      let consumedBits = 0 | 0;
      let last = lastResolved;
      if (last === 32) {
        const idx = 31 - clz32(diff);
        const selectedBit = 1 << idx;
        const task = getTask(idx);
        decodeTask(task, idx);
        consumedBits = consumedBits ^ selectedBit | 0;
        if (shouldSettleTask === undefined || shouldSettleTask(task)) {
          settleTask(task);
          if (hasOnResolved)
            onResolvedTask(task);
        }
        diff ^= selectedBit;
        modified++;
        if ((modified & 7) === 0 && consumedBits !== 0) {
          LastWorker = LastWorker ^ consumedBits | 0;
          a_store(workerBits, 0, LastWorker);
          consumedBits = 0 | 0;
        }
        last = idx;
      }
      while (diff !== 0) {
        const lowerMask = last === 31 ? 2147483647 : (1 << last) - 1;
        let pick = diff & lowerMask;
        if (pick === 0)
          pick = diff;
        const idx = 31 - clz32(pick);
        const selectedBit = 1 << idx;
        const task = getTask(idx);
        decodeTask(task, idx);
        consumedBits = consumedBits ^ selectedBit | 0;
        if (shouldSettleTask === undefined || shouldSettleTask(task)) {
          settleTask(task);
          if (hasOnResolved)
            onResolvedTask(task);
        }
        diff ^= selectedBit;
        modified++;
        if ((modified & 7) === 0 && consumedBits !== 0) {
          LastWorker = LastWorker ^ consumedBits | 0;
          a_store(workerBits, 0, LastWorker);
          consumedBits = 0 | 0;
        }
        last = idx;
      }
      if (consumedBits !== 0) {
        LastWorker = LastWorker ^ consumedBits | 0;
        a_store(workerBits, 0, LastWorker);
      }
      lastResolved = last;
      return modified;
    };
  };
  const waitForHostChange = (timeoutMs) => {
    if (a_waitAsync === undefined) {
      a_store(doorbellArmed, 0, 0);
      return;
    }
    a_store(doorbellArmed, 0, 1);
    try {
      const wait = a_waitAsync(hostBits, 0, LastWorker | 0, timeoutMs);
      if (!wait.async)
        a_store(doorbellArmed, 0, 0);
      return wait;
    } catch {
      a_store(doorbellArmed, 0, 0);
      return;
    }
  };
  const decodeAt = (at) => {
    const off = at * headersSlotStride + slotBaseU32;
    const recycled = recycleShift();
    let task;
    if (recycled) {
      fillTaskFrom(recycled, headersBuffer, off);
      recycled.value = null;
      recycled.finalize = undefined;
      recycled.resolve = def;
      recycled.reject = def;
      task = recycled;
    } else {
      task = makeTaskFrom(headersBuffer, off);
    }
    decodeTask(task, at);
    resolvedPush(task);
    return true;
  };
  const publish = (task) => {
    if (encodeTracked(task))
      return true;
    if ((deferredCount | 0) !== 0) {
      deferredCount = 0 | 0;
      return false;
    }
    toBeSentPush(task);
    return false;
  };
  const flushPending = () => {
    if (toBeSent.isEmpty)
      return false;
    const encoded = encodeManyTrackedFrom(toBeSent) | 0;
    deferredCount = 0 | 0;
    return encoded !== 0;
  };
  const resetPendingState = () => {
    toBeSent.clear();
    deferredCount = 0 | 0;
    pendingPromiseCount = 0 | 0;
  };
  const deactivateStealConsumer = (id) => {
    if (!stealEnabled || !stealIsProducer)
      return false;
    if (!Number.isInteger(id) || id < 0 || id >= stealConsumers) {
      throw new RangeError(`consumerId ${id} out of range`);
    }
    const bit = 1 << id;
    const previous = Atomics.and(stealView, stealLiveIndex, ~bit);
    return (previous & bit) !== 0;
  };
  return {
    enlist,
    encode,
    encodeManyFrom,
    encodeAll,
    publish,
    flushPending,
    decode: stealEnabled ? decodeSteal : decode,
    hasSpace,
    resolved,
    hostBits,
    workerBits,
    recyclecList,
    resolveHost,
    waitForHostChange,
    setHostWaiterArmed: (armed) => {
      a_store(doorbellArmed, 0, armed ? 1 : 0);
    },
    hasPendingFrames: () => toBeSent.size !== 0,
    getPendingFrameCount: () => toBeSent.size | 0,
    getPendingPromiseCount: () => pendingPromiseCount | 0,
    resetPendingState,
    deactivateStealConsumer,
    takeDeferredCount: () => {
      const count = deferredCount | 0;
      deferredCount = 0 | 0;
      return count;
    },
    setPromiseHandler: (handler) => {
      promiseHandler = handler;
    }
  };
};

// src/worker/composable-runners.ts
var ABORT_SIGNAL_META_OFFSET = 1;
var TIMEOUT_KIND_RESOLVE = 1;
var p_now = performance.now.bind(performance);
var raceTimeout = (promise, ms, resolveOnTimeout, timeoutValue) => new Promise((resolve, reject) => {
  let done = false;
  const timer = setTimeout(() => {
    if (done)
      return;
    done = true;
    if (resolveOnTimeout)
      resolve(timeoutValue);
    else
      reject(timeoutValue);
  }, ms);
  promise.then((value) => {
    if (done)
      return;
    done = true;
    clearTimeout(timer);
    resolve(value);
  }, (err) => {
    if (done)
      return;
    done = true;
    clearTimeout(timer);
    reject(err);
  });
});
var nowStamp = (now) => (Math.floor(now()) & TASK_SLOT_META_VALUE_MASK) >>> 0;
var applyTimeoutBudget = (promise, slot, spec, now) => {
  const elapsed = nowStamp(now) - getTaskSlotMeta(slot) & TASK_SLOT_META_VALUE_MASK;
  const remaining = spec.ms - elapsed;
  if (!(remaining > 0)) {
    promise.then(() => {}, () => {});
    return spec.kind === TIMEOUT_KIND_RESOLVE ? Promise.resolve(spec.value) : Promise.reject(spec.value);
  }
  const timeoutMs = Math.max(1, Math.floor(remaining));
  return raceTimeout(promise, timeoutMs, spec.kind === TIMEOUT_KIND_RESOLVE, spec.value);
};
var NO_ABORT_SIGNAL = -1;
var readSignal = (slot) => {
  const encodedSignal = getTaskFunctionMeta(slot);
  if (encodedSignal === 0)
    return NO_ABORT_SIGNAL;
  const signal = encodedSignal - ABORT_SIGNAL_META_OFFSET | 0;
  return signal >= 0 ? signal : NO_ABORT_SIGNAL;
};
var makeToolkitCache = (hasAborted, now) => {
  const bySignal = [];
  return (signal) => {
    let toolkit = bySignal[signal];
    if (toolkit)
      return toolkit;
    const hasAbortedMethod = () => hasAborted(signal);
    toolkit = {
      hasAborted: hasAbortedMethod,
      now
    };
    bySignal[signal] = toolkit;
    return toolkit;
  };
};
var composeWorkerRunner = ({
  job,
  timeout,
  hasAborted,
  now
}) => {
  const nowTime = now ?? p_now;
  if (!hasAborted) {
    if (!timeout) {
      return (slot) => job(slot.value);
    }
    return (slot) => {
      const result = job(slot.value);
      if (!(result instanceof Promise))
        return result;
      return applyTimeoutBudget(result, slot, timeout, nowTime);
    };
  }
  const getToolkit = makeToolkitCache(hasAborted, nowTime);
  if (!timeout) {
    return (slot) => {
      const signal = readSignal(slot);
      if (signal === NO_ABORT_SIGNAL)
        return job(slot.value);
      return job(slot.value, getToolkit(signal));
    };
  }
  return (slot) => {
    const signal = readSignal(slot);
    const result = signal === NO_ABORT_SIGNAL ? job(slot.value) : job(slot.value, getToolkit(signal));
    if (!(result instanceof Promise))
      return result;
    return applyTimeoutBudget(result, slot, timeout, nowTime);
  };
};

// scripts/browser-stubs/buffer-reference.ts
var BUFFER_REFERENCE_NUMERIC_TRANSFER = Symbol.for("knitting.bufferReference.numericTransfer");
var BUFFER_REFERENCE_RETURN_RELEASE_TOKEN = Symbol.for("knitting.bufferReference.returnReleaseToken");
var unavailable = () => {
  throw new Error('BufferReference cannot run in runtime "browser"');
};

class BufferReference {
  constructor() {
    unavailable();
  }
  static fromMetadata = unavailable;
}
var isBufferReferenceValue = (_value) => false;
var withBufferReferenceReturnReleaser = (_releaser, run) => run();
var readBufferReferenceReturnReleaseMessage = (_value) => {
  return;
};
var createBufferReferenceReturnReleaseMessage = unavailable;
var detachArrayBufferBestEffort = unavailable;

// src/worker/rx-queue.ts
var createWorkerRxQueue = ({
  listOfFunctions,
  workerOptions,
  lock,
  returnLock,
  borrowReturnedBufferReferences,
  hasAborted,
  now,
  stealing
}) => {
  const PLACE_HOLDER = (_) => {
    throw "UNREACHABLE FROM PLACE HOLDER (thread)";
  };
  let hasAnythingFinished = 0;
  let awaiting = 0;
  const jobs = listOfFunctions.reduce((acc, fixed) => (acc.push(fixed.run), acc), []);
  const toWork = new RingQueue;
  const pendingFrames = new RingQueue;
  const toWorkPush = (slot) => toWork.push(slot);
  const toWorkShift = () => toWork.shiftNoClear();
  const pendingShift = () => pendingFrames.shiftNoClear();
  const pendingUnshift = (slot) => pendingFrames.unshift(slot);
  const pendingPush = (slot) => pendingFrames.push(slot);
  const recyclePush = (slot) => lock.recyclecList.push(slot);
  const FUNCTION_ID_MASK = 65535;
  const IDX_FLAGS = TaskIndex.FlagsToHost;
  const FLAG_REJECT = TaskFlag.Reject;
  const a_load = Atomics.load;
  const returnHostBits = returnLock.hostBits;
  const returnWorkerBits = returnLock.workerBits;
  const deferredReleases = [];
  const explicitReturnReleases = new Map;
  const drainReturnReleases = () => {
    if (deferredReleases.length === 0)
      return;
    if ((a_load(returnHostBits, 0) ^ a_load(returnWorkerBits, 0)) !== 0)
      return;
    for (let i = 0;i < deferredReleases.length; i++) {
      try {
        deferredReleases[i]();
      } catch {}
    }
    deferredReleases.length = 0;
  };
  const releaseReturnedBufferReference = (token) => {
    const key = token.toString();
    const release = explicitReturnReleases.get(key);
    if (release === undefined)
      return;
    explicitReturnReleases.delete(key);
    try {
      release();
    } catch {}
  };
  const runByIndex = listOfFunctions.reduce((acc, fixed, idx) => {
    const job = jobs[idx];
    acc.push(composeWorkerRunner({
      job,
      timeout: fixed.timeout,
      hasAborted,
      now
    }));
    return acc;
  }, []);
  const hasCompleted = workerOptions?.resolveAfterFinishingAll === true ? () => hasAnythingFinished !== 0 && toWork.size === 0 : () => hasAnythingFinished !== 0;
  const { decode, resolved } = lock;
  const resolvedShift = () => resolved.shiftNoClear();
  const enqueueLock = () => {
    if (stealing && toWork.size !== 0)
      return false;
    if (!decode())
      return false;
    let task = resolvedShift();
    while (task) {
      task.resolve = PLACE_HOLDER;
      task.reject = PLACE_HOLDER;
      attachPayloadTransportFinalizer(task, task.value);
      toWorkPush(task);
      task = resolvedShift();
    }
    return true;
  };
  const encodeReturnSafe = (slot) => {
    if (!returnLock.encode(slot))
      return false;
    return true;
  };
  const sendReturn = (slot, shouldReject) => {
    slot[IDX_FLAGS] = shouldReject ? FLAG_REJECT : 0;
    if (!encodeReturnSafe(slot))
      return false;
    if (slot.finalize !== undefined) {
      const token = slot.finalize[BUFFER_REFERENCE_RETURN_RELEASE_TOKEN];
      if (token === undefined || borrowReturnedBufferReferences !== true) {
        deferredReleases.push(slot.finalize);
      } else {
        explicitReturnReleases.set(token.toString(), slot.finalize);
      }
      slot.finalize = undefined;
    }
    hasAnythingFinished--;
    recyclePush(slot);
    return true;
  };
  const settleNow = (slot, isError, value, wasAwaited) => {
    runTaskFinalizers(slot);
    slot.value = value;
    hasAnythingFinished++;
    if (wasAwaited && awaiting > 0)
      awaiting--;
    const shouldReject = isError || slot[IDX_FLAGS] === FLAG_REJECT;
    if (!sendReturn(slot, shouldReject))
      pendingPush(slot);
  };
  const writeOne = () => {
    const slot = pendingShift();
    if (!slot)
      return false;
    if (!sendReturn(slot, slot[IDX_FLAGS] === FLAG_REJECT)) {
      pendingUnshift(slot);
      return false;
    }
    return true;
  };
  return {
    hasCompleted,
    hasPending: () => toWork.size !== 0,
    writeBatch: (max) => {
      let wrote = 0;
      while (wrote < max) {
        if (!writeOne())
          break;
        wrote++;
      }
      return wrote;
    },
    serviceBatchImmediate: () => {
      let processed = 0;
      while (processed < 5 && toWork.size !== 0) {
        const slot = toWorkShift();
        try {
          const fnIndex = slot[TaskIndex.FunctionID] & FUNCTION_ID_MASK;
          const result = runByIndex[fnIndex](slot);
          slot[IDX_FLAGS] = 0;
          slot.value = null;
          if (result instanceof Promise) {
            awaiting++;
            result.then((value) => settleNow(slot, false, value, true), (err) => settleNow(slot, true, err, true));
          } else {
            settleNow(slot, false, result, false);
          }
        } catch (err) {
          settleNow(slot, true, err, false);
        }
        ++processed;
      }
      return processed;
    },
    enqueueLock,
    drainReturnReleases,
    releaseReturnedBufferReference,
    hasAwaiting: () => awaiting > 0,
    getAwaiting: () => awaiting
  };
};

// src/ipc/transport/shared-memory.ts
var page = 1024 * 4;
var CACHE_LINE_BYTES = 64;
var SIGNAL_OFFSETS = {
  op: 0,
  rxStatus: CACHE_LINE_BYTES,
  txStatus: CACHE_LINE_BYTES * 2
};
var TRANSPORT_SIGNAL_BYTES = CACHE_LINE_BYTES * 3;
var a_store = Atomics.store;
var createSharedMemoryTransport = ({ sabObject, isMain, startTime }) => {
  const toGrow = sabObject?.size ?? page;
  const roundedSize = toGrow + (page - toGrow % page) % page;
  const signalRegion = toSharedBufferRegion(sabObject?.sharedSab ? sabObject.sharedSab : createSharedArrayBuffer(roundedSize, page * page));
  const sab = signalRegion.sab;
  const baseByteOffset = signalRegion.byteOffset;
  const startAt = startTime ?? performance.now();
  const opView = new Int32Array(sab, baseByteOffset + SIGNAL_OFFSETS.op, 1);
  if (isMain)
    a_store(opView, 0, 0);
  const rxStatus = new Int32Array(sab, baseByteOffset + SIGNAL_OFFSETS.rxStatus, 1);
  a_store(rxStatus, 0, 1);
  return {
    sab: signalRegion,
    op: opView,
    startAt,
    opView,
    rxStatus,
    txStatus: new Int32Array(sab, baseByteOffset + SIGNAL_OFFSETS.txStatus, 1)
  };
};

// src/memory/regionRegistry.ts
var SLOT_META_PACKED_MASK = 4294967264;
var register = ({
  lockSector
}) => {
  const lockRegion = toSharedBufferRegion(lockSector ?? createWasmSharedArrayBuffer(LOCK_SECTOR_BYTE_LENGTH));
  const lockSAB = lockRegion.sab;
  const hostBits = new Int32Array(lockSAB, lockRegion.byteOffset + PAYLOAD_LOCK_HOST_BITS_OFFSET_BYTES, 1);
  const workerBits = new Int32Array(lockSAB, lockRegion.byteOffset + PAYLOAD_LOCK_WORKER_BITS_OFFSET_BYTES, 1);
  const startAndIndex = new Uint32Array(LockBound.slots);
  const size64bit = new Uint32Array(LockBound.slots);
  const clz32 = Math.clz32;
  const a_load = Atomics.load;
  const a_store2 = Atomics.store;
  const a_xor = Atomics.xor;
  const EMPTY = 4294967295 >>> 0;
  const SLOT_MASK = TASK_SLOT_INDEX_MASK;
  const START_MASK = ~SLOT_MASK >>> 0;
  startAndIndex.fill(EMPTY);
  let tableLength = 0;
  let usedBits = 0 | 0;
  let hostLast = 0 | 0;
  const startAndIndexToArray = (length) => startAndIndex.slice(0, length);
  const compactFreeBitsStable = (b, freeBits) => {
    const sai = startAndIndex;
    let w = 0 | 0;
    b = b | 0;
    freeBits = freeBits >>> 0;
    for (let r = 0;r < b; r++) {
      const v = sai[r];
      if (v === EMPTY)
        continue;
      if ((freeBits & 1 << (v & SLOT_MASK)) !== 0)
        continue;
      if (w !== r)
        sai[w] = v;
      w++;
    }
    const live = w;
    for (;w < b; w++)
      sai[w] = EMPTY;
    return live;
  };
  const updateTable = () => {
    const w = a_load(workerBits, 0) | 0;
    const state = (hostLast ^ w) >>> 0;
    let freeBits = ~state >>> 0;
    if (tableLength === 0 || freeBits === 0)
      return;
    if (freeBits === EMPTY) {
      tableLength = 0;
      usedBits = 0 | 0;
      return;
    }
    freeBits &= usedBits;
    if (freeBits === 0)
      return;
    usedBits &= ~freeBits;
    tableLength = compactFreeBitsStable(tableLength, freeBits);
  };
  const findAndInsert = (task, size) => {
    const sai = startAndIndex;
    const sz = size64bit;
    let tl = tableLength;
    let insertAt = -1;
    let insertStart = 0;
    let prevEnd = 0;
    let didCompactScan = false;
    if (tl === 0 && usedBits === 0) {
      sai[0] = 0;
      sz[0] = size;
      task[TaskIndex.Start] = 0;
      task[TaskIndex.slotBuffer] = (task[TaskIndex.slotBuffer] & SLOT_META_PACKED_MASK | 0) >>> 0;
      tableLength = 1;
      usedBits = 1;
      hostLast ^= 1;
      return 0;
    }
    if (tl !== 0) {
      const w = a_load(workerBits, 0) | 0;
      let freeBits = ~(hostLast ^ w) >>> 0;
      if (freeBits !== 0)
        freeBits &= usedBits;
      if (freeBits === usedBits >>> 0) {
        tableLength = 0;
        usedBits = 0 | 0;
        tl = 0;
        freeBits = 0 >>> 0;
      } else if (freeBits !== 0) {
        for (let i = 0;i < tl; i++) {
          const v = sai[i];
          const reclaimedSlot = v & SLOT_MASK;
          const reclaimedBit = 1 << reclaimedSlot;
          if ((freeBits & reclaimedBit) === 0)
            continue;
          if (sz[reclaimedSlot] >>> 0 !== size >>> 0)
            continue;
          const availableBits2 = ~usedBits >>> 0;
          const freeBit2 = (availableBits2 & -availableBits2) >>> 0;
          if (freeBit2 === 0)
            return -1;
          const slotIndex2 = 31 - clz32(freeBit2);
          const start = v & START_MASK;
          sai[i] = (start | slotIndex2) >>> 0;
          sz[slotIndex2] = size;
          task[TaskIndex.Start] = start;
          task[TaskIndex.slotBuffer] = (task[TaskIndex.slotBuffer] & SLOT_META_PACKED_MASK | slotIndex2) >>> 0;
          usedBits = usedBits & ~reclaimedBit | freeBit2;
          hostLast ^= freeBit2;
          return slotIndex2;
        }
      }
      if (tl !== 0 && freeBits !== 0 && freeBits !== EMPTY) {
        didCompactScan = true;
        let write = 0;
        for (let read = 0;read < tl; read++) {
          const v = sai[read];
          const slot = v & SLOT_MASK;
          if ((freeBits & 1 << slot) !== 0)
            continue;
          const curStart = v & START_MASK;
          if (insertAt === -1 && curStart - prevEnd >>> 0 >= size >>> 0) {
            insertAt = write;
            insertStart = prevEnd;
          }
          if (write !== read)
            sai[write] = v;
          write++;
          prevEnd = curStart + (sz[slot] >>> 0) >>> 0;
        }
        for (let i = write;i < tl; i++)
          sai[i] = EMPTY;
        if (freeBits !== 0)
          usedBits &= ~freeBits;
        tableLength = tl = write;
      }
    }
    if (tl >= LockBound.slots)
      return -1;
    const availableBits = ~usedBits >>> 0;
    const freeBit = (availableBits & -availableBits) >>> 0;
    if (freeBit === 0)
      return -1;
    const slotIndex = 31 - clz32(freeBit);
    if (!didCompactScan && tl !== 0) {
      const firstStart = sai[0] & START_MASK;
      if (firstStart >= size >>> 0) {
        for (let i = tl;i > 0; i--)
          sai[i] = sai[i - 1];
        sai[0] = slotIndex;
        sz[slotIndex] = size;
        task[TaskIndex.Start] = 0;
        task[TaskIndex.slotBuffer] = (task[TaskIndex.slotBuffer] & SLOT_META_PACKED_MASK | slotIndex) >>> 0;
        tableLength = tl + 1;
        usedBits |= freeBit;
        hostLast ^= freeBit;
        return slotIndex;
      }
      for (let at = 0;at + 1 < tl; at++) {
        const cur = sai[at];
        const curStart = cur & START_MASK;
        const curEnd = curStart + (sz[cur & SLOT_MASK] >>> 0) >>> 0;
        const nextStart = sai[at + 1] & START_MASK;
        if (nextStart - curEnd >>> 0 < size >>> 0)
          continue;
        for (let i = tl;i > at + 1; i--)
          sai[i] = sai[i - 1];
        sai[at + 1] = (curEnd | slotIndex) >>> 0;
        sz[slotIndex] = size;
        task[TaskIndex.Start] = curEnd;
        task[TaskIndex.slotBuffer] = (task[TaskIndex.slotBuffer] & SLOT_META_PACKED_MASK | slotIndex) >>> 0;
        tableLength = tl + 1;
        usedBits |= freeBit;
        hostLast ^= freeBit;
        return slotIndex;
      }
      const last = sai[tl - 1];
      const lastStart = last & START_MASK;
      const newStart = lastStart + (sz[last & SLOT_MASK] >>> 0) >>> 0;
      sai[tl] = (newStart | slotIndex) >>> 0;
      sz[slotIndex] = size;
      task[TaskIndex.Start] = newStart;
      task[TaskIndex.slotBuffer] = (task[TaskIndex.slotBuffer] & SLOT_META_PACKED_MASK | slotIndex) >>> 0;
      tableLength = tl + 1;
      usedBits |= freeBit;
      hostLast ^= freeBit;
      return slotIndex;
    }
    if (tl === 0) {
      sai[0] = slotIndex;
      sz[slotIndex] = size;
      task[TaskIndex.Start] = 0;
      task[TaskIndex.slotBuffer] = (task[TaskIndex.slotBuffer] & SLOT_META_PACKED_MASK | slotIndex) >>> 0;
      tableLength = 1;
      usedBits |= freeBit;
      hostLast ^= freeBit;
      return slotIndex;
    }
    if (insertAt !== -1) {
      for (let i = tl;i > insertAt; i--)
        sai[i] = sai[i - 1];
      sai[insertAt] = (insertStart | slotIndex) >>> 0;
      sz[slotIndex] = size;
      task[TaskIndex.Start] = insertStart;
      task[TaskIndex.slotBuffer] = (task[TaskIndex.slotBuffer] & SLOT_META_PACKED_MASK | slotIndex) >>> 0;
      tableLength = tl + 1;
      usedBits |= freeBit;
      hostLast ^= freeBit;
      return slotIndex;
    }
    sai[tl] = (prevEnd | slotIndex) >>> 0;
    sz[slotIndex] = size;
    task[TaskIndex.Start] = prevEnd;
    task[TaskIndex.slotBuffer] = (task[TaskIndex.slotBuffer] & SLOT_META_PACKED_MASK | slotIndex) >>> 0;
    tableLength = tl + 1;
    usedBits |= freeBit;
    hostLast ^= freeBit;
    return slotIndex;
  };
  const allocTask = (task) => {
    const payloadLen = task[TaskIndex.PayloadLen] | 0;
    const size = payloadLen + 63 & ~63;
    const slotIndex = findAndInsert(task, size);
    if (slotIndex === -1)
      return -1;
    a_store2(hostBits, 0, hostLast);
    return slotIndex;
  };
  const setSlotLength = (slotIndex, payloadLen) => {
    slotIndex = slotIndex & TASK_SLOT_INDEX_MASK;
    const aligned = (payloadLen | 0) + 63 & ~63;
    size64bit[slotIndex] = aligned >>> 0;
    return true;
  };
  const free = (index) => {
    a_xor(workerBits, 0, 1 << (index & TASK_SLOT_INDEX_MASK));
  };
  return {
    allocTask,
    setSlotLength,
    lockSAB,
    free,
    hostBits,
    workerBits,
    updateTable,
    startAndIndexToArray
  };
};

// src/memory/byte-carpet.ts
var BYTE_CARPET_ALIGN_BYTES = 64;
var U32_BYTES = Uint32Array.BYTES_PER_ELEMENT;
var toNonNegativeInteger = (value, label) => {
  if (!Number.isInteger(value) || value < 0) {
    throw new RangeError(`${label} must be a non-negative integer`);
  }
  return value;
};
var alignBytes = (value, alignment = BYTE_CARPET_ALIGN_BYTES) => {
  const safeValue = toNonNegativeInteger(value, "value");
  const safeAlignment = toNonNegativeInteger(alignment, "alignment");
  if (safeAlignment === 0) {
    throw new RangeError("alignment must be greater than zero");
  }
  return Math.ceil(safeValue / safeAlignment) * safeAlignment;
};
var makeSharedBufferRegion = (sab, byteOffset, byteLength) => ({
  sab,
  byteOffset: toNonNegativeInteger(byteOffset, "byteOffset"),
  byteLength: toNonNegativeInteger(byteLength, "byteLength")
});
var createByteCarpet = ({
  alignTo = BYTE_CARPET_ALIGN_BYTES,
  startByteOffset = 0
} = {}) => {
  const defaultAlignment = toNonNegativeInteger(alignTo, "alignTo");
  if (defaultAlignment === 0) {
    throw new RangeError("alignTo must be greater than zero");
  }
  let cursor = toNonNegativeInteger(startByteOffset, "startByteOffset");
  const slices = [];
  const take = (name, byteLength, {
    alignTo: sliceAlignment = defaultAlignment,
    reserveByteLength
  } = {}) => {
    const logicalByteLength = toNonNegativeInteger(byteLength, `${name} byteLength`);
    const safeSliceAlignment = toNonNegativeInteger(sliceAlignment, `${name} alignTo`);
    if (safeSliceAlignment === 0) {
      throw new RangeError(`${name} alignTo must be greater than zero`);
    }
    const reserved = reserveByteLength == null ? alignBytes(logicalByteLength, safeSliceAlignment) : toNonNegativeInteger(reserveByteLength, `${name} reserveByteLength`);
    if (reserved < logicalByteLength) {
      throw new RangeError(`${name} reserveByteLength must cover byteLength`);
    }
    const byteOffset = alignBytes(cursor, safeSliceAlignment);
    const slice = {
      name,
      byteOffset,
      byteLength: logicalByteLength,
      reservedByteLength: reserved
    };
    slices.push(slice);
    cursor = byteOffset + reserved;
    return slice;
  };
  return {
    slices,
    take,
    byteLength: () => cursor,
    bind: (sab, slice) => makeSharedBufferRegion(sab, slice.byteOffset, slice.byteLength)
  };
};
var getStridedSlotOffsetU32 = ({
  slotIndex,
  slotStrideU32,
  baseU32 = 0,
  extraU32 = 0
}) => slotIndex * slotStrideU32 + baseU32 + extraU32;
var getStridedSlotByteOffset = ({
  slotIndex,
  slotStrideU32,
  baseByteOffset = 0,
  baseU32 = 0,
  extraU32 = 0
}) => baseByteOffset + getStridedSlotOffsetU32({
  slotIndex,
  slotStrideU32,
  baseU32,
  extraU32
}) * U32_BYTES;
var getStridedRegionSpanBytes = ({
  slotCount,
  slotStrideU32,
  slotLengthU32,
  baseU32 = 0
}) => {
  const safeSlotCount = toNonNegativeInteger(slotCount, "slotCount");
  if (safeSlotCount === 0)
    return 0;
  return (getStridedSlotOffsetU32({
    slotIndex: safeSlotCount - 1,
    slotStrideU32,
    baseU32
  }) + slotLengthU32) * U32_BYTES;
};
var getInterleavedSlotStrideU32 = (slotStrideU32) => slotStrideU32 * 2;
var getHeaderBlockByteLength = ({
  slotCount,
  slotStrideU32,
  queues = 1,
  alignTo = BYTE_CARPET_ALIGN_BYTES
}) => alignBytes(slotCount * slotStrideU32 * U32_BYTES * queues, alignTo);
var createInterleavedHeaderPair = ({
  sab,
  byteOffset,
  slotCount,
  slotStrideU32
}) => {
  const headerSlotStrideU32 = getInterleavedSlotStrideU32(slotStrideU32);
  const slotBytes = slotStrideU32 * U32_BYTES;
  const spanBytes = getStridedRegionSpanBytes({
    slotCount,
    slotStrideU32: headerSlotStrideU32,
    slotLengthU32: slotStrideU32
  });
  return {
    headerSlotStrideU32,
    requestHeaders: makeSharedBufferRegion(sab, byteOffset, spanBytes),
    returnHeaders: makeSharedBufferRegion(sab, byteOffset + slotBytes, spanBytes)
  };
};
var createLockControlCarpet = ({
  signalBytes,
  abortBytes,
  lockSectorBytes,
  headerSlotStrideU32,
  slotCount,
  headerLayout = "interleaved",
  alignTo = BYTE_CARPET_ALIGN_BYTES,
  createBuffer = (byteLength) => new SharedArrayBuffer(byteLength)
}) => {
  const carpet = createByteCarpet({ alignTo });
  const signalsSlice = carpet.take("signals", signalBytes);
  const requestLockSlice = carpet.take("requestLockSector", lockSectorBytes);
  const returnLockSlice = carpet.take("returnLockSector", lockSectorBytes);
  let requestHeadersSlice;
  let returnHeadersSlice;
  let interleavedHeadersSlice;
  if (headerLayout === "interleaved") {
    interleavedHeadersSlice = carpet.take("interleavedHeaders", getHeaderBlockByteLength({
      slotCount,
      slotStrideU32: headerSlotStrideU32,
      queues: 2,
      alignTo
    }));
  } else {
    requestHeadersSlice = carpet.take("requestHeaders", getHeaderBlockByteLength({
      slotCount,
      slotStrideU32: headerSlotStrideU32,
      alignTo
    }));
    returnHeadersSlice = carpet.take("returnHeaders", getHeaderBlockByteLength({
      slotCount,
      slotStrideU32: headerSlotStrideU32,
      alignTo
    }));
  }
  const abortSignalsSlice = carpet.take("abortSignals", abortBytes);
  const controlSAB = createBuffer(carpet.byteLength());
  const signals = carpet.bind(controlSAB, signalsSlice);
  const abortSignals = carpet.bind(controlSAB, abortSignalsSlice);
  const requestLockSector = carpet.bind(controlSAB, requestLockSlice);
  const returnLockSector = carpet.bind(controlSAB, returnLockSlice);
  const headerPair = headerLayout === "interleaved" ? createInterleavedHeaderPair({
    sab: controlSAB,
    byteOffset: interleavedHeadersSlice.byteOffset,
    slotCount,
    slotStrideU32: headerSlotStrideU32
  }) : {
    headerSlotStrideU32,
    requestHeaders: carpet.bind(controlSAB, requestHeadersSlice),
    returnHeaders: carpet.bind(controlSAB, returnHeadersSlice)
  };
  return {
    controlSAB,
    signals,
    abortSignals,
    lock: {
      headers: headerPair.requestHeaders,
      headerSlotStrideU32: headerPair.headerSlotStrideU32,
      lockSector: requestLockSector,
      payloadSector: requestLockSector
    },
    returnLock: {
      headers: headerPair.returnHeaders,
      headerSlotStrideU32: headerPair.headerSlotStrideU32,
      lockSector: returnLockSector,
      payloadSector: returnLockSector
    },
    slices: carpet.slices
  };
};

// src/memory/shared-buffer-io.ts
var page2 = 1024 * 4;
var textEncode2 = new TextEncoder;
var textDecode2 = new TextDecoder;
var DYNAMIC_HEADER_BYTES = 64;
var DYNAMIC_SAFE_PADDING_BYTES = page2;
var alignUpto64 = (n) => n + (64 - 1) & ~(64 - 1);
var isExactUint8Array = (src) => src.constructor === Uint8Array;
var canonicalDynamicUint8Array = (src) => isExactUint8Array(src) ? src : new Uint8Array(src.buffer, src.byteOffset, src.byteLength);
var isSharedBufferEncodeIntoError = (error) => error instanceof TypeError;
var isSharedBufferDecodeError = (error) => error instanceof TypeError;
var getBufferCtor = () => {
  const bufferCtor = globalThis.Buffer;
  if (typeof bufferCtor?.from !== "function" || typeof bufferCtor?.allocUnsafe !== "function" || typeof bufferCtor?.allocUnsafeSlow !== "function") {
    return;
  }
  return bufferCtor;
};
var manualEncodeInto = (str, target) => {
  let read = 0;
  let written = 0;
  for (const char of str) {
    const encoded = textEncode2.encode(char);
    if (written + encoded.byteLength > target.byteLength)
      break;
    target.set(encoded, written);
    written += encoded.byteLength;
    read += char.length;
  }
  return { read, written };
};
var fallbackEncodeInto = (str, target) => {
  const scratch = new Uint8Array(target.byteLength);
  const result = typeof textEncode2.encodeInto === "function" ? textEncode2.encodeInto(str, scratch) : manualEncodeInto(str, scratch);
  if (result.written > 0) {
    target.set(scratch.subarray(0, result.written), 0);
  }
  return result;
};
var fallbackDecode = (bytes) => textDecode2.decode(bytes.slice());
var sharedBufferEncodeInto = (str, target, textCompat) => {
  if (typeof textEncode2.encodeInto !== "function") {
    return fallbackEncodeInto(str, target);
  }
  if (textCompat?.encodeInto === true) {
    return textEncode2.encodeInto(str, target);
  }
  if (textCompat?.encodeInto === false)
    return fallbackEncodeInto(str, target);
  try {
    return textEncode2.encodeInto(str, target);
  } catch (error) {
    if (!isSharedBufferEncodeIntoError(error))
      throw error;
    return fallbackEncodeInto(str, target);
  }
};
var sharedBufferDecode = (bytes, textCompat) => {
  if (textCompat?.decode === true)
    return textDecode2.decode(bytes);
  if (textCompat?.decode === false)
    return fallbackDecode(bytes);
  try {
    return textDecode2.decode(bytes);
  } catch (error) {
    if (!isSharedBufferDecodeError(error))
      throw error;
    return fallbackDecode(bytes);
  }
};
var createSharedDynamicBufferIO = ({
  sab,
  payloadConfig,
  textCompat
}) => {
  const payloadRegion = sab === undefined ? undefined : toSharedBufferRegion(sab);
  const hasExplicitRegion = sab !== undefined && !isSharedBuffer(sab);
  const hasExternalArrayBuffer = payloadRegion?.sab instanceof ArrayBuffer && !(payloadRegion.sab instanceof SharedArrayBuffer);
  const forceFixedRegion = hasExplicitRegion || hasExternalArrayBuffer;
  const regionByteLength = payloadRegion?.byteLength;
  const bufferCtor = IS_BUN && payloadRegion?.sab instanceof ArrayBuffer && !(payloadRegion.sab instanceof SharedArrayBuffer) ? undefined : getBufferCtor();
  const resolvedPayload = resolvePayloadBufferOptions({
    sab: payloadRegion?.sab,
    options: !forceFixedRegion || regionByteLength === undefined ? payloadConfig : {
      ...payloadConfig,
      mode: "fixed",
      payloadInitialBytes: payloadConfig?.payloadInitialBytes ?? regionByteLength,
      payloadMaxByteLength: payloadConfig?.payloadMaxByteLength ?? regionByteLength
    }
  });
  const canGrow = resolvedPayload.mode === "growable";
  let lockSAB = payloadRegion?.sab ?? (canGrow ? createSharedArrayBuffer(resolvedPayload.payloadInitialBytes, resolvedPayload.payloadMaxByteLength) : createSharedArrayBuffer(resolvedPayload.payloadInitialBytes));
  let baseByteOffset = payloadRegion?.byteOffset ?? 0;
  let backingByteLength = payloadRegion?.byteLength ?? lockSAB.byteLength;
  let u8 = new Uint8Array(lockSAB, baseByteOffset + DYNAMIC_HEADER_BYTES, Math.max(0, backingByteLength - DYNAMIC_HEADER_BYTES));
  const requireBufferView = bufferCtor ? (buffer, byteOffset) => {
    const view = bufferCtor.from(buffer, byteOffset + DYNAMIC_HEADER_BYTES);
    if (view.buffer !== buffer) {
      throw new Error("Buffer view does not alias shared buffer");
    }
    return view;
  } : undefined;
  let buf = requireBufferView?.(lockSAB, baseByteOffset);
  let f64 = new Float64Array(lockSAB, baseByteOffset + DYNAMIC_HEADER_BYTES, Math.max(0, backingByteLength - DYNAMIC_HEADER_BYTES) >>> 3);
  const capacityBytes = () => backingByteLength - DYNAMIC_HEADER_BYTES;
  const ensureCapacity = (neededBytes) => {
    if (capacityBytes() >= neededBytes)
      return true;
    if (!canGrow)
      return false;
    try {
      if (!(lockSAB instanceof SharedArrayBuffer))
        return false;
      lockSAB = growSharedArrayBuffer(lockSAB, alignUpto64(DYNAMIC_HEADER_BYTES + neededBytes + DYNAMIC_SAFE_PADDING_BYTES));
    } catch {
      return false;
    }
    baseByteOffset = 0;
    backingByteLength = lockSAB.byteLength;
    u8 = new Uint8Array(lockSAB, baseByteOffset + DYNAMIC_HEADER_BYTES, backingByteLength - DYNAMIC_HEADER_BYTES);
    buf = requireBufferView?.(lockSAB, baseByteOffset);
    f64 = new Float64Array(lockSAB, baseByteOffset + DYNAMIC_HEADER_BYTES, backingByteLength - DYNAMIC_HEADER_BYTES >>> 3);
    return true;
  };
  const readUtf8 = (start, end) => {
    if (!buf) {
      return sharedBufferDecode(u8.subarray(start, end), textCompat);
    }
    return buf.toString("utf8", start, end);
  };
  const writeBinary = (src, start = 0) => {
    const bytes = canonicalDynamicUint8Array(src);
    if (!ensureCapacity(start + bytes.byteLength)) {
      return -1;
    }
    u8.set(bytes, start);
    return bytes.byteLength;
  };
  const writeBuffer = (src, start = 0) => {
    const bytes = src.byteLength;
    if (!ensureCapacity(start + bytes)) {
      return -1;
    }
    u8.set(src, start);
    return bytes;
  };
  const writeArrayBuffer = (src, start = 0) => {
    const bytes = src.byteLength;
    if (!ensureCapacity(start + bytes)) {
      return -1;
    }
    u8.set(new Uint8Array(src), start);
    return bytes;
  };
  const write8Binary = (src, start = 0) => {
    const bytes = src.byteLength;
    if (!ensureCapacity(start + bytes)) {
      return -1;
    }
    f64.set(src, start >>> 3);
    return bytes;
  };
  const readBytesCopy = (start, end) => u8.slice(start, end);
  const readBytesView = (start, end) => u8.subarray(start, end);
  const readBytesBufferCopy = (start, end) => {
    if (!bufferCtor || !buf)
      return readBytesCopy(start, end);
    const length = Math.max(0, end - start | 0);
    const out = bufferCtor.allocUnsafe(length);
    if (length === 0)
      return out;
    buf.copy(out, 0, start, end);
    return out;
  };
  const readBytesArrayBufferCopy = (start, end) => {
    if (!bufferCtor || !buf) {
      const out2 = readBytesCopy(start, end);
      return out2.buffer;
    }
    const length = Math.max(0, end - start | 0);
    if (length === 0)
      return new ArrayBuffer(0);
    const out = bufferCtor.allocUnsafeSlow(length);
    buf.copy(out, 0, start, end);
    return out.buffer;
  };
  const read8BytesFloatCopy = (start, end) => f64.slice(start >>> 3, end >>> 3);
  const read8BytesFloatView = (start, end) => f64.subarray(start >>> 3, end >>> 3);
  const writeUtf8 = (str, start, reservedBytes = str.length * 3) => {
    if (!ensureCapacity(start + reservedBytes)) {
      return -1;
    }
    const target = u8.subarray(start, start + reservedBytes);
    if (!buf) {
      const { read: read2, written: written2 } = sharedBufferEncodeInto(str, target, textCompat);
      if (read2 !== str.length)
        return -1;
      return written2;
    }
    const { read, written } = textEncode2.encodeInto(str, target);
    if (read !== str.length)
      return -1;
    return written;
  };
  return {
    readUtf8,
    writeBinary,
    writeBuffer,
    writeArrayBuffer,
    write8Binary,
    readBytesCopy,
    readBytesView,
    readBytesBufferCopy,
    readBufferCopy: readBytesBufferCopy,
    readBytesArrayBufferCopy,
    readArrayBufferCopy: readBytesArrayBufferCopy,
    read8BytesFloatCopy,
    read8BytesFloatView,
    writeUtf8
  };
};
var createSharedStaticBufferIO = ({
  headersBuffer,
  slotStrideU32,
  textCompat
}) => {
  const bufferCtor = getBufferCtor();
  const buffer = headersBuffer instanceof Uint32Array ? headersBuffer.buffer : headersBuffer;
  const baseByteOffset = headersBuffer instanceof Uint32Array ? headersBuffer.byteOffset : 0;
  const u32Bytes = Uint32Array.BYTES_PER_ELEMENT;
  const slotStride = slotStrideU32 ?? HEADER_SLOT_STRIDE_U32;
  const writableBytes = HEADER_STATIC_PAYLOAD_U32 * u32Bytes;
  const baseU8 = new Uint8Array(buffer, baseByteOffset);
  const baseBuf = bufferCtor?.from(buffer, baseByteOffset);
  const baseF64 = new Float64Array(buffer, baseByteOffset, buffer.byteLength - baseByteOffset >>> 3);
  const slotStartBytes = (at) => getStridedSlotByteOffset({
    slotIndex: at,
    slotStrideU32: slotStride,
    baseByteOffset,
    baseU32: LockBound.header
  });
  const slotByteOffsets = new Uint32Array(LockBound.slots);
  for (let i = 0;i < LockBound.slots; i++) {
    slotByteOffsets[i] = slotStartBytes(i) - baseByteOffset;
  }
  const baseU32 = new Uint32Array(buffer, baseByteOffset, buffer.byteLength - baseByteOffset >>> 2);
  const slotU32Offsets = new Uint32Array(LockBound.slots);
  for (let i = 0;i < LockBound.slots; i++) {
    slotU32Offsets[i] = slotByteOffsets[i] >>> 2;
  }
  const writeU32Words = (words, count, at) => {
    const base = slotU32Offsets[at];
    for (let i = 0;i < count; i++)
      baseU32[base + i] = words[i];
    return count * u32Bytes;
  };
  const readU32Words = (out, count, at) => {
    const base = slotU32Offsets[at];
    for (let i = 0;i < count; i++)
      out[i] = baseU32[base + i];
    return out;
  };
  const canWrite = (start, length) => (start | 0) >= 0 && start + length <= writableBytes;
  const writeUtf8 = (str, at) => {
    const start = slotByteOffsets[at];
    const target = baseU8.subarray(start, start + writableBytes);
    if (!baseBuf) {
      const { read: read2, written: written2 } = sharedBufferEncodeInto(str, target, textCompat);
      if (read2 !== str.length)
        return -1;
      return written2;
    }
    const { read, written } = textEncode2.encodeInto(str, target);
    if (read !== str.length)
      return -1;
    return written;
  };
  const readUtf8 = (start, end, at) => {
    const slotStart = slotByteOffsets[at];
    if (!baseBuf) {
      return sharedBufferDecode(baseU8.subarray(slotStart + start, slotStart + end), textCompat);
    }
    return baseBuf.toString("utf8", slotStart + start, slotStart + end);
  };
  const writeBinary = (src, at, start = 0) => {
    baseU8.set(src, slotByteOffsets[at] + start);
    return src.byteLength;
  };
  const writeBuffer = (src, at, start = 0) => {
    baseU8.set(src, slotByteOffsets[at] + start);
    return src.byteLength;
  };
  const writeArrayBuffer = (src, at, start = 0) => {
    const bytes = src.byteLength;
    baseU8.set(new Uint8Array(src), slotByteOffsets[at] + start);
    return bytes;
  };
  const writeExactUint8Array = (src, at, start = 0) => {
    baseU8.set(src, slotByteOffsets[at] + start);
    return src.byteLength;
  };
  const writeUint8Array = (src, at, start = 0) => {
    if (!isExactUint8Array(src))
      return -1;
    return writeExactUint8Array(src, at, start);
  };
  const write8Binary = (src, at, start = 0) => {
    const bytes = src.byteLength;
    if (!canWrite(start, bytes))
      return -1;
    baseF64.set(src, slotByteOffsets[at] + start >>> 3);
    return bytes;
  };
  const readBytesCopy = (start, end, at) => baseU8.slice(slotByteOffsets[at] + start, slotByteOffsets[at] + end);
  const readBytesView = (start, end, at) => baseU8.subarray(slotByteOffsets[at] + start, slotByteOffsets[at] + end);
  const readBytesBufferCopy = (start, end, at) => {
    if (!bufferCtor || !baseBuf)
      return readBytesCopy(start, end, at);
    const length = end - start;
    const out = bufferCtor.allocUnsafe(length);
    const slotStart = slotByteOffsets[at];
    baseBuf.copy(out, 0, slotStart + start, slotStart + end);
    return out;
  };
  const readUint8ArrayBufferCopy = (start, end, at) => {
    if (!bufferCtor)
      return readBytesCopy(start, end, at);
    const bytes = readBytesBufferCopy(start, end, at);
    return new Uint8Array(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  };
  const readUint8ArraySliceCopy = (start, end, at) => readBytesCopy(start, end, at);
  const readUint8ArrayCopy = IS_BUN ? readUint8ArraySliceCopy : readUint8ArrayBufferCopy;
  const readBytesArrayBufferCopy = (start, end, at) => {
    if (!bufferCtor || !baseBuf) {
      const out2 = readBytesCopy(start, end, at);
      return out2.buffer;
    }
    const length = Math.max(0, end - start | 0);
    if (length === 0)
      return new ArrayBuffer(0);
    const out = bufferCtor.allocUnsafeSlow(length);
    const slotStart = slotByteOffsets[at];
    baseBuf.copy(out, 0, slotStart + start, slotStart + end);
    return out.buffer;
  };
  const read8BytesFloatCopy = (start, end, at) => baseF64.slice(slotByteOffsets[at] + start >>> 3, slotByteOffsets[at] + end >>> 3);
  const read8BytesFloatView = (start, end, at) => baseF64.subarray(slotByteOffsets[at] + start >>> 3, slotByteOffsets[at] + end >>> 3);
  return {
    writeUtf8,
    readUtf8,
    writeBinary,
    writeBuffer,
    writeArrayBuffer,
    writeExactUint8Array,
    writeUint8Array,
    writeU32Words,
    readU32Words,
    write8Binary,
    readBytesCopy,
    readBytesView,
    readBytesBufferCopy,
    readBufferCopy: readBytesBufferCopy,
    readUint8ArrayCopy,
    readUint8ArrayBufferCopy,
    readBytesArrayBufferCopy,
    readArrayBufferCopy: readBytesArrayBufferCopy,
    read8BytesFloatCopy,
    read8BytesFloatView,
    maxBytes: writableBytes
  };
};

// src/error.ts
var ErrorKnitting = {
  Function: 0,
  Symbol: 1,
  Json: 2,
  Serializable: 3
};
var reasonFrom = (task, type, detail) => {
  switch (type) {
    case ErrorKnitting.Function: {
      const name = typeof task.value === "function" ? task.value.name || "<anonymous>" : "<unknown>";
      return `KNT_ERROR_0: Function is not a valid type; name: ${name}`;
    }
    case ErrorKnitting.Symbol:
      return "KNT_ERROR_1: Symbol must use Symbol.for(...) keys";
    case ErrorKnitting.Json:
      return detail == null || detail.length === 0 ? "KNT_ERROR_2: JSON stringify failed; payload must be JSON-safe" : `KNT_ERROR_2: JSON stringify failed; ${detail}`;
    case ErrorKnitting.Serializable:
      return detail == null || detail.length === 0 ? "KNT_ERROR_3: Unsupported payload type; serialize it yourself" : `KNT_ERROR_3: Unsupported payload type; ${detail}`;
  }
};
var encoderError = ({
  task,
  type,
  onPromise,
  detail
}) => {
  const reason = reasonFrom(task, type, detail);
  if (!RUNTIME_IS_MAIN_THREAD) {
    task.value = reason;
    task[TaskIndex.FlagsToHost] = TaskFlag.Reject;
    return false;
  }
  if (onPromise == null) {
    throw new TypeError(reason);
  }
  if (!beginPromisePayload(task))
    return false;
  queueMicrotask(() => {
    finishPromisePayload(task);
    task.value = reason;
    onPromise(task, true, reason);
  });
  return false;
};

// src/common/envelope.ts
var PayloadTransportFinalizer2 = Symbol.for("knitting.payloadCodec.transportFinalizer");

class Envelope {
  header;
  payload;
  constructor(header, payload) {
    this.header = header;
    this.payload = payload;
  }
  [Symbol.dispose]() {
    const body = this.payload;
    if (body !== null && typeof body === "object") {
      body[Symbol.dispose]?.();
    }
  }
  [PayloadTransportFinalizer2]() {
    const body = this.payload;
    if (body === null || typeof body !== "object")
      return;
    const finalizer = body[PayloadTransportFinalizer2];
    return typeof finalizer === "function" ? finalizer.call(body) : undefined;
  }
}

// scripts/browser-stubs/buffer-reference-native.ts
var getBufferReferenceCapabilities = () => {
  throw new Error('BufferReference cannot run in runtime "browser"');
};

// src/connections/shared-array-buffer-payload.ts
var SHARED_ARRAY_BUFFER_CODEC_ID = "knitting.sharedArrayBuffer";
var SHARED_ARRAY_BUFFER_NUMERIC_TRANSFER = Symbol.for("knitting.sharedArrayBuffer.numericTransfer");
var SHARED_ARRAY_BUFFER_NUMERIC_WORDS = 8;
var SHARED_ARRAY_BUFFER_TOKEN_NUMERIC_WORDS = 2;
var EXTERNAL_PAYLOAD_BRAND = Symbol.for("knitting.payloadCodec");
var getProcessId = () => {
  const proc = getNodeProcess();
  if (proc !== undefined && typeof proc.pid === "number")
    return proc.pid;
  const deno = globalThis.Deno;
  if (typeof deno?.pid === "number")
    return deno.pid;
  return 0;
};
var PROCESS_ORIGIN = `${RUNTIME}:${getProcessId()}`;
var hasSharedArrayBuffer = typeof SharedArrayBuffer === "function";
var isSharedArrayBufferValue = (value) => hasSharedArrayBuffer && value instanceof SharedArrayBuffer;
var pinnedBySab = new WeakMap;
var payloadBySharedBuffer = new WeakMap;
var warmedTokensByTransport = new WeakMap;
var cachedSharedBuffersByToken = new Map;
var pinFinalizer = typeof FinalizationRegistry === "function" ? new FinalizationRegistry((token) => {
  try {
    getBufferReferenceCapabilities().releaseShared(token);
  } catch {}
}) : undefined;
var splitU64 = (value) => [
  Number(value & 0xffffffffn) >>> 0,
  Number(value >> 32n & 0xffffffffn) >>> 0
];
var joinU64 = (low, high) => BigInt(high >>> 0) << 32n | BigInt(low >>> 0);
var encodeRuntime = (runtime) => {
  switch (runtime) {
    case "node":
      return 1;
    case "deno":
      return 2;
    case "bun":
      return 3;
    default:
      return 0;
  }
};
var decodeRuntime = (value) => {
  switch (value) {
    case 1:
      return "node";
    case 2:
      return "deno";
    case 3:
      return "bun";
    default:
      return;
  }
};
var getWarmTokens = (transportKey) => {
  if (transportKey === undefined)
    return;
  let warmTokens = warmedTokensByTransport.get(transportKey);
  if (warmTokens === undefined) {
    warmTokens = new Set;
    warmedTokensByTransport.set(transportKey, warmTokens);
  }
  return warmTokens;
};
var pinSab = (sab) => {
  let pin = pinnedBySab.get(sab);
  if (pin === undefined) {
    const produced = getBufferReferenceCapabilities().produceShared(sab);
    pin = {
      token: produced.token,
      pointer: produced.pointer,
      byteLength: produced.byteLength
    };
    pinnedBySab.set(sab, pin);
    pinFinalizer?.register(sab, pin.token);
  }
  return pin;
};
var makeMetadata = (pin) => ({
  kind: SHARED_ARRAY_BUFFER_CODEC_ID,
  origin: PROCESS_ORIGIN,
  runtime: RUNTIME,
  pointer: pin.pointer.toString(),
  token: pin.token.toString(),
  byteLength: pin.byteLength
});
var makeFullNumericMetadata = (pin) => {
  if (pin.byteLength > 4294967295)
    return;
  const [tokenLow, tokenHigh] = splitU64(pin.token);
  const [pointerLow, pointerHigh] = splitU64(pin.pointer);
  return [
    tokenLow,
    tokenHigh,
    pointerLow,
    pointerHigh,
    pin.byteLength >>> 0,
    encodeRuntime(RUNTIME),
    getProcessId() >>> 0,
    0
  ];
};
var makeTokenNumericMetadata = (pin) => {
  const [tokenLow, tokenHigh] = splitU64(pin.token);
  return [tokenLow, tokenHigh];
};
var wrapSharedArrayBufferPayload = (sab) => {
  let payload = payloadBySharedBuffer.get(sab);
  if (payload !== undefined)
    return payload;
  const pin = pinSab(sab);
  payload = createSharedArrayBufferPayload(sab, pin, makeMetadata(pin));
  return payload;
};
var createSharedArrayBufferPayload = (buffer, pin, metadata) => {
  let payload = payloadBySharedBuffer.get(buffer);
  if (payload !== undefined)
    return payload;
  const fullNumeric = makeFullNumericMetadata(pin);
  const tokenOnlyNumeric = makeTokenNumericMetadata(pin);
  payload = {
    [EXTERNAL_PAYLOAD_BRAND]: SHARED_ARRAY_BUFFER_CODEC_ID,
    toMetadata: () => metadata,
    [SHARED_ARRAY_BUFFER_NUMERIC_TRANSFER]: (transportKey) => {
      if (fullNumeric === undefined) {
        return;
      }
      const warmTokens = getWarmTokens(transportKey);
      if (warmTokens === undefined)
        return fullNumeric;
      if (warmTokens.has(pin.token))
        return tokenOnlyNumeric;
      warmTokens.add(pin.token);
      return fullNumeric;
    }
  };
  payloadBySharedBuffer.set(buffer, payload);
  return payload;
};
var getSharedArrayBufferPayload = (value) => {
  if (isSharedArrayBufferValue(value))
    return wrapSharedArrayBufferPayload(value);
  return payloadBySharedBuffer.get(value);
};
var isSharedArrayBufferMetadata = (value) => {
  if (value === null || typeof value !== "object")
    return false;
  const meta = value;
  return meta.kind === SHARED_ARRAY_BUFFER_CODEC_ID && typeof meta.origin === "string" && typeof meta.runtime === "string" && typeof meta.pointer === "string" && typeof meta.token === "string" && typeof meta.byteLength === "number" && Number.isInteger(meta.byteLength) && meta.byteLength >= 0;
};
var materializeSharedBuffer = (metadata, warmOnly) => {
  if (metadata.origin !== PROCESS_ORIGIN) {
    throw new Error(`SharedArrayBuffer cannot cross a process boundary (origin ${metadata.origin} ` + `!= ${PROCESS_ORIGIN}); it is shared by reference to thread workers only.`);
  }
  const token = BigInt(metadata.token);
  const cached = cachedSharedBuffersByToken.get(token);
  if (cached !== undefined)
    return cached;
  if (warmOnly) {
    throw new TypeError("SharedArrayBuffer cache miss for warm token payload");
  }
  const region = getBufferReferenceCapabilities().adoptShared({
    token,
    pointer: BigInt(metadata.pointer),
    byteOffset: 0,
    byteLength: metadata.byteLength
  });
  cachedSharedBuffersByToken.set(token, region.buffer);
  createSharedArrayBufferPayload(region.buffer, {
    token,
    pointer: BigInt(metadata.pointer),
    byteLength: metadata.byteLength
  }, metadata);
  return region.buffer;
};
var decode = (metadata) => {
  if (!isSharedArrayBufferMetadata(metadata)) {
    throw new TypeError("Invalid SharedArrayBuffer payload metadata");
  }
  return materializeSharedBuffer(metadata, false);
};
var decodeNumeric = (words) => {
  if (words.length === SHARED_ARRAY_BUFFER_TOKEN_NUMERIC_WORDS) {
    const token = joinU64(words[0] ?? 0, words[1] ?? 0);
    const cached = cachedSharedBuffersByToken.get(token);
    if (cached !== undefined)
      return cached;
    throw new TypeError("SharedArrayBuffer cache miss for warm token payload");
  }
  const runtime = decodeRuntime(words[5] ?? 0);
  if (runtime === undefined) {
    throw new TypeError("Invalid SharedArrayBuffer numeric runtime");
  }
  const originPid = words[6];
  if (originPid === undefined || !Number.isInteger(originPid) || originPid < 0) {
    throw new TypeError("Invalid SharedArrayBuffer numeric origin");
  }
  if (words.length !== SHARED_ARRAY_BUFFER_NUMERIC_WORDS) {
    throw new TypeError("Invalid SharedArrayBuffer numeric word count");
  }
  const metadata = {
    kind: SHARED_ARRAY_BUFFER_CODEC_ID,
    origin: `${runtime}:${originPid >>> 0}`,
    runtime,
    pointer: joinU64(words[2] ?? 0, words[3] ?? 0).toString(),
    token: joinU64(words[0] ?? 0, words[1] ?? 0).toString(),
    byteLength: words[4] ?? 0
  };
  return materializeSharedBuffer(metadata, false);
};
var codecGlobal = globalThis;
var codecs = codecGlobal.__KNITTING_PAYLOAD_CODECS__ ??= Object.create(null);
codecs[SHARED_ARRAY_BUFFER_CODEC_ID] = { decode, decodeNumeric };

// scripts/browser-stubs/process-shared-buffer.ts
var isProcessSharedBufferValue = (_value) => false;
var unavailable2 = () => {
  throw new Error("ProcessSharedBuffer is unavailable in the browser build");
};

class ProcessSharedBuffer {
  constructor() {
    unavailable2();
  }
  static create = unavailable2;
  static fromMetadata = unavailable2;
  toMetadata = unavailable2;
}

// src/connections/numeric-array.ts
var NUMERIC_ARRAY_BRAND = Symbol.for("knitting.numericArray");

class NumericArray extends Array {
}
Object.defineProperty(NumericArray.prototype, NUMERIC_ARRAY_BRAND, {
  value: true,
  enumerable: false,
  writable: false,
  configurable: false
});
var isNumericArray = (value) => value[NUMERIC_ARRAY_BRAND] === true;
var numericArrayFromFloat64 = (view) => {
  const length = view.length;
  const out = new NumericArray(length);
  for (let i = 0;i < length; i++)
    out[i] = view[i];
  return out;
};

// src/memory/payloadCodec.ts
var memory = new ArrayBuffer(8);
var Float64View = new Float64Array(memory);
var BigInt64View = new BigInt64Array(memory);
var Uint32View = new Uint32Array(memory);
var textEncode3 = new TextEncoder;
var runtimeBufferClass = globalThis.Buffer;
var runtimeBufferByteLength = typeof runtimeBufferClass?.byteLength === "function" ? (value, encoding) => runtimeBufferClass.byteLength(value, encoding) : undefined;
var isRuntimeBuffer = (value) => typeof runtimeBufferClass?.isBuffer === "function" && runtimeBufferClass.isBuffer(value);
var isRuntimeUint8Array = (value) => value != null && typeof value === "object" && Object.getPrototypeOf(value) === Uint8Array.prototype;
var utf8ByteLength = !runtimeBufferByteLength ? (text) => textEncode3.encode(text).byteLength : (text) => runtimeBufferByteLength(text, "utf8");
var BIGINT64_MIN = -(1n << 63n);
var BIGINT64_MAX = (1n << 63n) - 1n;
var { parse: parseJSON, stringify: stringifyJSON } = JSON;
var { for: symbolFor, keyFor: symbolKeyFor } = Symbol;
var EXTERNAL_PAYLOAD_BRAND2 = symbolFor("knitting.payloadCodec");
var BUFFER_REFERENCE_CODEC_ID = "knitting.bufferReference";
var PROCESS_SHARED_BUFFER_CODEC_ID = "knitting.processSharedBuffer";
var externalPayloadGlobal = globalThis;
var objectGetPrototypeOf = Object.getPrototypeOf;
var objectHasOwn = Object.prototype.hasOwnProperty;
var arrayIsArray = Array.isArray;
var objectPrototype = Object.prototype;
var UNSUPPORTED_OBJECT_DETAIL = "Unsupported object type. Allowed: plain object, array, Error, Date, Envelope, Buffer, ArrayBuffer, DataView, typed arrays, and registered external payloads. Serialize it yourself.";
var ENVELOPE_PAYLOAD_DETAIL = "Envelope payload must be an ArrayBuffer, SharedArrayBuffer, " + "ProcessSharedBuffer, or BufferReference.";
var ENVELOPE_HEADER_DETAIL = "Envelope header must be a JSON-like value or string.";
var ENVELOPE_PROMISE_DETAIL = "Envelope header cannot contain Promise values.";
var DYNAMIC_PAYLOAD_LIMIT_DETAIL = "Dynamic payload exceeds maxPayloadBytes.";
var DYNAMIC_PAYLOAD_CAPACITY_DETAIL = "Dynamic payload buffer capacity exceeded.";
var PROCESS_BOUNDARY_POINTER_PAYLOAD_DETAIL = "SharedArrayBuffer and BufferReference are process-local pointer payloads " + "and cannot cross a process-worker boundary; use ProcessSharedBuffer instead.";
var RESERVED_EXTERNAL_PAYLOAD_DETAIL = "Reserved Knitting external payload codec cannot be forged.";
var isProcessLocalPointerCodec = (codecId) => codecId === SHARED_ARRAY_BUFFER_CODEC_ID || codecId === BUFFER_REFERENCE_CODEC_ID;
var isReservedExternalPayloadCodec = (codecId) => isProcessLocalPointerCodec(codecId) || codecId === PROCESS_SHARED_BUFFER_CODEC_ID;
var isPlainJsonObject = (value) => {
  const proto = objectGetPrototypeOf(value);
  return proto === objectPrototype || proto === null;
};
var readExternalPayloadCodecId = (value) => {
  const codecId = value[EXTERNAL_PAYLOAD_BRAND2];
  return typeof codecId === "string" ? codecId : undefined;
};
var runtimeCode = (value) => {
  switch (value) {
    case "node":
      return 1;
    case "deno":
      return 2;
    case "bun":
      return 3;
    default:
      return 0;
  }
};
var kindCode = (value) => {
  switch (value) {
    case "shared-array-buffer":
      return 1;
    case "external-array-buffer":
      return 2;
    default:
      return 0;
  }
};
var isU32 = (value) => typeof value === "number" && Number.isInteger(value) && value >= 0 && value <= 4294967295;
var isExternalPayloadLike = (value) => typeof value.toMetadata === "function" && typeof value[EXTERNAL_PAYLOAD_BRAND2] === "string";
var readTrustedExternalPayloadMetadata = (value) => {
  if (isBufferReferenceValue(value)) {
    return BufferReference.prototype.toMetadata.call(value);
  }
  if (isProcessSharedBufferValue(value)) {
    return ProcessSharedBuffer.prototype.toMetadata.call(value);
  }
  return value.toMetadata();
};
var decodeExternalPayload = (raw, processBoundary) => {
  const payload = parseJSON(raw);
  if (!arrayIsArray(payload) || payload.length !== 2)
    return payload;
  const codecId = payload[0];
  const metadata = payload[1];
  if (typeof codecId !== "string") {
    return { codec: codecId, metadata };
  }
  if (processBoundary && isProcessLocalPointerCodec(codecId)) {
    throw new TypeError(PROCESS_BOUNDARY_POINTER_PAYLOAD_DETAIL);
  }
  const codec = externalPayloadGlobal.__KNITTING_PAYLOAD_CODECS__?.[codecId];
  return typeof codec?.decode === "function" ? codec.decode(metadata) : { codec: codecId, metadata };
};
var PROCESS_SHARED_BUFFER_NUMERIC_WORDS = 8;
var BUFFER_REFERENCE_NUMERIC_WORDS = 8;
var NUMERIC_SENTINEL = 4294967295;
var decodeNumericExternalPayload = (codecId, words) => {
  const codec = externalPayloadGlobal.__KNITTING_PAYLOAD_CODECS__?.[codecId];
  if (typeof codec?.decodeNumeric === "function") {
    return codec.decodeNumeric(words);
  }
  return { codec: codecId, metadata: Array.from(words) };
};
var decodeProcessSharedBufferNumericWords = (words) => decodeNumericExternalPayload(PROCESS_SHARED_BUFFER_CODEC_ID, words);
var decodeBufferReferenceNumericWords = (words) => decodeNumericExternalPayload(BUFFER_REFERENCE_CODEC_ID, words);
var decodeSharedArrayBufferNumericWords = (words) => decodeNumericExternalPayload(SHARED_ARRAY_BUFFER_CODEC_ID, words);
var tryEncodePrimitiveTask = (task) => {
  const value = task.value;
  switch (typeof value) {
    case "number":
      if (value !== value) {
        task[TaskIndex.Type] = PayloadSignal.NaN;
        return true;
      }
      Float64View[0] = value;
      task[TaskIndex.Type] = PayloadSignal.Float64;
      task[TaskIndex.Start] = Uint32View[0];
      task[TaskIndex.End] = Uint32View[1];
      return true;
    case "boolean":
      task[TaskIndex.Type] = value ? PayloadSignal.True : PayloadSignal.False;
      return true;
    case "undefined":
      task[TaskIndex.Type] = PayloadSignal.Undefined;
      return true;
    case "bigint":
      if (value < BIGINT64_MIN || value > BIGINT64_MAX)
        return false;
      BigInt64View[0] = value;
      task[TaskIndex.Type] = PayloadSignal.BigInt;
      task[TaskIndex.Start] = Uint32View[0];
      task[TaskIndex.End] = Uint32View[1];
      return true;
    case "object":
      if (value === null) {
        task[TaskIndex.Type] = PayloadSignal.Null;
        return true;
      }
      return false;
    default:
      return false;
  }
};
var hasPromiseInEnvelopeHeader = (value, seen) => {
  if (value instanceof Promise)
    return true;
  if (value === null || typeof value !== "object")
    return false;
  const objectValue = value;
  const visited = seen ?? new Set;
  if (visited.has(objectValue))
    return false;
  visited.add(objectValue);
  if (arrayIsArray(objectValue)) {
    const list = objectValue;
    for (let i = 0;i < list.length; i++) {
      if (hasPromiseInEnvelopeHeader(list[i], visited))
        return true;
    }
    return false;
  }
  if (!isPlainJsonObject(objectValue))
    return false;
  const record = objectValue;
  for (const key in record) {
    if (!objectHasOwn.call(record, key))
      continue;
    if (hasPromiseInEnvelopeHeader(record[key], visited))
      return true;
  }
  return false;
};
var toErrorCause = (cause) => {
  if (cause === null || cause === undefined)
    return cause;
  switch (typeof cause) {
    case "string":
    case "number":
    case "boolean":
      return cause;
    case "bigint":
      return cause.toString();
    case "symbol":
    case "function":
      return String(cause);
  }
  if (cause instanceof Error) {
    const nested = {
      name: cause.name,
      message: cause.message
    };
    if (typeof cause.stack === "string")
      nested.stack = cause.stack;
    if (objectHasOwn.call(cause, "cause")) {
      nested.cause = toErrorCause(cause.cause);
    }
    return nested;
  }
  try {
    return parseJSON(stringifyJSON(cause));
  } catch {
    return String(cause);
  }
};
var toErrorPayload = (error) => {
  const payload = {
    name: error.name,
    message: error.message
  };
  if (typeof error.stack === "string")
    payload.stack = error.stack;
  if (objectHasOwn.call(error, "cause")) {
    payload.cause = toErrorCause(error.cause);
  }
  return payload;
};
var parseErrorPayload = (raw) => {
  let parsed;
  try {
    parsed = parseJSON(raw);
  } catch {
    return new Error(raw);
  }
  if (parsed == null || typeof parsed !== "object") {
    return new Error(String(parsed));
  }
  const payload = parsed;
  const err = new Error(typeof payload.message === "string" ? payload.message : "");
  if (typeof payload.name === "string" && payload.name.length > 0) {
    err.name = payload.name;
  }
  if (typeof payload.stack === "string") {
    try {
      err.stack = payload.stack;
    } catch {}
  }
  if (objectHasOwn.call(payload, "cause")) {
    err.cause = payload.cause;
  }
  return err;
};
var decodeBigIntBinary = (bytes) => {
  const sign = bytes[0];
  let value = 0n;
  for (let i = bytes.length - 1;i >= 1; i--) {
    value = value << 8n | BigInt(bytes[i]);
  }
  return sign === 1 ? -value : value;
};
var initStaticIO = (headersBuffer, headerSlotStrideU32, textCompat) => {
  const slotStride = headerSlotStrideU32 ?? HEADER_SLOT_STRIDE_U32;
  const requiredBytes = getStridedRegionSpanBytes({
    slotCount: LockBound.slots,
    slotStrideU32: slotStride,
    slotLengthU32: HEADER_STATIC_PAYLOAD_U32,
    baseU32: LockBound.header
  });
  if (headersBuffer.byteLength < Math.max(requiredBytes, HEADER_BYTE_LENGTH)) {
    return null;
  }
  return createSharedStaticBufferIO({
    headersBuffer,
    slotStrideU32: slotStride,
    textCompat
  });
};
var requireStaticIO = (headersBuffer, headerSlotStrideU32, textCompat) => {
  const staticIO = initStaticIO(headersBuffer, headerSlotStrideU32, textCompat);
  if (staticIO === null) {
    throw new RangeError("headersBuffer is too small for static payload IO");
  }
  return staticIO;
};
var encodePayload = ({
  lockSector,
  payload,
  sab,
  payloadConfig,
  headersBuffer,
  headerSlotStrideU32,
  textCompat,
  onPromise,
  processBoundary = false
}) => {
  const payloadSab = payload?.sab ?? sab;
  const resolvedPayloadConfig = resolvePayloadBufferOptions({
    sab: payloadSab,
    options: payload?.config ?? payloadConfig
  });
  const maxPayloadBytes = resolvedPayloadConfig.maxPayloadBytes;
  const { allocTask, setSlotLength, free } = register({ lockSector });
  const {
    writeBinary: writeDynamicBinary,
    writeBuffer: writeDynamicBuffer,
    writeArrayBuffer: writeDynamicArrayBuffer,
    write8Binary: writeDynamic8Binary,
    writeUtf8: writeDynamicUtf8
  } = createSharedDynamicBufferIO({
    sab: payloadSab,
    payloadConfig: resolvedPayloadConfig,
    textCompat: textCompat?.payload
  });
  const {
    maxBytes: staticMaxBytes,
    writeBinary: writeStaticBinary,
    writeBuffer: writeStaticBuffer,
    writeArrayBuffer: writeStaticArrayBuffer,
    writeExactUint8Array: writeStaticExactUint8Array,
    writeU32Words: writeStaticU32Words,
    write8Binary: writeStatic8Binary,
    writeUtf8: writeStaticUtf8
  } = requireStaticIO(headersBuffer, headerSlotStrideU32, textCompat?.headers);
  const dynamicLimitError = (task, actualBytes, label) => encoderError({
    task,
    type: ErrorKnitting.Serializable,
    onPromise,
    detail: `${DYNAMIC_PAYLOAD_LIMIT_DETAIL} limit=${maxPayloadBytes}; ` + `actual=${actualBytes}; type=${label}.`
  });
  const dynamicCapacityError = (task) => encoderError({
    task,
    type: ErrorKnitting.Serializable,
    onPromise,
    detail: DYNAMIC_PAYLOAD_CAPACITY_DETAIL
  });
  const ensureWithinDynamicLimit = (task, bytes, label) => {
    if (bytes <= maxPayloadBytes)
      return true;
    return dynamicLimitError(task, bytes, label);
  };
  const dynamicUtf8ReserveBytesWithExtra = (task, text, extraBytes, label) => {
    const estimatedBytes = text.length * 3;
    const estimatedTotal = estimatedBytes + extraBytes;
    if (estimatedTotal <= maxPayloadBytes)
      return estimatedBytes;
    const exactBytes = utf8ByteLength(text);
    const exactTotal = exactBytes + extraBytes;
    if (exactTotal > maxPayloadBytes) {
      dynamicLimitError(task, exactTotal, label);
      return -1;
    }
    return exactBytes;
  };
  const dynamicUtf8ReserveBytes = (task, text, label) => dynamicUtf8ReserveBytesWithExtra(task, text, 0, label);
  const reserveDynamic = (task, bytes) => {
    task[TaskIndex.PayloadLen] = bytes;
    return allocTask(task);
  };
  let objectDynamicSlot = -1;
  const reserveDynamicObject = (task, bytes) => {
    task[TaskIndex.PayloadLen] = bytes;
    const reservedSlot = allocTask(task);
    objectDynamicSlot = reservedSlot;
    return reservedSlot;
  };
  const rollbackObjectDynamic = () => {
    if (objectDynamicSlot !== -1) {
      free(objectDynamicSlot);
      objectDynamicSlot = -1;
    }
  };
  const failDynamicWriteAfterReserve = (task, reservedSlot) => {
    free(reservedSlot);
    if (objectDynamicSlot === reservedSlot)
      objectDynamicSlot = -1;
    return dynamicCapacityError(task);
  };
  let bigintScratch = new Uint8Array(16);
  const encodeBigIntIntoScratch = (value) => {
    let sign = 0;
    let abs = value;
    if (value < 0n) {
      sign = 1;
      abs = -value;
    }
    let at = 1;
    while (abs > 0n) {
      if (at >= bigintScratch.byteLength) {
        const next = new Uint8Array(bigintScratch.byteLength << 1);
        next.set(bigintScratch, 0);
        bigintScratch = next;
      }
      bigintScratch[at++] = Number(abs & 0xffn);
      abs >>= 8n;
    }
    bigintScratch[0] = sign;
    return at;
  };
  const clearBigIntScratch = (used) => {
    bigintScratch.fill(0, 0, used);
  };
  const encodeErrorObject = (task, error) => {
    let text;
    try {
      text = stringifyJSON(toErrorPayload(error));
    } catch (encodeErrorReason) {
      const detail = encodeErrorReason instanceof Error ? encodeErrorReason.message : String(encodeErrorReason);
      return encoderError({
        task,
        type: ErrorKnitting.Serializable,
        onPromise,
        detail
      });
    }
    const reserveBytes = dynamicUtf8ReserveBytes(task, text, "Error");
    if (reserveBytes < 0)
      return false;
    task[TaskIndex.Type] = PayloadBuffer.Error;
    const reservedSlot = reserveDynamicObject(task, reserveBytes);
    const written = writeDynamicUtf8(text, task[TaskIndex.Start], reserveBytes);
    if (written < 0)
      return failDynamicWriteAfterReserve(task, reservedSlot);
    task[TaskIndex.PayloadLen] = written;
    setSlotLength(reservedSlot, written);
    task.value = null;
    return true;
  };
  const encodeObjectBinary = (task, slotIndex, bytesView, dynamicType, staticType) => {
    const bytes = bytesView.byteLength;
    if (bytes <= staticMaxBytes) {
      const written2 = writeStaticBinary(bytesView, slotIndex);
      if (written2 !== -1) {
        task[TaskIndex.Type] = staticType;
        task[TaskIndex.PayloadLen] = written2;
        task.value = null;
        return true;
      }
    }
    task[TaskIndex.Type] = dynamicType;
    if (!ensureWithinDynamicLimit(task, bytes, payloadBufferName(dynamicType))) {
      return false;
    }
    const reservedSlot = reserveDynamicObject(task, bytes);
    const written = writeDynamicBinary(bytesView, task[TaskIndex.Start]);
    if (written < 0)
      return failDynamicWriteAfterReserve(task, reservedSlot);
    task[TaskIndex.PayloadLen] = written;
    setSlotLength(reservedSlot, written);
    task.value = null;
    return true;
  };
  const encodeObjectUint8Array = (task, slotIndex, bytesView) => {
    const bytes = bytesView.byteLength;
    if (bytes <= staticMaxBytes) {
      writeStaticExactUint8Array(bytesView, slotIndex);
      task[TaskIndex.Type] = PayloadBuffer.StaticBinary;
      task[TaskIndex.PayloadLen] = bytes;
      task.value = null;
      return true;
    }
    task[TaskIndex.Type] = PayloadBuffer.Binary;
    if (!ensureWithinDynamicLimit(task, bytes, "Binary"))
      return false;
    const reservedSlot = reserveDynamicObject(task, bytes);
    const written = writeDynamicBinary(bytesView, task[TaskIndex.Start]);
    if (written < 0)
      return failDynamicWriteAfterReserve(task, reservedSlot);
    task[TaskIndex.PayloadLen] = written;
    setSlotLength(reservedSlot, written);
    task.value = null;
    return true;
  };
  const encodeObjectBuffer = (task, slotIndex, buffer) => {
    const bytes = buffer.byteLength;
    if (bytes <= staticMaxBytes) {
      const written2 = writeStaticBuffer(buffer, slotIndex);
      if (written2 !== -1) {
        task[TaskIndex.Type] = PayloadBuffer.StaticBuffer;
        task[TaskIndex.PayloadLen] = written2;
        task.value = null;
        return true;
      }
    }
    task[TaskIndex.Type] = PayloadBuffer.Buffer;
    if (!ensureWithinDynamicLimit(task, bytes, "Buffer"))
      return false;
    const reservedSlot = reserveDynamicObject(task, bytes);
    const written = writeDynamicBuffer(buffer, task[TaskIndex.Start]);
    if (written < 0)
      return failDynamicWriteAfterReserve(task, reservedSlot);
    task[TaskIndex.PayloadLen] = written;
    setSlotLength(reservedSlot, written);
    task.value = null;
    return true;
  };
  const encodeObjectFloat64Array = (task, slotIndex, float64) => {
    const bytes = float64.byteLength;
    if (bytes <= staticMaxBytes) {
      const written2 = writeStatic8Binary(float64, slotIndex);
      if (written2 !== -1) {
        task[TaskIndex.Type] = PayloadBuffer.StaticFloat64Array;
        task[TaskIndex.PayloadLen] = written2;
        task.value = null;
        return true;
      }
    }
    task[TaskIndex.Type] = PayloadBuffer.Float64Array;
    if (!ensureWithinDynamicLimit(task, bytes, "Float64Array"))
      return false;
    const reservedSlot = reserveDynamicObject(task, bytes);
    const written = writeDynamic8Binary(float64, task[TaskIndex.Start]);
    if (written < 0)
      return failDynamicWriteAfterReserve(task, reservedSlot);
    task[TaskIndex.PayloadLen] = written;
    setSlotLength(reservedSlot, written);
    task.value = null;
    return true;
  };
  let numericArrayScratch = new Float64Array(0);
  const encodeObjectNumericArray = (task, slotIndex, numericArray) => {
    const length = numericArray.length;
    if (numericArrayScratch.length < length) {
      numericArrayScratch = new Float64Array(length);
    }
    for (let i = 0;i < length; i++)
      numericArrayScratch[i] = numericArray[i];
    const float64 = numericArrayScratch.subarray(0, length);
    const bytes = float64.byteLength;
    if (bytes <= staticMaxBytes) {
      const written2 = writeStatic8Binary(float64, slotIndex);
      if (written2 !== -1) {
        task[TaskIndex.Type] = PayloadBuffer.StaticNumericArray;
        task[TaskIndex.PayloadLen] = written2;
        task.value = null;
        return true;
      }
    }
    task[TaskIndex.Type] = PayloadBuffer.NumericArray;
    if (!ensureWithinDynamicLimit(task, bytes, "NumericArray"))
      return false;
    const reservedSlot = reserveDynamicObject(task, bytes);
    const written = writeDynamic8Binary(float64, task[TaskIndex.Start]);
    if (written < 0)
      return failDynamicWriteAfterReserve(task, reservedSlot);
    task[TaskIndex.PayloadLen] = written;
    setSlotLength(reservedSlot, written);
    task.value = null;
    return true;
  };
  const encodeObjectArrayBuffer = (task, slotIndex, arrayBuffer) => {
    const bytes = arrayBuffer.byteLength;
    if (bytes <= staticMaxBytes) {
      const written2 = writeStaticArrayBuffer(arrayBuffer, slotIndex);
      if (written2 !== -1) {
        task[TaskIndex.Type] = PayloadBuffer.StaticArrayBuffer;
        task[TaskIndex.PayloadLen] = written2;
        task.value = null;
        return true;
      }
    }
    task[TaskIndex.Type] = PayloadBuffer.ArrayBuffer;
    if (!ensureWithinDynamicLimit(task, bytes, "ArrayBuffer"))
      return false;
    const reservedSlot = reserveDynamicObject(task, bytes);
    const written = writeDynamicArrayBuffer(arrayBuffer, task[TaskIndex.Start]);
    if (written < 0)
      return failDynamicWriteAfterReserve(task, reservedSlot);
    task[TaskIndex.PayloadLen] = written;
    setSlotLength(reservedSlot, written);
    task.value = null;
    return true;
  };
  const processSharedBufferWords = new Uint32Array(PROCESS_SHARED_BUFFER_NUMERIC_WORDS);
  const sharedArrayBufferWords = new Uint32Array(SHARED_ARRAY_BUFFER_NUMERIC_WORDS);
  const tryEncodeProcessSharedBufferNumeric = (task, slotIndex, value) => {
    const descriptor = value.descriptor;
    if (descriptor === undefined || descriptor.name !== undefined || !isU32(descriptor.fd) || !isU32(descriptor.size) || !isU32(descriptor.byteLength) || !isU32(value.byteOffset) || !isU32(value.byteLength)) {
      return false;
    }
    const baseAddressMod64 = descriptor.baseAddressMod64;
    if (baseAddressMod64 !== undefined && !isU32(baseAddressMod64)) {
      return false;
    }
    processSharedBufferWords[0] = descriptor.fd;
    processSharedBufferWords[1] = descriptor.size;
    processSharedBufferWords[2] = descriptor.byteLength;
    processSharedBufferWords[3] = value.byteOffset;
    processSharedBufferWords[4] = value.byteLength;
    processSharedBufferWords[5] = runtimeCode(descriptor.runtime);
    processSharedBufferWords[6] = kindCode(descriptor.kind);
    processSharedBufferWords[7] = baseAddressMod64 === undefined ? NUMERIC_SENTINEL : baseAddressMod64;
    task[TaskIndex.Type] = PayloadBuffer.ProcessSharedBuffer;
    task[TaskIndex.PayloadLen] = writeStaticU32Words(processSharedBufferWords, PROCESS_SHARED_BUFFER_NUMERIC_WORDS, slotIndex);
    task.value = null;
    return true;
  };
  const tryEncodeBufferReferenceNumeric = (task, slotIndex, value) => {
    const words = isBufferReferenceValue(value) ? BufferReference.prototype[BUFFER_REFERENCE_NUMERIC_TRANSFER].call(value) : value[BUFFER_REFERENCE_NUMERIC_TRANSFER]?.();
    if (words === undefined)
      return false;
    task[TaskIndex.Type] = PayloadBuffer.BufferReference;
    task[TaskIndex.PayloadLen] = writeStaticU32Words(words, BUFFER_REFERENCE_NUMERIC_WORDS, slotIndex);
    attachPayloadTransportFinalizer(task, value);
    task.value = null;
    return true;
  };
  const tryEncodeSharedArrayBufferNumeric = (task, slotIndex, value) => {
    const words = value[SHARED_ARRAY_BUFFER_NUMERIC_TRANSFER]?.(lockSector);
    if (words === undefined)
      return false;
    sharedArrayBufferWords[0] = words[0] ?? 0;
    sharedArrayBufferWords[1] = words[1] ?? 0;
    sharedArrayBufferWords[2] = words[2] ?? 0;
    sharedArrayBufferWords[3] = words[3] ?? 0;
    sharedArrayBufferWords[4] = words[4] ?? 0;
    sharedArrayBufferWords[5] = words[5] ?? 0;
    sharedArrayBufferWords[6] = words[6] ?? 0;
    sharedArrayBufferWords[7] = words[7] ?? 0;
    task[TaskIndex.Type] = PayloadBuffer.SharedArrayBuffer;
    task[TaskIndex.PayloadLen] = writeStaticU32Words(sharedArrayBufferWords, words.length, slotIndex);
    task.value = null;
    return true;
  };
  const encodeObjectExternalPayload = (task, slotIndex, externalPayload, trustedReservedCodec = false) => {
    const codecId = readExternalPayloadCodecId(externalPayload);
    if (codecId === undefined) {
      return encoderError({
        task,
        type: ErrorKnitting.Serializable,
        onPromise,
        detail: UNSUPPORTED_OBJECT_DETAIL
      });
    }
    if (trustedReservedCodec) {
      if (processBoundary && isProcessLocalPointerCodec(codecId)) {
        return encoderError({
          task,
          type: ErrorKnitting.Serializable,
          onPromise,
          detail: PROCESS_BOUNDARY_POINTER_PAYLOAD_DETAIL
        });
      }
      if (codecId === SHARED_ARRAY_BUFFER_CODEC_ID && tryEncodeSharedArrayBufferNumeric(task, slotIndex, externalPayload)) {
        return true;
      }
      if (codecId === BUFFER_REFERENCE_CODEC_ID && tryEncodeBufferReferenceNumeric(task, slotIndex, externalPayload)) {
        return true;
      }
      if (codecId === PROCESS_SHARED_BUFFER_CODEC_ID && tryEncodeProcessSharedBufferNumeric(task, slotIndex, externalPayload)) {
        return true;
      }
    } else if (isReservedExternalPayloadCodec(codecId)) {
      return encoderError({
        task,
        type: ErrorKnitting.Serializable,
        onPromise,
        detail: processBoundary && isProcessLocalPointerCodec(codecId) ? PROCESS_BOUNDARY_POINTER_PAYLOAD_DETAIL : RESERVED_EXTERNAL_PAYLOAD_DETAIL
      });
    }
    let text;
    try {
      text = stringifyJSON([
        codecId,
        trustedReservedCodec ? readTrustedExternalPayloadMetadata(externalPayload) : externalPayload.toMetadata()
      ]);
    } catch (error) {
      const detail = error instanceof Error ? error.message : String(error);
      return encoderError({
        task,
        type: ErrorKnitting.Serializable,
        onPromise,
        detail
      });
    }
    if (typeof text !== "string") {
      return encoderError({
        task,
        type: ErrorKnitting.Serializable,
        onPromise,
        detail: "External payload metadata must be JSON serializable."
      });
    }
    if (text.length <= staticMaxBytes) {
      const written2 = writeStaticUtf8(text, slotIndex);
      if (written2 !== -1) {
        task[TaskIndex.Type] = PayloadBuffer.StaticExternalPayload;
        task[TaskIndex.PayloadLen] = written2;
        attachPayloadTransportFinalizer(task, externalPayload);
        task.value = null;
        return true;
      }
    }
    task[TaskIndex.Type] = PayloadBuffer.ExternalPayload;
    const reserveBytes = dynamicUtf8ReserveBytes(task, text, "ExternalPayload");
    if (reserveBytes < 0)
      return false;
    const reservedSlot = reserveDynamicObject(task, reserveBytes);
    const written = writeDynamicUtf8(text, task[TaskIndex.Start], reserveBytes);
    if (written < 0)
      return failDynamicWriteAfterReserve(task, reservedSlot);
    task[TaskIndex.PayloadLen] = written;
    setSlotLength(reservedSlot, written);
    attachPayloadTransportFinalizer(task, externalPayload);
    task.value = null;
    return true;
  };
  const encodeObjectDate = (task, date) => {
    Float64View[0] = date.getTime();
    task[TaskIndex.Type] = PayloadBuffer.Date;
    task[TaskIndex.Start] = Uint32View[0];
    task[TaskIndex.End] = Uint32View[1];
    task.value = null;
    return true;
  };
  const encodeEnvelopeHeaderText = (task, header, headerIsString) => {
    if (hasPromiseInEnvelopeHeader(header)) {
      encoderError({
        task,
        type: ErrorKnitting.Serializable,
        onPromise,
        detail: ENVELOPE_PROMISE_DETAIL
      });
      return;
    }
    if (headerIsString)
      return header;
    let headerText;
    try {
      headerText = stringifyJSON(header);
    } catch (error) {
      const detail = error instanceof Error ? error.message : String(error);
      encoderError({ task, type: ErrorKnitting.Json, onPromise, detail });
      return;
    }
    if (typeof headerText !== "string") {
      encoderError({
        task,
        type: ErrorKnitting.Serializable,
        onPromise,
        detail: ENVELOPE_HEADER_DETAIL
      });
      return;
    }
    return headerText;
  };
  const resolveEnvelopeExternalBody = (body) => {
    if (body === null || typeof body !== "object")
      return;
    const sharedArrayBuffer = getSharedArrayBufferPayload(body);
    if (sharedArrayBuffer !== undefined) {
      return { payload: sharedArrayBuffer, trustedReservedCodec: true };
    }
    if (isBufferReferenceValue(body) || isProcessSharedBufferValue(body)) {
      return {
        payload: body,
        trustedReservedCodec: true
      };
    }
    if (isExternalPayloadLike(body)) {
      return {
        payload: body,
        trustedReservedCodec: false
      };
    }
    return;
  };
  const encodeEnvelopeArrayBufferBody = (task, slotIndex, headerText, headerIsString, payload2) => {
    const payloadBytes = new Uint8Array(payload2);
    const payloadLength = payloadBytes.byteLength;
    const payloadReserveBytes = payloadLength > 0 ? payloadLength : 1;
    const staticHeaderWritten = writeStaticUtf8(headerText, slotIndex);
    if (staticHeaderWritten !== -1) {
      if (!ensureWithinDynamicLimit(task, payloadReserveBytes, "EnvelopeStaticHeaderPayload"))
        return false;
      const reservedSlot2 = reserveDynamicObject(task, payloadReserveBytes);
      task[TaskIndex.Type] = headerIsString ? PayloadBuffer.EnvelopeStaticHeaderString : PayloadBuffer.EnvelopeStaticHeader;
      task[TaskIndex.PayloadLen] = staticHeaderWritten;
      task[TaskIndex.End] = payloadLength;
      if (payloadLength > 0) {
        const payloadWritten = writeDynamicBinary(payloadBytes, task[TaskIndex.Start]);
        if (payloadWritten < 0) {
          return failDynamicWriteAfterReserve(task, reservedSlot2);
        }
        setSlotLength(reservedSlot2, payloadWritten);
      }
      task.value = null;
      return true;
    }
    const headerReserveBytes = dynamicUtf8ReserveBytesWithExtra(task, headerText, payloadLength, headerIsString ? "EnvelopeDynamicHeaderString" : "EnvelopeDynamicHeader");
    if (headerReserveBytes < 0)
      return false;
    task[TaskIndex.Type] = headerIsString ? PayloadBuffer.EnvelopeDynamicHeaderString : PayloadBuffer.EnvelopeDynamicHeader;
    const reservedSlot = reserveDynamicObject(task, headerReserveBytes + payloadLength);
    const baseStart = task[TaskIndex.Start];
    const writtenHeaderBytes = writeDynamicUtf8(headerText, baseStart, headerReserveBytes);
    if (writtenHeaderBytes < 0) {
      return failDynamicWriteAfterReserve(task, reservedSlot);
    }
    if (payloadLength > 0) {
      const payloadWritten = writeDynamicBinary(payloadBytes, baseStart + writtenHeaderBytes);
      if (payloadWritten < 0) {
        return failDynamicWriteAfterReserve(task, reservedSlot);
      }
    }
    task[TaskIndex.PayloadLen] = writtenHeaderBytes;
    task[TaskIndex.End] = payloadLength;
    setSlotLength(reservedSlot, writtenHeaderBytes + payloadLength);
    task.value = null;
    return true;
  };
  const encodeEnvelopeExternalBody = (task, slotIndex, headerText, headerIsString, externalBody, trustedReservedCodec) => {
    const codecId = readExternalPayloadCodecId(externalBody);
    if (codecId === undefined) {
      return encoderError({
        task,
        type: ErrorKnitting.Serializable,
        onPromise,
        detail: ENVELOPE_PAYLOAD_DETAIL
      });
    }
    if (trustedReservedCodec) {
      if (processBoundary && isProcessLocalPointerCodec(codecId)) {
        return encoderError({
          task,
          type: ErrorKnitting.Serializable,
          onPromise,
          detail: PROCESS_BOUNDARY_POINTER_PAYLOAD_DETAIL
        });
      }
    } else if (isReservedExternalPayloadCodec(codecId)) {
      return encoderError({
        task,
        type: ErrorKnitting.Serializable,
        onPromise,
        detail: processBoundary && isProcessLocalPointerCodec(codecId) ? PROCESS_BOUNDARY_POINTER_PAYLOAD_DETAIL : RESERVED_EXTERNAL_PAYLOAD_DETAIL
      });
    }
    let bodyText;
    try {
      bodyText = stringifyJSON([
        codecId,
        trustedReservedCodec ? readTrustedExternalPayloadMetadata(externalBody) : externalBody.toMetadata()
      ]);
    } catch (error) {
      const detail = error instanceof Error ? error.message : String(error);
      return encoderError({
        task,
        type: ErrorKnitting.Serializable,
        onPromise,
        detail
      });
    }
    if (typeof bodyText !== "string") {
      return encoderError({
        task,
        type: ErrorKnitting.Serializable,
        onPromise,
        detail: "Envelope body metadata must be JSON serializable."
      });
    }
    const bodyBytes = textEncode3.encode(bodyText);
    const bodyLength = bodyBytes.byteLength;
    const staticHeaderWritten = writeStaticUtf8(headerText, slotIndex);
    if (staticHeaderWritten !== -1) {
      if (!ensureWithinDynamicLimit(task, bodyLength, "EnvelopeStaticHeaderExternal"))
        return false;
      const reservedSlot2 = reserveDynamicObject(task, bodyLength);
      task[TaskIndex.Type] = headerIsString ? PayloadBuffer.EnvelopeStaticHeaderStringExternal : PayloadBuffer.EnvelopeStaticHeaderExternal;
      task[TaskIndex.PayloadLen] = staticHeaderWritten;
      task[TaskIndex.End] = bodyLength;
      const bodyWritten2 = writeDynamicBinary(bodyBytes, task[TaskIndex.Start]);
      if (bodyWritten2 < 0) {
        return failDynamicWriteAfterReserve(task, reservedSlot2);
      }
      setSlotLength(reservedSlot2, bodyWritten2);
      attachPayloadTransportFinalizer(task, externalBody);
      task.value = null;
      return true;
    }
    const headerReserveBytes = dynamicUtf8ReserveBytesWithExtra(task, headerText, bodyLength, headerIsString ? "EnvelopeDynamicHeaderStringExternal" : "EnvelopeDynamicHeaderExternal");
    if (headerReserveBytes < 0)
      return false;
    task[TaskIndex.Type] = headerIsString ? PayloadBuffer.EnvelopeDynamicHeaderStringExternal : PayloadBuffer.EnvelopeDynamicHeaderExternal;
    const reservedSlot = reserveDynamicObject(task, headerReserveBytes + bodyLength);
    const baseStart = task[TaskIndex.Start];
    const writtenHeaderBytes = writeDynamicUtf8(headerText, baseStart, headerReserveBytes);
    if (writtenHeaderBytes < 0) {
      return failDynamicWriteAfterReserve(task, reservedSlot);
    }
    const bodyWritten = writeDynamicBinary(bodyBytes, baseStart + writtenHeaderBytes);
    if (bodyWritten < 0) {
      return failDynamicWriteAfterReserve(task, reservedSlot);
    }
    task[TaskIndex.PayloadLen] = writtenHeaderBytes;
    task[TaskIndex.End] = bodyLength;
    setSlotLength(reservedSlot, writtenHeaderBytes + bodyLength);
    attachPayloadTransportFinalizer(task, externalBody);
    task.value = null;
    return true;
  };
  const encodeObjectEnvelope = (task, slotIndex, envelope) => {
    const header = envelope.header;
    const payload2 = envelope.payload;
    const headerIsString = typeof header === "string";
    if (payload2 instanceof ArrayBuffer) {
      const headerText = encodeEnvelopeHeaderText(task, header, headerIsString);
      if (headerText === undefined)
        return false;
      return encodeEnvelopeArrayBufferBody(task, slotIndex, headerText, headerIsString, payload2);
    }
    const externalBody = resolveEnvelopeExternalBody(payload2);
    if (externalBody !== undefined) {
      const headerText = encodeEnvelopeHeaderText(task, header, headerIsString);
      if (headerText === undefined)
        return false;
      return encodeEnvelopeExternalBody(task, slotIndex, headerText, headerIsString, externalBody.payload, externalBody.trustedReservedCodec);
    }
    return encoderError({
      task,
      type: ErrorKnitting.Serializable,
      onPromise,
      detail: ENVELOPE_PAYLOAD_DETAIL
    });
  };
  const encodeObjectPromise = (task, promise) => {
    if (beginPromisePayload(task)) {
      promise.then((value) => {
        finishPromisePayload(task);
        task.value = value;
        onPromise(task, false, value);
      }, (reason) => {
        finishPromisePayload(task);
        task.value = reason;
        onPromise(task, true, reason);
      });
    }
    return false;
  };
  const encodeDispatch = (task, slotIndex) => {
    const args = task.value;
    if (tryEncodePrimitiveTask(task))
      return true;
    switch (typeof args) {
      case "bigint": {
        const binaryBytes = encodeBigIntIntoScratch(args);
        const binary = bigintScratch.subarray(0, binaryBytes);
        if (binaryBytes <= staticMaxBytes) {
          const written2 = writeStaticBinary(binary, slotIndex);
          if (written2 !== -1) {
            task[TaskIndex.Type] = PayloadBuffer.StaticBigInt;
            task[TaskIndex.PayloadLen] = written2;
            clearBigIntScratch(binaryBytes);
            task.value = null;
            return true;
          }
        }
        task[TaskIndex.Type] = PayloadBuffer.BigInt;
        if (!ensureWithinDynamicLimit(task, binaryBytes, "BigInt")) {
          clearBigIntScratch(binaryBytes);
          return false;
        }
        const reservedSlot = reserveDynamic(task, binaryBytes);
        const written = writeDynamicBinary(binary, task[TaskIndex.Start]);
        if (written < 0) {
          clearBigIntScratch(binaryBytes);
          return failDynamicWriteAfterReserve(task, reservedSlot);
        }
        task[TaskIndex.PayloadLen] = written;
        setSlotLength(reservedSlot, written);
        clearBigIntScratch(binaryBytes);
        task.value = null;
        return true;
      }
      case "function":
        return encoderError({
          task,
          type: ErrorKnitting.Function,
          onPromise
        });
      case "object":
        objectDynamicSlot = -1;
        try {
          const objectValue = args;
          const sharedArrayBufferPayload = getSharedArrayBufferPayload(objectValue);
          if (sharedArrayBufferPayload !== undefined) {
            return encodeObjectExternalPayload(task, slotIndex, sharedArrayBufferPayload, true);
          }
          const objectProto = objectGetPrototypeOf(objectValue);
          if (isRuntimeUint8Array(objectValue)) {
            return encodeObjectUint8Array(task, slotIndex, objectValue);
          }
          if (arrayIsArray(objectValue) && isNumericArray(objectValue)) {
            return encodeObjectNumericArray(task, slotIndex, objectValue);
          }
          if (arrayIsArray(objectValue) || objectProto === objectPrototype || objectProto === null) {
            let text;
            try {
              text = stringifyJSON(objectValue);
            } catch (error) {
              const detail = error instanceof Error ? error.message : String(error);
              return encoderError({
                task,
                type: ErrorKnitting.Json,
                onPromise,
                detail
              });
            }
            if (text.length <= staticMaxBytes) {
              const written2 = writeStaticUtf8(text, slotIndex);
              if (written2 !== -1) {
                task[TaskIndex.Type] = PayloadBuffer.StaticJson;
                task[TaskIndex.PayloadLen] = written2;
                task.value = null;
                return true;
              }
            }
            task[TaskIndex.Type] = PayloadBuffer.Json;
            const reserveBytes = dynamicUtf8ReserveBytes(task, text, "Json");
            if (reserveBytes < 0)
              return false;
            const reservedSlot = reserveDynamicObject(task, reserveBytes);
            const written = writeDynamicUtf8(text, task[TaskIndex.Start], reserveBytes);
            if (written < 0) {
              return failDynamicWriteAfterReserve(task, reservedSlot);
            }
            task[TaskIndex.PayloadLen] = written;
            setSlotLength(reservedSlot, written);
            task.value = null;
            return true;
          }
          if (isBufferReferenceValue(objectValue) || isProcessSharedBufferValue(objectValue)) {
            return encodeObjectExternalPayload(task, slotIndex, objectValue, true);
          }
          const objectCtor = objectValue.constructor;
          if (isRuntimeBuffer(objectValue)) {
            return encodeObjectBuffer(task, slotIndex, objectValue);
          }
          switch (objectCtor) {
            case ArrayBuffer:
              return encodeObjectArrayBuffer(task, slotIndex, objectValue);
            case Int32Array: {
              const int32 = objectValue;
              return encodeObjectBinary(task, slotIndex, new Uint8Array(int32.buffer, int32.byteOffset, int32.byteLength), PayloadBuffer.Int32Array, PayloadBuffer.StaticInt32Array);
            }
            case Float64Array:
              return encodeObjectFloat64Array(task, slotIndex, objectValue);
            case BigInt64Array: {
              const bigInt64 = objectValue;
              return encodeObjectBinary(task, slotIndex, new Uint8Array(bigInt64.buffer, bigInt64.byteOffset, bigInt64.byteLength), PayloadBuffer.BigInt64Array, PayloadBuffer.StaticBigInt64Array);
            }
            case BigUint64Array: {
              const bigUint64 = objectValue;
              return encodeObjectBinary(task, slotIndex, new Uint8Array(bigUint64.buffer, bigUint64.byteOffset, bigUint64.byteLength), PayloadBuffer.BigUint64Array, PayloadBuffer.StaticBigUint64Array);
            }
            case DataView: {
              const dataView = objectValue;
              return encodeObjectBinary(task, slotIndex, new Uint8Array(dataView.buffer, dataView.byteOffset, dataView.byteLength), PayloadBuffer.DataView, PayloadBuffer.StaticDataView);
            }
            case Date:
              return encodeObjectDate(task, objectValue);
            case Envelope:
              return encodeObjectEnvelope(task, slotIndex, objectValue);
            case Promise:
              return encodeObjectPromise(task, objectValue);
            case Error:
              return encodeErrorObject(task, objectValue);
          }
          if (objectValue instanceof Date) {
            return encodeObjectDate(task, objectValue);
          }
          if (objectValue instanceof Envelope) {
            return encodeObjectEnvelope(task, slotIndex, objectValue);
          }
          if (objectValue instanceof Promise) {
            return encodeObjectPromise(task, objectValue);
          }
          if (objectValue instanceof Error) {
            return encodeErrorObject(task, objectValue);
          }
          if (isExternalPayloadLike(objectValue)) {
            return encodeObjectExternalPayload(task, slotIndex, objectValue);
          }
          return encoderError({
            task,
            type: ErrorKnitting.Serializable,
            onPromise,
            detail: UNSUPPORTED_OBJECT_DETAIL
          });
        } catch (error) {
          rollbackObjectDynamic();
          const detail = error instanceof Error ? error.message : String(error);
          return encoderError({
            task,
            type: ErrorKnitting.Serializable,
            onPromise,
            detail
          });
        }
      case "string": {
        const text = args;
        if (text.length <= staticMaxBytes) {
          const written2 = writeStaticUtf8(text, slotIndex);
          if (written2 !== -1) {
            task[TaskIndex.Type] = PayloadBuffer.StaticString;
            task[TaskIndex.PayloadLen] = written2;
            task.value = null;
            return true;
          }
        }
        task[TaskIndex.Type] = PayloadBuffer.String;
        const reserveBytes = dynamicUtf8ReserveBytes(task, text, "String");
        if (reserveBytes < 0)
          return false;
        const reservedSlot = reserveDynamic(task, reserveBytes);
        const written = writeDynamicUtf8(text, task[TaskIndex.Start], reserveBytes);
        if (written < 0) {
          return failDynamicWriteAfterReserve(task, reservedSlot);
        }
        task[TaskIndex.PayloadLen] = written;
        setSlotLength(reservedSlot, written);
        task.value = null;
        return true;
      }
      case "symbol": {
        const key = symbolKeyFor(args);
        if (key === undefined) {
          return encoderError({
            task,
            type: ErrorKnitting.Symbol,
            onPromise
          });
        }
        if (key.length * 3 <= staticMaxBytes) {
          const written2 = writeStaticUtf8(key, slotIndex);
          if (written2 !== -1) {
            task[TaskIndex.Type] = PayloadBuffer.StaticSymbol;
            task[TaskIndex.PayloadLen] = written2;
            task.value = null;
            return true;
          }
        }
        task[TaskIndex.Type] = PayloadBuffer.Symbol;
        const reserveBytes = dynamicUtf8ReserveBytes(task, key, "Symbol");
        if (reserveBytes < 0)
          return false;
        const reservedSlot = reserveDynamic(task, reserveBytes);
        const written = writeDynamicUtf8(key, task[TaskIndex.Start], reserveBytes);
        if (written < 0) {
          return failDynamicWriteAfterReserve(task, reservedSlot);
        }
        task[TaskIndex.PayloadLen] = written;
        setSlotLength(reservedSlot, written);
        task.value = null;
        return true;
      }
    }
    return false;
  };
  return encodeDispatch;
};
var decodePayload = ({
  lockSector,
  payload,
  sab,
  payloadConfig,
  headersBuffer,
  headerSlotStrideU32,
  textCompat,
  host,
  processBoundary = false
}) => {
  const payloadSab = payload?.sab ?? sab;
  const resolvedPayloadConfig = resolvePayloadBufferOptions({
    sab: payloadSab,
    options: payload?.config ?? payloadConfig
  });
  const { free } = register({ lockSector });
  const freeTaskSlot = (task) => free(getTaskSlotIndex(task));
  const {
    readUtf8: readDynamicUtf8,
    readBytesCopy: readDynamicBytesCopy,
    readBytesBufferCopy: readDynamicBufferCopy,
    readBufferCopy: readDynamicBuffer,
    readBytesArrayBufferCopy: readDynamicArrayBufferCopy,
    readArrayBufferCopy: readDynamicArrayBuffer,
    read8BytesFloatCopy: readDynamic8BytesFloatCopy,
    read8BytesFloatView: readDynamic8BytesFloatView
  } = createSharedDynamicBufferIO({
    sab: payloadSab,
    payloadConfig: resolvedPayloadConfig,
    textCompat: textCompat?.payload
  });
  const {
    readUtf8: readStaticUtf8,
    readBytesBufferCopy: readStaticBufferCopy,
    readBufferCopy: readStaticBuffer,
    readUint8ArrayCopy: readStaticUint8ArrayCopy,
    readBytesArrayBufferCopy: readStaticArrayBufferCopy,
    readArrayBufferCopy: readStaticArrayBuffer,
    read8BytesFloatCopy: readStatic8BytesFloatCopy,
    readU32Words: readStaticU32Words
  } = requireStaticIO(headersBuffer, headerSlotStrideU32, textCompat?.headers);
  const processSharedBufferWords = new Uint32Array(PROCESS_SHARED_BUFFER_NUMERIC_WORDS);
  const sharedArrayBufferWords = new Uint32Array(SHARED_ARRAY_BUFFER_NUMERIC_WORDS);
  const bufferReferenceWords = new Uint32Array(BUFFER_REFERENCE_NUMERIC_WORDS);
  return (task, slotIndex, specialFlags) => {
    const payloadType = task[TaskIndex.Type];
    if (processBoundary && (payloadType === PayloadBuffer.SharedArrayBuffer || payloadType === PayloadBuffer.BufferReference)) {
      throw new TypeError(PROCESS_BOUNDARY_POINTER_PAYLOAD_DETAIL);
    }
    switch (payloadType) {
      case PayloadSignal.BigInt:
        Uint32View[0] = task[TaskIndex.Start];
        Uint32View[1] = task[TaskIndex.End];
        task.value = BigInt64View[0];
        return;
      case PayloadSignal.True:
        task.value = true;
        return;
      case PayloadSignal.False:
        task.value = false;
        return;
      case PayloadSignal.Float64:
        Uint32View[0] = task[TaskIndex.Start];
        Uint32View[1] = task[TaskIndex.End];
        task.value = Float64View[0];
        return;
      case PayloadSignal.NaN:
        task.value = NaN;
        return;
      case PayloadSignal.Null:
        task.value = null;
        return;
      case PayloadSignal.Undefined:
        task.value = undefined;
        return;
      case PayloadBuffer.String:
        task.value = readDynamicUtf8(task[TaskIndex.Start], task[TaskIndex.Start] + task[TaskIndex.PayloadLen]);
        freeTaskSlot(task);
        return;
      case PayloadBuffer.StaticString:
        task.value = readStaticUtf8(0, task[TaskIndex.PayloadLen], slotIndex);
        return;
      case PayloadBuffer.Json:
        task.value = parseJSON(readDynamicUtf8(task[TaskIndex.Start], task[TaskIndex.Start] + task[TaskIndex.PayloadLen]));
        freeTaskSlot(task);
        return;
      case PayloadBuffer.StaticJson:
        task.value = parseJSON(readStaticUtf8(0, task[TaskIndex.PayloadLen], slotIndex));
        return;
      case PayloadBuffer.EnvelopeStaticHeader:
      case PayloadBuffer.EnvelopeStaticHeaderString: {
        const rawHeader = readStaticUtf8(0, task[TaskIndex.PayloadLen], slotIndex);
        const header = task[TaskIndex.Type] === PayloadBuffer.EnvelopeStaticHeaderString ? rawHeader : parseJSON(rawHeader);
        const payloadLength = task[TaskIndex.End];
        const payload2 = payloadLength > 0 ? readDynamicArrayBufferCopy(task[TaskIndex.Start], task[TaskIndex.Start] + payloadLength) : new ArrayBuffer(0);
        task.value = new Envelope(header, payload2);
        freeTaskSlot(task);
        return;
      }
      case PayloadBuffer.EnvelopeDynamicHeader:
      case PayloadBuffer.EnvelopeDynamicHeaderString: {
        const headerStart = task[TaskIndex.Start];
        const payloadStart = headerStart + task[TaskIndex.PayloadLen];
        const payloadLength = task[TaskIndex.End];
        const rawHeader = readDynamicUtf8(headerStart, payloadStart);
        const header = task[TaskIndex.Type] === PayloadBuffer.EnvelopeDynamicHeaderString ? rawHeader : parseJSON(rawHeader);
        const payload2 = payloadLength > 0 ? readDynamicArrayBufferCopy(payloadStart, payloadStart + payloadLength) : new ArrayBuffer(0);
        task.value = new Envelope(header, payload2);
        freeTaskSlot(task);
        return;
      }
      case PayloadBuffer.EnvelopeStaticHeaderExternal:
      case PayloadBuffer.EnvelopeStaticHeaderStringExternal: {
        const rawHeader = readStaticUtf8(0, task[TaskIndex.PayloadLen], slotIndex);
        const header = task[TaskIndex.Type] === PayloadBuffer.EnvelopeStaticHeaderStringExternal ? rawHeader : parseJSON(rawHeader);
        const bodyStart = task[TaskIndex.Start];
        const body = decodeExternalPayload(readDynamicUtf8(bodyStart, bodyStart + task[TaskIndex.End]), processBoundary);
        task.value = new Envelope(header, body);
        freeTaskSlot(task);
        return;
      }
      case PayloadBuffer.EnvelopeDynamicHeaderExternal:
      case PayloadBuffer.EnvelopeDynamicHeaderStringExternal: {
        const headerStart = task[TaskIndex.Start];
        const bodyStart = headerStart + task[TaskIndex.PayloadLen];
        const rawHeader = readDynamicUtf8(headerStart, bodyStart);
        const header = task[TaskIndex.Type] === PayloadBuffer.EnvelopeDynamicHeaderStringExternal ? rawHeader : parseJSON(rawHeader);
        const body = decodeExternalPayload(readDynamicUtf8(bodyStart, bodyStart + task[TaskIndex.End]), processBoundary);
        task.value = new Envelope(header, body);
        freeTaskSlot(task);
        return;
      }
      case PayloadBuffer.BigInt:
        task.value = decodeBigIntBinary(readDynamicBufferCopy(task[TaskIndex.Start], task[TaskIndex.Start] + task[TaskIndex.PayloadLen]));
        freeTaskSlot(task);
        return;
      case PayloadBuffer.StaticBigInt:
        task.value = decodeBigIntBinary(readStaticBufferCopy(0, task[TaskIndex.PayloadLen], slotIndex));
        return;
      case PayloadBuffer.Symbol:
        task.value = symbolFor(readDynamicUtf8(task[TaskIndex.Start], task[TaskIndex.Start] + task[TaskIndex.PayloadLen]));
        freeTaskSlot(task);
        return;
      case PayloadBuffer.StaticSymbol:
        task.value = symbolFor(readStaticUtf8(0, task[TaskIndex.PayloadLen], slotIndex));
        return;
      case PayloadBuffer.Int32Array: {
        const bytes = readDynamicBufferCopy(task[TaskIndex.Start], task[TaskIndex.Start] + task[TaskIndex.PayloadLen]);
        task.value = new Int32Array(bytes.buffer, bytes.byteOffset, bytes.byteLength >>> 2);
        freeTaskSlot(task);
        return;
      }
      case PayloadBuffer.StaticInt32Array: {
        const bytes = readStaticBufferCopy(0, task[TaskIndex.PayloadLen], slotIndex);
        task.value = new Int32Array(bytes.buffer, bytes.byteOffset, bytes.byteLength >>> 2);
        return;
      }
      case PayloadBuffer.Float64Array: {
        task.value = readDynamic8BytesFloatCopy(task[TaskIndex.Start], task[TaskIndex.Start] + task[TaskIndex.PayloadLen]);
        freeTaskSlot(task);
        return;
      }
      case PayloadBuffer.StaticFloat64Array:
        task.value = readStatic8BytesFloatCopy(0, task[TaskIndex.PayloadLen], slotIndex);
        return;
      case PayloadBuffer.NumericArray: {
        task.value = numericArrayFromFloat64(readDynamic8BytesFloatView(task[TaskIndex.Start], task[TaskIndex.Start] + task[TaskIndex.PayloadLen]));
        freeTaskSlot(task);
        return;
      }
      case PayloadBuffer.StaticNumericArray:
        task.value = numericArrayFromFloat64(readStatic8BytesFloatCopy(0, task[TaskIndex.PayloadLen], slotIndex));
        return;
      case PayloadBuffer.BigInt64Array: {
        const bytes = readDynamicBufferCopy(task[TaskIndex.Start], task[TaskIndex.Start] + task[TaskIndex.PayloadLen]);
        task.value = new BigInt64Array(bytes.buffer, bytes.byteOffset, bytes.byteLength >>> 3);
        freeTaskSlot(task);
        return;
      }
      case PayloadBuffer.StaticBigInt64Array: {
        const bytes = readStaticBufferCopy(0, task[TaskIndex.PayloadLen], slotIndex);
        task.value = new BigInt64Array(bytes.buffer, bytes.byteOffset, bytes.byteLength >>> 3);
        return;
      }
      case PayloadBuffer.BigUint64Array: {
        const bytes = readDynamicBufferCopy(task[TaskIndex.Start], task[TaskIndex.Start] + task[TaskIndex.PayloadLen]);
        task.value = new BigUint64Array(bytes.buffer, bytes.byteOffset, bytes.byteLength >>> 3);
        freeTaskSlot(task);
        return;
      }
      case PayloadBuffer.StaticBigUint64Array: {
        const bytes = readStaticBufferCopy(0, task[TaskIndex.PayloadLen], slotIndex);
        task.value = new BigUint64Array(bytes.buffer, bytes.byteOffset, bytes.byteLength >>> 3);
        return;
      }
      case PayloadBuffer.DataView: {
        const bytes = readDynamicBufferCopy(task[TaskIndex.Start], task[TaskIndex.Start] + task[TaskIndex.PayloadLen]);
        task.value = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
        freeTaskSlot(task);
        return;
      }
      case PayloadBuffer.StaticDataView: {
        const bytes = readStaticBufferCopy(0, task[TaskIndex.PayloadLen], slotIndex);
        task.value = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
        return;
      }
      case PayloadBuffer.ExternalPayload:
        task.value = decodeExternalPayload(readDynamicUtf8(task[TaskIndex.Start], task[TaskIndex.Start] + task[TaskIndex.PayloadLen]), processBoundary);
        freeTaskSlot(task);
        return;
      case PayloadBuffer.StaticExternalPayload:
        task.value = decodeExternalPayload(readStaticUtf8(0, task[TaskIndex.PayloadLen], slotIndex), processBoundary);
        return;
      case PayloadBuffer.ProcessSharedBuffer:
        task.value = decodeProcessSharedBufferNumericWords(readStaticU32Words(processSharedBufferWords, PROCESS_SHARED_BUFFER_NUMERIC_WORDS, slotIndex));
        return;
      case PayloadBuffer.SharedArrayBuffer:
        task.value = decodeSharedArrayBufferNumericWords(readStaticU32Words(sharedArrayBufferWords, task[TaskIndex.PayloadLen] >>> 2, slotIndex));
        return;
      case PayloadBuffer.BufferReference:
        task.value = decodeBufferReferenceNumericWords(readStaticU32Words(bufferReferenceWords, BUFFER_REFERENCE_NUMERIC_WORDS, slotIndex));
        return;
      case PayloadBuffer.Date:
        Uint32View[0] = task[TaskIndex.Start];
        Uint32View[1] = task[TaskIndex.End];
        task.value = new Date(Float64View[0]);
        return;
      case PayloadBuffer.Error:
        task.value = parseErrorPayload(readDynamicUtf8(task[TaskIndex.Start], task[TaskIndex.Start] + task[TaskIndex.PayloadLen]));
        freeTaskSlot(task);
        return;
      case PayloadBuffer.Binary:
        {
          const buffer = readDynamicBufferCopy(task[TaskIndex.Start], task[TaskIndex.Start] + task[TaskIndex.PayloadLen]);
          task.value = new Uint8Array(buffer.buffer, buffer.byteOffset, buffer.byteLength);
        }
        freeTaskSlot(task);
        return;
      case PayloadBuffer.StaticBinary:
        task.value = readStaticUint8ArrayCopy(0, task[TaskIndex.PayloadLen], slotIndex);
        return;
      case PayloadBuffer.ArrayBuffer:
        task.value = readDynamicArrayBuffer(task[TaskIndex.Start], task[TaskIndex.Start] + task[TaskIndex.PayloadLen]);
        freeTaskSlot(task);
        return;
      case PayloadBuffer.StaticArrayBuffer:
        task.value = readStaticArrayBuffer(0, task[TaskIndex.PayloadLen], slotIndex);
        return;
      case PayloadBuffer.Buffer:
        task.value = readDynamicBuffer(task[TaskIndex.Start], task[TaskIndex.Start] + task[TaskIndex.PayloadLen]);
        freeTaskSlot(task);
        return;
      case PayloadBuffer.StaticBuffer:
        task.value = readStaticBuffer(0, task[TaskIndex.PayloadLen], slotIndex);
        return;
    }
  };
};
registerLockPayloadCodec(encodePayload, decodePayload);

// src/common/task-symbol.ts
var endpointSymbol = Symbol.for("task");

// src/common/module-url.ts
var WINDOWS_DRIVE_PATH = /^[A-Za-z]:[\\/]/;
var WINDOWS_UNC_PATH = /^\\\\[^\\/?]+\\[^\\/?]+/;
var encodeFilePath = (path) => encodeURI(path).replace(/\?/g, "%3F").replace(/#/g, "%23");
var nodePathToFileURL = () => getNodeBuiltinModule("node:url")?.pathToFileURL;
var pathToFileUrlFallback = (specifier) => {
  const absolute = specifier.startsWith("/") ? specifier : `/${specifier}`;
  return `file://${encodeFilePath(absolute)}`;
};
var toModuleUrl = (specifier) => {
  if (WINDOWS_DRIVE_PATH.test(specifier)) {
    const normalized = specifier.replace(/\\/g, "/");
    return `file:///${encodeFilePath(normalized)}`;
  }
  if (WINDOWS_UNC_PATH.test(specifier)) {
    const normalized = specifier.replace(/^\\\\+/, "").replace(/\\/g, "/");
    return `file://${encodeFilePath(normalized)}`;
  }
  try {
    return new URL(specifier).href;
  } catch {
    const pathToFileURL = nodePathToFileURL();
    return pathToFileURL ? pathToFileURL(specifier).href : pathToFileUrlFallback(specifier);
  }
};
var toImportSpecifier = (moduleUrl) => {
  if (!IS_ANDROMEDA || !moduleUrl.startsWith("file://"))
    return moduleUrl;
  const withoutScheme = moduleUrl.slice("file://".length);
  const path = withoutScheme.startsWith("/") ? withoutScheme : `/${withoutScheme}`;
  try {
    return decodeURIComponent(path);
  } catch {
    return path;
  }
};

// src/worker/task-loader.ts
var TimeoutKind = {
  Reject: 0,
  Resolve: 1
};
var normalizeTimeout = (timeout) => {
  if (timeout == null)
    return;
  if (typeof timeout === "number") {
    const ms2 = Math.floor(timeout);
    return ms2 >= 0 ? { ms: ms2, kind: TimeoutKind.Reject, value: new Error("Task timeout") } : undefined;
  }
  const ms = Math.floor(timeout.time);
  if (!(ms >= 0))
    return;
  if ("default" in timeout) {
    return { ms, kind: TimeoutKind.Resolve, value: timeout.default };
  }
  if (timeout.maybe === true) {
    return { ms, kind: TimeoutKind.Resolve, value: undefined };
  }
  if ("error" in timeout) {
    return { ms, kind: TimeoutKind.Reject, value: timeout.error };
  }
  return { ms, kind: TimeoutKind.Reject, value: new Error("Task timeout") };
};
var composeWorkerCallable = (fixed, _permission) => {
  return fixed.f;
};
var getFunctions = async ({ list, ids, names, at, permission }) => {
  const modules = list.map((specifier) => toModuleUrl(specifier));
  const nameSet = new Set(names);
  const results = await Promise.all(modules.map(async (imports) => {
    const module = await import(toImportSpecifier(imports));
    const fixedTasks = Object.entries(module).filter(([_, value]) => value != null && typeof value === "object" && value?.[endpointSymbol] === true).map(([name, value]) => ({
      ...value,
      name
    }));
    const functionTasks = Object.entries(module).filter(([name, value]) => nameSet.has(name) && typeof value === "function").map(([name, value]) => ({
      f: value,
      id: -1,
      importedFrom: imports,
      at: -1,
      name,
      [endpointSymbol]: true
    }));
    return [...fixedTasks, ...functionTasks];
  }));
  const flattened = results.flat();
  const useAtFilter = modules.length === 1 && at.length > 0;
  const atSet = useAtFilter ? new Set(at) : null;
  const targetModule = useAtFilter ? modules[0] : null;
  const flattenedResults = flattened.filter((obj) => useAtFilter ? obj.importedFrom === targetModule && atSet.has(obj.at) : ids.includes(obj.id)).sort((a, b) => a.name.localeCompare(b.name));
  return flattenedResults.map((fixed) => ({
    ...fixed,
    run: composeWorkerCallable(fixed, permission),
    timeout: normalizeTimeout(fixed.timeout)
  }));
};

// src/worker/timers.ts
var Comment = {
  thisIsAHint: 0
};
var maybeGc = (() => {
  const host = globalThis;
  const gc = typeof host.gc === "function" ? () => host.gc() : undefined;
  if (gc) {
    try {
      delete host.gc;
    } catch {
      host.gc = undefined;
    }
    if (host.global) {
      try {
        delete host.global.gc;
      } catch {
        host.global.gc = undefined;
      }
    }
  }
  return gc ?? (() => {});
})();
var DEFAULT_PAUSE_TIME = 250;
var a_load = Atomics.load;
var a_store2 = Atomics.store;
var a_wait = typeof Atomics.wait === "function" ? Atomics.wait : undefined;
var p_now2 = performance.now.bind(performance);
var waitFallbackView = a_wait === undefined || typeof SharedArrayBuffer !== "function" ? undefined : new Int32Array(new SharedArrayBuffer(Int32Array.BYTES_PER_ELEMENT));
var a_pause = "pause" in Atomics ? Atomics.pause : undefined;
var runtimeGlobals = globalThis;
var isPlainNodeWindows = runtimeGlobals.process?.platform === "win32" && typeof runtimeGlobals.process?.versions?.node === "string" && runtimeGlobals.process?.versions?.bun === undefined && runtimeGlobals.Deno === undefined;
var nativeWaitTimeoutMs = (parkMs) => isPlainNodeWindows ? 1 : Number.isFinite(parkMs) ? parkMs : Infinity;
var pollingWaitTimeoutMs = (parkMs) => Number.isFinite(parkMs) ? Math.min(Math.max(parkMs, 0), 1) : 1;
var whilePausing = ({ pauseInNanoseconds }) => {
  const forNanoseconds = pauseInNanoseconds ?? DEFAULT_PAUSE_TIME;
  if (!a_pause || forNanoseconds <= 0)
    return () => {};
  return () => a_pause(forNanoseconds);
};
var pauseGeneric = whilePausing({});
var sleepUntilChanged = ({
  at,
  opView,
  pauseInNanoseconds,
  rxStatus,
  txStatus,
  enqueueLock,
  write,
  nativeWaitU32,
  useSharedMemoryWait = true,
  flushBeforeClaim = false
}) => {
  const pause = pauseInNanoseconds === undefined ? pauseGeneric : whilePausing({ pauseInNanoseconds });
  const flushWrite = () => {
    if (!write)
      return false;
    const wrote = write();
    if (typeof wrote === "number")
      return wrote > 0;
    return wrote === true;
  };
  const tryProgress = flushBeforeClaim ? () => {
    const wrote = flushWrite();
    return enqueueLock() || wrote;
  } : () => {
    const claimed = enqueueLock();
    return flushWrite() || claimed;
  };
  return (value, spinMicroseconds, parkMs) => {
    const until = p_now2() + spinMicroseconds / 1000;
    maybeGc();
    let spinChecks = 0;
    while (true) {
      if (a_load(opView, at) !== value || txStatus[Comment.thisIsAHint] === 1)
        return;
      if (tryProgress())
        return;
      pause();
      if ((spinChecks++ & 63) === 0 && p_now2() >= until)
        break;
    }
    if (tryProgress())
      return;
    a_store2(rxStatus, 0, 0);
    if (nativeWaitU32 !== undefined) {
      nativeWaitU32(opView.buffer, opView.byteOffset + at * Int32Array.BYTES_PER_ELEMENT, value >>> 0, nativeWaitTimeoutMs(parkMs));
    } else if (useSharedMemoryWait && a_wait && opView.buffer instanceof SharedArrayBuffer) {
      a_wait(opView, at, value, parkMs ?? Infinity);
    } else if (a_wait && waitFallbackView) {
      a_wait(waitFallbackView, 0, 0, pollingWaitTimeoutMs(parkMs));
    }
    a_store2(rxStatus, 0, 1);
  };
};

// src/worker/safety/process.ts
var toErrorMessage = (error) => error instanceof Error ? error.message : String(error);
var failProcessGuardInstall = (target, reason, cause) => {
  const suffix = cause === undefined ? "" : `: ${toErrorMessage(cause)}`;
  throw new Error(`KNT_ERROR_PROCESS_GUARD_INSTALL: ${target} ${reason}${suffix}`);
};
var installTerminationGuard = () => {
  const proc = getNodeProcess();
  if (!proc)
    return;
  if (proc.__knittingTerminationGuard === true)
    return;
  const blocked = (name) => {
    throw new Error(`KNT_ERROR_PROCESS_GUARD: ${name} is disabled in worker tasks`);
  };
  const guardMethod = (name) => {
    try {
      Object.defineProperty(proc, name, {
        configurable: false,
        writable: false,
        value: (..._args) => blocked(`process.${name}`)
      });
    } catch (defineError) {
      try {
        proc[name] = (..._args) => blocked(`process.${name}`);
      } catch (assignError) {
        failProcessGuardInstall(`process.${name}`, "install failed", [
          toErrorMessage(defineError),
          toErrorMessage(assignError)
        ].join("; "));
      }
    }
    if (typeof proc[name] !== "function") {
      failProcessGuardInstall(`process.${name}`, "install verification failed");
    }
  };
  guardMethod("exit");
  guardMethod("kill");
  guardMethod("abort");
  guardMethod("reallyExit");
  const globalScope = globalThis;
  if (globalScope.Deno && typeof globalScope.Deno.exit === "function") {
    try {
      Object.defineProperty(globalScope.Deno, "exit", {
        configurable: false,
        writable: false,
        value: (_code) => blocked("Deno.exit")
      });
    } catch (defineError) {
      try {
        globalScope.Deno.exit = (_code) => blocked("Deno.exit");
      } catch (assignError) {
        failProcessGuardInstall("Deno.exit", "install failed", [
          toErrorMessage(defineError),
          toErrorMessage(assignError)
        ].join("; "));
      }
    }
    if (typeof globalScope.Deno.exit !== "function") {
      failProcessGuardInstall("Deno.exit", "install verification failed");
    }
  }
  proc.__knittingTerminationGuard = true;
};
var installUnhandledRejectionSilencer = () => {
  const proc = getNodeProcess();
  if (!proc || typeof proc.on !== "function") {
    return;
  }
  if (proc.__knittingUnhandledRejectionSilencer === true)
    return;
  proc.__knittingUnhandledRejectionSilencer = true;
  proc.on("unhandledRejection", () => {});
};
// src/worker/safety/performance.ts
var installPerformanceNowGuard = () => {
  const g = globalThis;
  if (g.__knittingPerformanceNowGuardInstalled === true)
    return;
  g.__knittingPerformanceNowGuardInstalled = true;
  const perf = globalThis.performance;
  if (!perf || typeof perf.now !== "function")
    return;
  try {
    perf.now();
  } catch {}
};
// src/worker/safety/worker-data.ts
var scrubWorkerDataSensitiveBuffers = (value) => {
  const data = value;
  try {
    data.sab = undefined;
    data.lock = undefined;
    data.returnLock = undefined;
    data.permission = undefined;
  } catch {}
  try {
    delete data.sab;
  } catch {}
  try {
    delete data.lock;
  } catch {}
  try {
    delete data.returnLock;
  } catch {}
  try {
    delete data.permission;
  } catch {}
  try {
    Object.freeze(data);
  } catch {}
};
// src/worker/safety/startup.ts
var hasLockBuffers = (value) => isSharedBufferSource(value?.headers) && isSharedBufferSource(value?.lockSector) && isSharedBufferSource(value?.payload) && isSharedBufferSource(value?.payloadSector) && (value?.textCompat === undefined || isLockBufferTextCompat(value.textCompat));
var assertWorkerSharedMemoryBootData = ({ sab, lock, returnLock }) => {
  if (!isSharedBufferSource(sab)) {
    throw new Error("worker missing transport SAB");
  }
  if (!hasLockBuffers(lock)) {
    throw new Error("worker missing lock SABs");
  }
  if (!hasLockBuffers(returnLock)) {
    throw new Error("worker missing return lock SABs");
  }
};
var assertWorkerImportsResolved = ({ list, ids, names, listOfFunctions }) => {
  if (listOfFunctions.length > 0 && (names === undefined || listOfFunctions.length === names.length))
    return;
  console.log(list);
  console.log(ids);
  if (names !== undefined)
    console.log(names);
  console.log(listOfFunctions);
  throw new Error("No imports were found.");
};
// src/shared/abortSignal.ts
var SLOT_BITS = 32;
var SLOT_MASK = SLOT_BITS - 1;
var AbortSignalPoolExhausted = Symbol.for("knitting.abortSignal.poolExhausted");
var EnqueuedAbortSignal = Symbol.for("knitting.abortSignal.enqueuedSignal");
var signalAbortFactory = ({
  sab,
  maxSignals
}) => {
  const sabRegion = toSharedBufferRegion(sab);
  const atomicView = new Uint32Array(sabRegion.sab, sabRegion.byteOffset, sabRegion.byteLength / Uint32Array.BYTES_PER_ELEMENT);
  const size = atomicView.length;
  const inUse = new Uint32Array(size);
  const physicalMax = size * SLOT_BITS;
  const max = (() => {
    if (!Number.isFinite(maxSignals))
      return physicalMax;
    const parsed = Math.floor(maxSignals);
    if (parsed <= 0)
      return physicalMax;
    return Math.min(parsed, physicalMax);
  })();
  const closeNow = max + 1;
  let current = 0;
  let cursor = 0;
  const getSignal = () => {
    if (current >= max)
      return closeNow;
    for (let step = 0;step < size; step++) {
      const word = (cursor + step) % size;
      const wordBase = word << 5;
      const remaining = max - wordBase;
      if (remaining <= 0)
        continue;
      const allowedMask = remaining >= SLOT_BITS ? 4294967295 : (1 << remaining) - 1 >>> 0;
      const freeBits = (~inUse[word] & allowedMask) >>> 0;
      if (freeBits === 0)
        continue;
      const bit = (freeBits & -freeBits) >>> 0;
      inUse[word] = (inUse[word] | bit) >>> 0;
      current = current + 1 | 0;
      cursor = (word + 1) % size;
      Atomics.and(atomicView, word, ~bit);
      const bitIndex = 31 - Math.clz32(bit);
      return (word << 5) + bitIndex;
    }
    return closeNow;
  };
  const setSignal = (signal) => {
    if (signal === closeNow)
      return 0;
    if (!Number.isInteger(signal))
      return -1;
    if (signal < 0 || signal >= max)
      return -1;
    const word = signal >>> 5;
    const bit = 1 << (signal & SLOT_MASK);
    Atomics.or(atomicView, word, bit);
    return 1;
  };
  const abortAll = () => {
    for (let word = 0;word < size; word++) {
      Atomics.store(atomicView, word, inUse[word]);
    }
    return current;
  };
  const hasAborted = (signal) => {
    if (signal === closeNow)
      return true;
    if (!Number.isInteger(signal))
      return false;
    if (signal < 0 || signal >= max)
      return false;
    const word = signal >>> 5;
    const bit = 1 << (signal & SLOT_MASK);
    return (Atomics.load(atomicView, word) & bit) !== 0;
  };
  const resetSignal = (signal) => {
    if (signal === closeNow)
      return false;
    if (!Number.isInteger(signal))
      return false;
    if (signal < 0 || signal >= max)
      return false;
    const word = signal >>> 5;
    const bit = 1 << (signal & SLOT_MASK);
    const used = (inUse[word] & bit) !== 0;
    if (!used)
      return false;
    inUse[word] = (inUse[word] & ~bit) >>> 0;
    if (current > 0)
      current = current - 1 | 0;
    cursor = word;
    Atomics.and(atomicView, word, ~bit);
    return true;
  };
  return {
    max,
    closeNow,
    getSignal,
    setSignal,
    abortAll,
    hasAborted,
    resetSignal,
    inUseCount: () => current
  };
};

class OneShotDeferred {
  #triggered = false;
  constructor(deferred, onSettle, onEmptyReject) {
    const settleOnce = (fn) => (...args) => {
      if (this.#triggered)
        return;
      this.#triggered = true;
      onSettle();
      fn(...args);
    };
    deferred.resolve = settleOnce(deferred.resolve);
    deferred.reject = settleOnce(deferred.reject);
    deferred.promise.reject = (reason) => {
      if (this.#triggered)
        return;
      if (reason === undefined && onEmptyReject !== undefined) {
        onEmptyReject();
        return;
      }
      deferred.reject(reason);
    };
  }
}

// src/worker/bootstrap.ts
var DEFAULT_BOOTSTRAP_EXPORT_NAME = "default";
var isWorkerBootstrapOptions = (value) => {
  if (!value || typeof value !== "object")
    return false;
  const candidate = value;
  return typeof candidate.href === "string" && candidate.href.length > 0 && (candidate.name === undefined || typeof candidate.name === "string" && candidate.name.length > 0);
};
var isProcessSharedBufferMetadata = (value) => {
  try {
    ProcessSharedBuffer.fromMetadata(value);
    return true;
  } catch {
    return false;
  }
};
var reviveWorkerBootstrapValue = (value, seen = new WeakMap) => {
  if (isProcessSharedBufferMetadata(value)) {
    return ProcessSharedBuffer.fromMetadata(value);
  }
  if (value === null || typeof value !== "object")
    return value;
  const existing = seen.get(value);
  if (existing !== undefined)
    return existing;
  if (Array.isArray(value)) {
    const out2 = [];
    seen.set(value, out2);
    for (const item of value) {
      out2.push(reviveWorkerBootstrapValue(item, seen));
    }
    return out2;
  }
  const prototype = Object.getPrototypeOf(value);
  if (prototype !== Object.prototype && prototype !== null)
    return value;
  const out = {};
  seen.set(value, out);
  for (const [key, item] of Object.entries(value)) {
    out[key] = reviveWorkerBootstrapValue(item, seen);
  }
  return out;
};
var runWorkerBootstrap = async ({
  bootstrap,
  thread,
  totalNumberOfThread
}) => {
  if (bootstrap === undefined)
    return;
  if (!isWorkerBootstrapOptions(bootstrap)) {
    throw new TypeError("worker.bootstrap must include a non-empty href");
  }
  const module = await import(toModuleUrl(bootstrap.href));
  const name = bootstrap.name ?? DEFAULT_BOOTSTRAP_EXPORT_NAME;
  const selected = module[name];
  if (typeof selected !== "function") {
    const available = Object.keys(module).join(", ");
    throw new TypeError(`worker.bootstrap expected export "${name}" from "${bootstrap.href}" to be a function. Available exports: ${available || "(none)"}`);
  }
  const context = Object.freeze({
    thread,
    totalNumberOfThread,
    runtime: RUNTIME
  });
  await selected(reviveWorkerBootstrapValue(bootstrap.data), context);
};

// scripts/browser-stubs/process-worker-bootstrap.ts
var getProcessWorkerNativeWaitU32 = () => {
  return;
};
var installProcessWorkerBootstrap = () => {};

// src/debug/gate.ts
var readEnv = (key) => {
  const denoEnv = globalThis.Deno?.env;
  if (typeof denoEnv?.get === "function") {
    try {
      return denoEnv.get(key);
    } catch {}
  }
  try {
    return getNodeProcess()?.env?.[key];
  } catch {
    return;
  }
};
var raw = readEnv("KNITTING_DEBUG");
var DEBUG_NAMESPACES = new Set((raw ?? "").split(",").map((part) => part.trim()).filter((part) => part.length > 0));
var DEBUG_ENABLED = DEBUG_NAMESPACES.size > 0;
var resolveDebugNamespaces = (debug) => {
  const namespaces = new Set(DEBUG_NAMESPACES);
  if (debug === true) {
    namespaces.add("*");
  } else if (debug !== undefined && debug !== false) {
    for (const [key, value] of Object.entries(debug)) {
      if (value === true)
        namespaces.add(key);
    }
  }
  return namespaces;
};

// src/worker/loop.ts
var WORKER_FATAL_MESSAGE_KEY = "__knittingWorkerFatal";
var reportWorkerStartupFatal = (error) => {
  const message = String(error?.message ?? error);
  const payload = {
    [WORKER_FATAL_MESSAGE_KEY]: message
  };
  let reported = false;
  try {
    RUNTIME_PARENT_PORT?.postMessage?.(payload);
    reported = RUNTIME_PARENT_PORT !== undefined;
  } catch {}
  if (!reported) {
    try {
      globalThis.postMessage(payload);
      reported = true;
    } catch {}
  }
  if (!reported) {
    try {
      console.error(`Worker startup failed: ${message}`);
    } catch {}
    if (RUNTIME_IS_PROCESS_WORKER) {
      try {
        getNodeProcess()?.exit?.(1);
      } catch {}
    }
  }
};
var installBufferReferenceReleaseListener = (releaseReturnedBufferReference) => {
  const handleMessage = (message) => {
    const token = readBufferReferenceReturnReleaseMessage(message);
    if (token !== undefined)
      releaseReturnedBufferReference(token);
  };
  if (RUNTIME_PARENT_PORT !== undefined) {
    addRuntimeDataListener(RUNTIME_PARENT_PORT, handleMessage);
    return;
  }
  const scope = globalThis;
  scope.addEventListener?.("message", (event) => {
    handleMessage(event?.data);
  });
};
var workerMainLoop = async (startupData) => {
  installTerminationGuard();
  installUnhandledRejectionSilencer();
  installPerformanceNowGuard();
  const {
    debug,
    sab,
    thread,
    startAt,
    workerOptions,
    lock,
    returnLock,
    abortSignalSAB,
    abortSignalMax,
    payloadConfig,
    bufferReferenceReturn,
    permission,
    notifyOnHostPublish,
    totalNumberOfThread,
    list,
    ids,
    names,
    at,
    steal
  } = startupData;
  scrubWorkerDataSensitiveBuffers(startupData);
  assertWorkerSharedMemoryBootData({ sab, lock, returnLock });
  const debugNamespaces = resolveDebugNamespaces(debug);
  const dbg = debugNamespaces.size > 0 ? await Promise.resolve().then(() => (init_handle(), exports_handle)).then((module) => module.initDebug({
    name: `w${thread}`,
    runtime: RUNTIME,
    namespaces: debugNamespaces
  })) : undefined;
  const Comment2 = {
    thisIsAHint: 0
  };
  const signals = createSharedMemoryTransport({
    sabObject: {
      sharedSab: sab
    },
    isMain: false,
    thread,
    startTime: startAt
  });
  const lockState = lock2({
    headers: lock.headers,
    headerSlotStrideU32: lock.headerSlotStrideU32,
    LockBoundSector: lock.lockSector,
    payload: lock.payload,
    payloadSector: lock.payloadSector,
    payloadConfig,
    textCompat: lock.textCompat,
    processBoundary: RUNTIME_IS_PROCESS_WORKER,
    consumers: steal?.consumers,
    consumerId: steal?.consumerId,
    regionLanes: steal?.regionLanes
  });
  const returnLockState = lock2({
    headers: returnLock.headers,
    headerSlotStrideU32: returnLock.headerSlotStrideU32,
    LockBoundSector: returnLock.lockSector,
    payload: returnLock.payload,
    payloadSector: returnLock.payloadSector,
    payloadConfig,
    textCompat: returnLock.textCompat,
    processBoundary: RUNTIME_IS_PROCESS_WORKER,
    notifyOnHostPublish
  });
  const timers = workerOptions?.timers;
  const spinMicroseconds = timers?.spinMicroseconds ?? Math.max(1, totalNumberOfThread) * 50;
  const parkMs = dbg !== undefined ? Number.POSITIVE_INFINITY : timers?.parkMs ?? Math.max(1, totalNumberOfThread) * 50;
  const pauseSpin = (() => {
    const fn = typeof timers?.pauseNanoseconds === "number" ? whilePausing({ pauseInNanoseconds: timers.pauseNanoseconds }) : pauseGeneric;
    return () => fn();
  })();
  const { opView, rxStatus, txStatus } = signals;
  const a_store3 = Atomics.store;
  const a_load2 = Atomics.load;
  const nativeWaitU32 = getProcessWorkerNativeWaitU32();
  await runWorkerBootstrap({
    bootstrap: workerOptions?.bootstrap,
    thread,
    totalNumberOfThread
  });
  dbg?.envPhase("bootstrap");
  const listOfFunctions = await getFunctions({
    list,
    isWorker: true,
    ids,
    names,
    at,
    permission
  });
  dbg?.envPhase("tasks");
  dbg?.log("imports", `${listOfFunctions.length} task(s) from ${list.map((spec) => spec.split(/[\\/]/).pop() || spec).join(", ")}`);
  assertWorkerImportsResolved({ list, ids, names, listOfFunctions });
  const abortSignals = abortSignalSAB ? signalAbortFactory({
    sab: abortSignalSAB,
    maxSignals: abortSignalMax
  }) : undefined;
  const {
    enqueueLock,
    serviceBatchImmediate,
    hasCompleted,
    writeBatch,
    hasPending,
    getAwaiting,
    drainReturnReleases,
    releaseReturnedBufferReference
  } = createWorkerRxQueue({
    listOfFunctions,
    workerOptions,
    lock: lockState,
    returnLock: returnLockState,
    borrowReturnedBufferReferences: bufferReferenceReturn === "borrow",
    hasAborted: abortSignals?.hasAborted,
    stealing: steal !== undefined
  });
  installBufferReferenceReleaseListener(releaseReturnedBufferReference);
  a_store3(rxStatus, 0, 1);
  const WRITE_MAX = 64;
  const pauseUntil = sleepUntilChanged({
    opView,
    at: 0,
    rxStatus,
    txStatus,
    pauseInNanoseconds: timers?.pauseNanoseconds,
    enqueueLock,
    write: () => hasCompleted() ? writeBatch(WRITE_MAX) : 0,
    flushBeforeClaim: steal !== undefined,
    nativeWaitU32,
    useSharedMemoryWait: !(RUNTIME_IS_PROCESS_WORKER && RUNTIME === "node" && nativeWaitU32 === undefined)
  });
  const channel = createRuntimeMessageChannel();
  const port1 = channel.port1;
  const port2 = channel.port2;
  const post2 = (message) => port2.postMessage(message);
  let isInMacro = false;
  let awaitingSpins = 0;
  let lastAwaiting = 0;
  const MAX_AWAITING_MS = 10;
  let wakeToken = a_load2(opView, 0);
  const scheduleMacro = () => {
    if (isInMacro)
      return;
    isInMacro = true;
    post2(null);
  };
  const scheduleTimer = (delayMs) => {
    if (isInMacro)
      return;
    isInMacro = true;
    if (delayMs <= 0 && typeof SET_IMMEDIATE === "function") {
      SET_IMMEDIATE(loop);
      return;
    }
    if (delayMs <= 0) {
      post2(null);
      return;
    }
    if (typeof setTimeout === "function") {
      setTimeout(loop, delayMs);
      return;
    }
    post2(null);
  };
  const traceSignals = dbg?.enabled("signals") === true;
  const _hasCompleted = hasCompleted;
  const _hasPending = hasPending;
  const _getAwaiting = getAwaiting;
  const _drainReturnReleases = drainReturnReleases;
  const _pauseSpin = pauseSpin;
  const _enqueueLock = traceSignals ? () => {
    const progressed = enqueueLock();
    if (progressed) {
      dbg.log("signals", "work from=host");
    }
    return progressed;
  } : enqueueLock;
  const _writeBatch = traceSignals ? (max) => {
    const wrote = writeBatch(max);
    if (wrote > 0)
      dbg.log("signals", `result count=${wrote}`);
    return wrote;
  } : writeBatch;
  const _serviceBatchImmediate = traceSignals ? () => {
    const ran = serviceBatchImmediate();
    if (ran > 0)
      dbg.log("signals", `run count=${ran}`);
    return ran;
  } : serviceBatchImmediate;
  const _pauseUntil = traceSignals ? (value, spinMicroseconds2, parkMs2) => {
    dbg.log("signals", `idle token=${value}`);
    pauseUntil(value, spinMicroseconds2, parkMs2);
  } : pauseUntil;
  const flushBeforeClaim = steal !== undefined;
  const loop = () => {
    isInMacro = false;
    let progressed = true;
    let awaiting = 0;
    while (true) {
      if (flushBeforeClaim) {
        progressed = false;
        if (_hasCompleted()) {
          if (_writeBatch(WRITE_MAX) > 0)
            progressed = true;
        }
        progressed = _enqueueLock() || progressed;
      } else {
        progressed = _enqueueLock();
        if (_hasCompleted()) {
          if (_writeBatch(WRITE_MAX) > 0)
            progressed = true;
        }
      }
      _drainReturnReleases();
      if (_hasPending()) {
        if (_serviceBatchImmediate() > 0)
          progressed = true;
      }
      if ((awaiting = _getAwaiting()) > 0) {
        if (awaiting !== lastAwaiting)
          awaitingSpins = 0;
        lastAwaiting = awaiting;
        awaitingSpins++;
        const delay = Math.min(MAX_AWAITING_MS, Math.max(0, awaitingSpins - 1));
        scheduleTimer(delay);
        return;
      }
      awaitingSpins = lastAwaiting = 0;
      if (!progressed) {
        if (txStatus[Comment2.thisIsAHint] === 1) {
          _pauseSpin();
          continue;
        }
        _pauseUntil(wakeToken, spinMicroseconds, parkMs);
        wakeToken = a_load2(opView, 0);
      }
    }
  };
  const port1Any = port1;
  if (typeof port1Any.on === "function") {
    port1Any.on("message", loop);
  } else {
    port1Any.onmessage = loop;
  }
  port1Any.start?.();
  port2.start?.();
  dbg?.log("lifecycle", `ready: ${listOfFunctions.length} task(s) on thread ${thread}/${totalNumberOfThread}, entering dispatch loop`);
  scheduleMacro();
};
var isWorkerGlobalScope2 = () => {
  const scopeCtor = globalThis.WorkerGlobalScope;
  if (typeof scopeCtor === "function") {
    try {
      if (globalThis instanceof scopeCtor) {
        return true;
      }
    } catch {}
  }
  if (IS_ANDROMEDA && typeof globalThis.self !== "undefined") {
    return true;
  }
  return false;
};
var isLockBuffers = (value) => {
  if (!value || typeof value !== "object")
    return false;
  const candidate = value;
  return isSharedBufferSource(candidate.headers) && isSharedBufferSource(candidate.lockSector) && isSharedBufferSource(candidate.payload) && isSharedBufferSource(candidate.payloadSector) && (candidate.textCompat === undefined || isLockBufferTextCompat(candidate.textCompat));
};
var isWorkerBootPayload = (value) => {
  if (!value || typeof value !== "object")
    return false;
  const candidate = value;
  return isSharedBufferSource(candidate.sab) && Array.isArray(candidate.list) && Array.isArray(candidate.ids) && Array.isArray(candidate.names) && Array.isArray(candidate.at) && typeof candidate.thread === "number" && typeof candidate.totalNumberOfThread === "number" && typeof candidate.startAt === "number" && (candidate.abortSignalSAB === undefined || isSharedBufferSource(candidate.abortSignalSAB)) && isLockBuffers(candidate.lock) && isLockBuffers(candidate.returnLock);
};
var installWorkerGlobalBootstrap = () => {
  const g = globalThis;
  const start = (data) => {
    if (!isWorkerBootPayload(data))
      return;
    workerMainLoop(data).catch(reportWorkerStartupFatal);
  };
  if (typeof g.addEventListener === "function" && typeof g.removeEventListener === "function") {
    const onMessage = (event) => {
      const data = event?.data;
      if (!isWorkerBootPayload(data))
        return;
      try {
        g.removeEventListener?.("message", onMessage);
      } catch {}
      start(data);
    };
    g.addEventListener("message", onMessage);
    return;
  }
  g.onmessage = (event) => {
    const data = event?.data;
    if (!isWorkerBootPayload(data))
      return;
    g.onmessage = null;
    start(data);
  };
};
if (RUNTIME_IS_MAIN_THREAD === false && isWorkerBootPayload(RUNTIME_WORKER_DATA)) {
  workerMainLoop(RUNTIME_WORKER_DATA).catch(reportWorkerStartupFatal);
} else if (RUNTIME_IS_PROCESS_WORKER) {
  installProcessWorkerBootstrap({
    isWorkerBootPayload,
    reportWorkerStartupFatal,
    startWorker: (data) => {
      workerMainLoop(data).catch(reportWorkerStartupFatal);
    }
  });
} else if (isWorkerGlobalScope2()) {
  installWorkerGlobalBootstrap();
}

// src/common/task-source.ts
var genTaskID = ((counter) => () => counter++)(0);
var stableTaskID = (href, at) => {
  let hash = 2166136261;
  for (let index = 0;index < href.length; index++) {
    hash = Math.imul(hash ^ href.charCodeAt(index), 16777619);
  }
  return Math.imul(hash ^ at, 16777619) >>> 0;
};
var INTERNAL_CALLER_HINTS = [
  "/src/common/task-source.ts",
  "/src/common/task-source.js",
  "\\src\\common\\task-source.ts",
  "\\src\\common\\task-source.js",
  "/src/api.ts",
  "/src/api.js",
  "\\src\\api.ts",
  "\\src\\api.js"
];
var INTERNAL_CALLER_FUNCTIONS = new Set([
  "collectStackFrames",
  "resolveCallerHref",
  "getCallerFilePath",
  "buildTaskDefinition",
  "buildTaskDefinitionFromCaller",
  "task",
  "importTask"
]);
var isDefined = (value) => value !== undefined;
var isInternalCallerFrame = (file) => INTERNAL_CALLER_HINTS.some((hint) => file.includes(hint));
var isRuntimeInternalFrame = (file) => file.startsWith("node:") || file.startsWith("native:") || file.startsWith("bun:") || file.startsWith("internal/");
var isInternalCallerFunction = (functionName, methodName) => functionName !== undefined && INTERNAL_CALLER_FUNCTIONS.has(functionName) || methodName !== undefined && INTERNAL_CALLER_FUNCTIONS.has(methodName);
var collectStackFrames = () => {
  const ErrorCtor = Error;
  const original = ErrorCtor.prepareStackTrace;
  try {
    ErrorCtor.prepareStackTrace = (_error, stack2) => stack2;
    const stack = new Error().stack;
    if (!Array.isArray(stack))
      return [];
    const frames = stack.map((site) => {
      try {
        const file = site?.getFileName?.();
        if (typeof file !== "string" || file.length === 0)
          return;
        return {
          file,
          functionName: site?.getFunctionName?.() ?? undefined,
          methodName: site?.getMethodName?.() ?? undefined
        };
      } catch {
        return;
      }
    }).filter(isDefined);
    return frames;
  } finally {
    ErrorCtor.prepareStackTrace = original;
  }
};
var isInternalFrame = (frame) => isRuntimeInternalFrame(frame.file) || isInternalCallerFrame(frame.file) || isInternalCallerFunction(frame.functionName, frame.methodName);
var moduleUrlOverride;
var setModuleUrl = (url) => {
  moduleUrlOverride = typeof url === "string" && url.length > 0 ? toModuleUrl(url) : undefined;
};
var resolveCallerHref = (offset) => {
  if (moduleUrlOverride !== undefined)
    return moduleUrlOverride;
  const frames = collectStackFrames();
  const direct = frames[offset];
  const caller = (direct && !isInternalFrame(direct) ? direct.file : undefined) ?? frames.find((frame) => !isInternalFrame(frame))?.file ?? frames.find((frame) => !isRuntimeInternalFrame(frame.file))?.file;
  if (!caller) {
    throw new Error("Unable to determine caller file. This runtime exposes no stack traces " + "(e.g. Andromeda); call setModuleUrl(import.meta.url) at the top of " + "the module that defines your tasks before creating a pool.");
  }
  return toModuleUrl(caller);
};
var linkingMap = new Map;
var getCallerHref = (offset = 3) => resolveCallerHref(offset);
var getCallerFilePath = (offset = 3) => {
  const href = resolveCallerHref(offset);
  const at = linkingMap.get(href) ?? 0;
  linkingMap.set(href, at + 1);
  return [href, at];
};

// src/common/with-resolvers.ts
var attachReject = (promise, reject) => {
  const deferredPromise = promise;
  deferredPromise.reject = reject;
  return deferredPromise;
};
var withResolvers = () => {
  const native = Promise.withResolvers;
  if (typeof native === "function") {
    const deferred = native.call(Promise);
    return {
      promise: attachReject(deferred.promise, deferred.reject),
      resolve: deferred.resolve,
      reject: deferred.reject
    };
  }
  let resolve;
  let reject;
  const promise = attachReject(new Promise((res, rej) => {
    resolve = res;
    reject = rej;
  }), reject);
  return { promise, resolve, reject };
};

// src/runtime/tx-queue.ts
var SLOT_INDEX_MASK = 31;
var SLOT_META_MASK = 134217727;
var SLOT_META_SHIFT = 5;
var FUNCTION_ID_MASK = 65535;
var FUNCTION_META_MASK = 65535;
var FUNCTION_META_SHIFT = 16;
var ABORT_SIGNAL_META_OFFSET2 = 1;
var p_now3 = performance.now.bind(performance);
function createHostTxQueue({
  max,
  lock,
  returnLock,
  extraReturnLocks,
  releaseBufferReferenceReturn,
  abortSignals,
  now
}) {
  const PLACE_HOLDER = (_) => {
    throw "UNREACHABLE FROM PLACE HOLDER (main)";
  };
  const newSlot = (id) => {
    const task = makeTask();
    task[TaskIndex.ID] = id;
    task[TaskIndex.FunctionID] = 0;
    task.value = null;
    task.resolve = PLACE_HOLDER;
    task.reject = PLACE_HOLDER;
    return task;
  };
  const initialSize = max ?? 10;
  const queue = Array.from({ length: initialSize }, (_, index) => newSlot(index));
  const freeSockets = Array.from({ length: initialSize }, (_, i) => i);
  const freePush = (id) => freeSockets.push(id);
  const freePop = () => freeSockets.pop();
  const queuePush = (task) => queue.push(task);
  const {
    publish,
    flushPending,
    hasPendingFrames,
    getPendingFrameCount,
    getPendingPromiseCount,
    resetPendingState
  } = lock;
  let inUsed = 0 | 0;
  const resetSignal = abortSignals?.resetSignal;
  const nowTime = now ?? p_now3;
  const onReturnResolved = (task) => {
    inUsed = inUsed - 1 | 0;
    resetTaskLocalFlags(task);
    runTaskFinalizers(task);
    task.value = null;
    task.resolve = PLACE_HOLDER;
    task.reject = PLACE_HOLDER;
    freePush(task[TaskIndex.ID]);
  };
  const returnResolvers = [
    returnLock,
    ...extraReturnLocks ?? []
  ].map((each) => each.resolveHost({
    queue,
    activeRejectPlaceholder: PLACE_HOLDER,
    onResolved: onReturnResolved
  }));
  const returnWaiters = [
    returnLock,
    ...extraReturnLocks ?? []
  ].map((each) => typeof each.waitForHostChange === "function" ? each.waitForHostChange : () => {
    return;
  });
  const returnArmers = [
    returnLock,
    ...extraReturnLocks ?? []
  ].map((each) => typeof each.setHostWaiterArmed === "function" ? each.setHostWaiterArmed : (_armed) => {});
  const returnHooks = new Array(returnResolvers.length);
  if (releaseBufferReferenceReturn !== undefined) {
    returnHooks[0] = releaseBufferReferenceReturn;
  }
  const resolveReturnAt = (index) => {
    const resolve = returnResolvers[index];
    const hooks = returnHooks[index];
    return hooks === undefined ? resolve() : withBufferReferenceReturnReleaser(hooks, resolve);
  };
  const completeFrame = returnResolvers.length === 1 ? releaseBufferReferenceReturn === undefined ? returnResolvers[0] : () => withBufferReferenceReturnReleaser(releaseBufferReferenceReturn, returnResolvers[0]) : () => {
    let resolved = 0 | 0;
    for (let i = 0;i < returnResolvers.length; i++) {
      resolved = resolved + resolveReturnAt(i) | 0;
    }
    return resolved;
  };
  const completionArmed = new Uint8Array(returnWaiters.length);
  let completionWake;
  let completionGeneration = 0 | 0;
  const setCompletionWaiterArmed = (armed) => {
    for (const setArmed of returnArmers)
      setArmed(armed);
  };
  const waitForCompletion = (onWake, timeoutMs) => {
    completionWake = onWake;
    setCompletionWaiterArmed(true);
    let supported = true;
    for (let index = 0;index < returnWaiters.length; index++) {
      if (completionArmed[index] !== 0)
        continue;
      let wait;
      try {
        wait = returnWaiters[index](timeoutMs);
      } catch {
        wait = undefined;
      }
      if (wait === undefined) {
        supported = false;
        break;
      }
      completionArmed[index] = 1;
      const generation = completionGeneration;
      const wakeLane = () => {
        if (completionArmed[index] === 0)
          return;
        completionArmed[index] = 0;
        returnArmers[index](false);
        if (generation !== completionGeneration)
          return;
        completionWake?.();
      };
      if (!wait.async)
        wakeLane();
      else
        Promise.resolve(wait.value).then(wakeLane, wakeLane);
    }
    if (!supported) {
      completionWake = undefined;
      setCompletionWaiterArmed(false);
      completionGeneration = completionGeneration + 1 | 0;
    }
    return supported;
  };
  const hasActiveTasks = () => {
    const count = inUsed - getPendingPromiseCount() | 0;
    return count > 0;
  };
  const txIdle = () => getPendingFrameCount() === 0 && !hasActiveTasks();
  const rejectAll = (reason) => {
    for (let index = 0;index < queue.length; index++) {
      const slot = queue[index];
      if (slot.reject !== PLACE_HOLDER) {
        try {
          slot.reject(reason);
        } catch {}
        runTaskFinalizers(slot);
        slot.resolve = PLACE_HOLDER;
        slot.reject = PLACE_HOLDER;
        queue[index] = newSlot(index);
      }
    }
    resetPendingState();
    inUsed = 0 | 0;
  };
  const flushToWorker = () => flushPending();
  const enqueueKnown = (task) => {
    return publish(task);
  };
  return {
    rejectAll,
    hasPendingFrames,
    txIdle,
    completeFrame,
    waitForCompletion,
    setCompletionWaiterArmed,
    setReturnHooks: (lane, hooks) => {
      if (!Number.isInteger(lane) || lane < 0 || lane >= returnHooks.length) {
        throw new RangeError(`return lane ${lane} out of range`);
      }
      returnHooks[lane] = hooks;
    },
    enqueue: (functionID, timeout, abortSignal) => {
      const HAS_TIMER = timeout !== undefined;
      const functionIDMasked = functionID & FUNCTION_ID_MASK;
      const USE_SIGNAL = abortSignal !== undefined && abortSignals !== undefined;
      return (rawArgs) => {
        if (inUsed === queue.length) {
          const newSize = inUsed + 32;
          let current = queue.length;
          while (newSize > current) {
            queuePush(newSlot(current));
            freePush(current);
            current++;
          }
        }
        const index = freePop();
        const slot = queue[index];
        const deferred = withResolvers();
        slot[TaskIndex.FunctionID] = functionIDMasked;
        if (USE_SIGNAL) {
          const maybeSignal = abortSignals.getSignal();
          if (maybeSignal === abortSignals.closeNow) {
            return Promise.reject(AbortSignalPoolExhausted);
          }
          new OneShotDeferred(deferred, () => resetSignal(maybeSignal), () => {
            abortSignals.setSignal(maybeSignal);
          });
          const encodedSignalMeta = (maybeSignal + ABORT_SIGNAL_META_OFFSET2 & FUNCTION_META_MASK) >>> 0;
          slot[TaskIndex.FunctionID] = (encodedSignalMeta << FUNCTION_META_SHIFT | functionIDMasked) >>> 0;
        }
        slot.value = rawArgs;
        slot[TaskIndex.ID] = index;
        slot.resolve = deferred.resolve;
        slot.reject = deferred.reject;
        if (HAS_TIMER) {
          slot[TaskIndex.slotBuffer] = (slot[TaskIndex.slotBuffer] & SLOT_INDEX_MASK | (nowTime() >>> 0 & SLOT_META_MASK) << SLOT_META_SHIFT >>> 0) >>> 0;
        }
        publish(slot);
        inUsed = inUsed + 1 | 0;
        return deferred.promise;
      };
    },
    flushToWorker,
    enqueueKnown,
    settlePromisePayload: (task, isRejected, value) => {
      if (task.reject === PLACE_HOLDER)
        return false;
      if (isRejected) {
        try {
          task.reject(value);
        } catch {}
        resetTaskLocalFlags(task);
        runTaskFinalizers(task);
        task.value = null;
        task.resolve = PLACE_HOLDER;
        task.reject = PLACE_HOLDER;
        inUsed = inUsed - 1 | 0;
        freePush(task[TaskIndex.ID]);
        return false;
      }
      task.value = value;
      return enqueueKnown(task);
    }
  };
}

// scripts/browser-stubs/process-worker.ts
var createProcessSharedMemoryAllocator = () => {
  return;
};
var createProcessWorkerNativeSignalNotifier = () => {
  return;
};
var cleanupProcessWorkerMemoryQuietly = () => {};
var unavailable3 = () => {
  throw new Error("process workers are unavailable in the browser build");
};
var createProcessWorkerMemoryLayout = unavailable3;
var createProcessStealMemoryLayout = unavailable3;
var readProcessSharedMemorySettings = unavailable3;
var readProcessWorkerCommandPrefix = unavailable3;
var readProcessWorkerNodeMajor = unavailable3;
var readProcessWorkerRuntime = unavailable3;
var spawnProcessWorker = unavailable3;
var toProcessWorkerBootPayload = unavailable3;

// src/runtime/worker-common.ts
var execFlagKey = (flag) => flag.split("=", 1)[0];
var NODE_PERMISSION_EXEC_FLAGS = new Set([
  "--permission",
  "--experimental-permission",
  "--allow-fs-read",
  "--allow-fs-write",
  "--allow-worker",
  "--allow-child-process",
  "--allow-net",
  "--allow-addons",
  "--allow-ffi",
  "--allow-wasi"
]);
var NODE_WORKER_SAFE_EXEC_FLAGS = new Set([
  "--experimental-ffi",
  "--experimental-transform-types",
  "--expose-gc",
  "--no-warnings",
  ...NODE_PERMISSION_EXEC_FLAGS
]);
var isNodeWorkerSafeExecFlag = (flag) => NODE_WORKER_SAFE_EXEC_FLAGS.has(execFlagKey(flag));
var isNodePermissionExecFlag = (flag) => NODE_PERMISSION_EXEC_FLAGS.has(execFlagKey(flag));
var toWorkerSafeExecArgv = (flags) => {
  if (!flags || flags.length === 0)
    return;
  const filtered = flags.filter(isNodeWorkerSafeExecFlag);
  if (filtered.length === 0)
    return;
  const seen = new Set;
  const deduped = [];
  for (const flag of filtered) {
    if (seen.has(flag))
      continue;
    seen.add(flag);
    deduped.push(flag);
  }
  return deduped;
};
var toWorkerCompatExecArgv = (flags) => {
  const safe = toWorkerSafeExecArgv(flags);
  if (!safe || safe.length === 0)
    return;
  const compat = safe.filter((flag) => !isNodePermissionExecFlag(flag));
  return compat.length > 0 ? compat : undefined;
};
var isPlainRecord = (value) => {
  if (value === null || typeof value !== "object")
    return false;
  const prototype = Object.getPrototypeOf(value);
  return prototype === Object.prototype || prototype === null;
};
var serializeWorkerBootstrapValue = (value, seen = new WeakMap) => {
  if (value instanceof ProcessSharedBuffer)
    return value.toMetadata();
  if (value === null || typeof value !== "object")
    return value;
  const existing = seen.get(value);
  if (existing !== undefined)
    return existing;
  if (Array.isArray(value)) {
    const out2 = [];
    seen.set(value, out2);
    for (const item of value) {
      out2.push(serializeWorkerBootstrapValue(item, seen));
    }
    return out2;
  }
  if (!isPlainRecord(value))
    return value;
  const out = {};
  seen.set(value, out);
  for (const [key, item] of Object.entries(value)) {
    out[key] = serializeWorkerBootstrapValue(item, seen);
  }
  return out;
};
var serializeWorkerBootstrapData = (options) => {
  const bootstrap = options.bootstrap;
  if (bootstrap === undefined || bootstrap.data === undefined)
    return options;
  return {
    ...options,
    bootstrap: {
      ...bootstrap,
      data: serializeWorkerBootstrapValue(bootstrap.data)
    }
  };
};
var terminateWorkerQuietly = (worker) => {
  try {
    worker.unref?.();
    return Promise.resolve(worker.terminate()).then(() => {}, () => {});
  } catch {
    return Promise.resolve();
  }
};

// src/runtime/dispatcher.ts
var IMMEDIATE_PUMP = RUNTIME === "deno" || RUNTIME === "node" ? SET_IMMEDIATE : undefined;
var POLL_STALL_FREE_LOOPS = 128;
var DOORBELL_STALL_FREE_LOOPS = 1;
var hostDispatcherLoop = ({
  signalBox: {
    opView,
    txStatus,
    rxStatus
  },
  queue: {
    completeFrame,
    hasPendingFrames,
    flushToWorker,
    txIdle,
    waitForCompletion,
    setCompletionWaiterArmed
  },
  channelHandler,
  dispatcherOptions,
  notifySignal,
  crossProcess
}) => {
  const a_load2 = Atomics.load;
  const a_store3 = Atomics.store;
  const a_notify = Atomics.notify;
  const canNotifySignal = opView.buffer instanceof SharedArrayBuffer;
  const wakeSignal = notifySignal ?? (() => {
    if (canNotifySignal)
      a_notify(opView, 0, 1);
  });
  const notify = () => channelHandler.notify();
  const canUseDoorbell = crossProcess !== true && (dispatcherOptions?.doorbell ?? true) && (RUNTIME === "bun" || RUNTIME === "node") && typeof Atomics.waitAsync === "function";
  let doorbellEnabled = canUseDoorbell;
  let doorbellArmed = false;
  let doorbellEpoch = 0 | 0;
  const DOORBELL_WATCHDOG_MS = 1000;
  let stallCount = 0 | 0;
  const requestedStallFreeLoops = dispatcherOptions?.stallFreeLoops;
  let stallFreeLoops = requestedStallFreeLoops !== undefined ? Math.max(0, requestedStallFreeLoops | 0) : canUseDoorbell ? DOORBELL_STALL_FREE_LOOPS : POLL_STALL_FREE_LOOPS;
  const MAX_BACKOFF_MS = Math.max(0, (dispatcherOptions?.maxBackoffMs ?? 10) | 0);
  let backoffTimer;
  let inFlight = false;
  const cancelDoorbell = () => {
    if (!doorbellArmed)
      return;
    doorbellEpoch = doorbellEpoch + 1 | 0;
    doorbellArmed = false;
    setCompletionWaiterArmed(false);
  };
  const armDoorbell = () => {
    if (!doorbellEnabled || doorbellArmed === true) {
      if (!doorbellEnabled)
        notify();
      return;
    }
    const token = doorbellEpoch + 1 | 0;
    doorbellEpoch = token;
    doorbellArmed = true;
    let woke = false;
    const wake = () => {
      if (!doorbellArmed || doorbellEpoch !== token || woke)
        return;
      woke = true;
      doorbellArmed = false;
      doorbellEpoch = doorbellEpoch + 1 | 0;
      setCompletionWaiterArmed(false);
      notify();
    };
    let supported = false;
    try {
      supported = waitForCompletion(wake, DOORBELL_WATCHDOG_MS);
    } catch {
      supported = false;
    }
    if (!supported) {
      doorbellEnabled = false;
      if (requestedStallFreeLoops === undefined) {
        stallFreeLoops = POLL_STALL_FREE_LOOPS;
      }
      doorbellArmed = false;
      doorbellEpoch = doorbellEpoch + 1 | 0;
      setCompletionWaiterArmed(false);
      notify();
    }
  };
  const check = () => {
    if (inFlight) {
      check.rerun = true;
      return;
    }
    cancelDoorbell();
    if (txIdle()) {
      check.isRunning = false;
      return;
    }
    inFlight = true;
    if (backoffTimer !== undefined) {
      clearTimeout(backoffTimer);
      backoffTimer = undefined;
    }
    do {
      check.rerun = false;
      txStatus[0] = 1;
      if (a_load2(rxStatus, 0) === 0) {
        a_store3(opView, 0, 1);
        wakeSignal();
      }
      let completed = false;
      let progressed = true;
      while (progressed) {
        progressed = false;
        if (completeFrame() > 0) {
          progressed = true;
          completed = true;
        }
        while (hasPendingFrames()) {
          if (!flushToWorker())
            break;
          progressed = true;
        }
      }
      txStatus[0] = 0;
      if (!txIdle()) {
        if (completed || hasPendingFrames()) {
          stallCount = 0 | 0;
        } else {
          stallCount = stallCount + 1 | 0;
        }
        inFlight = false;
        scheduleNotify();
        return;
      }
      stallCount = 0 | 0;
    } while (check.rerun);
    check.isRunning = false;
    inFlight = false;
  };
  check.isRunning = false;
  check.rerun = false;
  const scheduleNotify = () => {
    if (stallCount <= stallFreeLoops) {
      notify();
      return;
    }
    if (doorbellEnabled) {
      check.isRunning = false;
      armDoorbell();
      return;
    }
    if (backoffTimer !== undefined)
      return;
    let delay = stallCount - stallFreeLoops - 1 | 0;
    if (delay < 0)
      delay = 0;
    else if (delay > MAX_BACKOFF_MS)
      delay = MAX_BACKOFF_MS;
    check.isRunning = false;
    backoffTimer = setTimeout(() => {
      backoffTimer = undefined;
      if (!check.isRunning) {
        check.isRunning = true;
        check();
      }
    }, delay);
  };
  return { check };
};

class ChannelHandler {
  channel;
  port1;
  port2;
  #handler;
  #notify;
  constructor(pump = "auto") {
    if (pump === "auto" && IMMEDIATE_PUMP !== undefined) {
      const immediate = IMMEDIATE_PUMP;
      const run = () => {
        this.#handler?.();
      };
      this.#notify = () => {
        immediate(run);
      };
      return;
    }
    const channel = createRuntimeMessageChannel();
    const port2 = channel.port2;
    this.channel = channel;
    this.port1 = channel.port1;
    this.port2 = port2;
    this.#notify = () => {
      port2.postMessage(null);
    };
  }
  notify() {
    this.#notify();
  }
  open(f) {
    this.#handler = f;
    const port1 = this.port1;
    if (port1 === undefined)
      return;
    if (typeof port1.on === "function") {
      port1.on("message", f);
    } else {
      port1.onmessage = f;
    }
    this.port1?.start?.();
    this.port2?.start?.();
  }
  close() {
    this.#handler = undefined;
    if (this.port1 === undefined || this.port2 === undefined)
      return;
    this.port1.onmessage = null;
    this.port2.onmessage = null;
    this.port1.close?.();
    this.port2.close?.();
  }
}

// scripts/browser-stubs/compiled-worker.ts
var spawnCompiledWorkerContext = () => {
  throw new Error("compiled workers are unavailable in the browser build");
};

// src/runtime/pool.ts
var WORKER_FATAL_MESSAGE_KEY2 = "__knittingWorkerFatal";
var isWorkerFatalMessage = (value) => !!value && typeof value === "object" && typeof value[WORKER_FATAL_MESSAGE_KEY2] === "string";
var DEFAULT_WORKER_PARK_MS = 1;
var DEFAULT_ABORT_SIGNAL_CAPACITY = 258;
var sanitizePositiveInteger = (value) => {
  if (!Number.isFinite(value))
    return;
  const parsed = Math.floor(value);
  return parsed > 0 ? parsed : undefined;
};
var resolveAbortSignalCapacity = (value) => sanitizePositiveInteger(value) ?? DEFAULT_ABORT_SIGNAL_CAPACITY;
var abortSignalByteLength = (capacity) => Math.max(1, Math.ceil(capacity / 32)) * Uint32Array.BYTES_PER_ELEMENT;
var withDefaultWorkerTimers = (options) => {
  const parkMs = options?.timers?.parkMs ?? DEFAULT_WORKER_PARK_MS;
  if (options === undefined)
    return { timers: { parkMs } };
  return {
    ...options,
    timers: {
      ...options.timers,
      parkMs
    }
  };
};
var withFixedPayloadConfig = (config) => ({
  ...config,
  mode: "fixed",
  payloadInitialBytes: config.payloadMaxByteLength
});
var resolveStealRegionLanes = (consumers) => {
  for (let lanes = LockBound.slots;lanes >= 1; lanes >>= 1) {
    if (LockBound.slots / lanes >= consumers + 1)
      return lanes;
  }
  throw new RangeError(`${consumers} stealing workers need more than ${LockBound.slots} lanes`);
};
var MAX_STEAL_CONSUMERS = LockBound.slots - 1;
var createStealPoolBuffers = ({
  threads,
  payload,
  regionLanes,
  abortSignalCapacity,
  usesAbortSignal,
  processWorker
}) => {
  const basePayloadConfig = resolvePayloadBufferOptions({ options: payload });
  const payloadConfig = processWorker === undefined ? basePayloadConfig : withFixedPayloadConfig(basePayloadConfig);
  const makePayload = () => payloadConfig.mode === "growable" ? createSharedArrayBuffer(payloadConfig.payloadInitialBytes, payloadConfig.payloadMaxByteLength) : createSharedArrayBuffer(payloadConfig.payloadInitialBytes);
  const carpet = () => createLockControlCarpet({
    signalBytes: 0,
    abortBytes: 0,
    lockSectorBytes: LOCK_SECTOR_BYTE_LENGTH,
    headerSlotStrideU32: HEADER_SLOT_STRIDE_U32,
    slotCount: LockBound.slots,
    headerLayout: "split"
  });
  const toBuffers = (half, payloadSab) => ({
    ...half,
    payload: payloadSab,
    textCompat: probeLockBufferTextCompat({
      headers: half.headers,
      payload: payloadSab
    })
  });
  const maxLanes = resolveStealRegionLanes(threads);
  const lanes = regionLanes === undefined ? maxLanes : Math.min(Math.max(1, regionLanes | 0), maxLanes);
  const resolvedAbortSignalCapacity = resolveAbortSignalCapacity(abortSignalCapacity);
  const processMemory = processWorker === undefined ? undefined : createProcessStealMemoryLayout({
    threads,
    signalBytes: processWorker.signalBytes,
    abortBytes: usesAbortSignal === true ? abortSignalByteLength(resolvedAbortSignalCapacity) : 0,
    abortSignalMax: usesAbortSignal === true ? resolvedAbortSignalCapacity : undefined,
    payloadBytes: payloadConfig.payloadMaxByteLength,
    sharedMemory: processWorker.sharedMemory
  });
  const submitBuffers = processMemory === undefined ? (() => {
    const submitCarpet = carpet();
    return toBuffers(submitCarpet.lock, makePayload());
  })() : toBuffers(processMemory.workers[0].controlLayout.lock, processMemory.workers[0].lockPayload);
  const hostSubmitLock = lock2({
    headers: submitBuffers.headers,
    headerSlotStrideU32: submitBuffers.headerSlotStrideU32,
    LockBoundSector: submitBuffers.lockSector,
    payload: submitBuffers.payload,
    payloadSector: submitBuffers.payloadSector,
    payloadConfig,
    textCompat: submitBuffers.textCompat,
    consumers: threads,
    regionLanes: lanes,
    processBoundary: processMemory !== undefined
  });
  const returnBuffers = [];
  const hostReturnLocks = [];
  for (let i = 0;i < threads; i++) {
    const buffers = processMemory === undefined ? toBuffers(carpet().returnLock, makePayload()) : toBuffers(processMemory.workers[i].controlLayout.returnLock, processMemory.workers[i].returnPayload);
    returnBuffers.push(buffers);
    hostReturnLocks.push(lock2({
      headers: buffers.headers,
      headerSlotStrideU32: buffers.headerSlotStrideU32,
      LockBoundSector: buffers.lockSector,
      payload: buffers.payload,
      payloadSector: buffers.payloadSector,
      payloadConfig,
      textCompat: buffers.textCompat,
      processBoundary: processMemory !== undefined
    }));
  }
  const abortSignalSAB = usesAbortSignal === true ? processMemory?.workers[0]?.controlLayout.abortSignals ?? createSharedArrayBuffer(abortSignalByteLength(resolvedAbortSignalCapacity)) : undefined;
  const abortSignals = abortSignalSAB === undefined ? undefined : signalAbortFactory({
    sab: abortSignalSAB,
    maxSignals: resolvedAbortSignalCapacity
  });
  const sharedQueue = createHostTxQueue({
    lock: hostSubmitLock,
    returnLock: hostReturnLocks[0],
    extraReturnLocks: hostReturnLocks.slice(1),
    abortSignals
  });
  return {
    submitBuffers,
    returnBuffers,
    hostSubmitLock,
    hostReturnLocks,
    sharedQueue,
    regionLanes: lanes,
    processMemory,
    abortSignalSAB,
    abortSignalMax: processMemory?.abortSignalMax ?? (abortSignalSAB === undefined ? undefined : resolvedAbortSignalCapacity)
  };
};
var spawnWorkerContext = ({
  list,
  ids,
  names,
  sab,
  thread,
  debug,
  hostDebug,
  totalNumberOfThread,
  source,
  at,
  workerOptions,
  workerExecArgv,
  permission,
  host,
  payload,
  bufferReferenceReturn,
  abortSignalCapacity,
  usesAbortSignal,
  sharedChannelHandler,
  stealPool
}) => {
  if (workerOptions?.runtime === "compiled") {
    return spawnCompiledWorkerContext({
      list,
      names,
      workerOptions,
      hostDebug,
      abortSignalCapacity,
      usesAbortSignal
    });
  }
  const tsFileUrl = new URL(import.meta.url);
  const poliWorker = RUNTIME_WORKER;
  const resolvedWorkerOptions = serializeWorkerBootstrapData(withDefaultWorkerTimers(workerOptions));
  const useProcessWorkerRuntime = resolvedWorkerOptions.runtime === "process";
  const processWorkerRuntime = useProcessWorkerRuntime ? readProcessWorkerRuntime(resolvedWorkerOptions) : undefined;
  const processWorkerCommandPrefix = useProcessWorkerRuntime ? readProcessWorkerCommandPrefix(resolvedWorkerOptions) : undefined;
  const processSharedMemorySettings = useProcessWorkerRuntime ? readProcessSharedMemorySettings(resolvedWorkerOptions) : undefined;
  if (!useProcessWorkerRuntime && typeof poliWorker !== "function") {
    throw new Error("Worker is not available in this runtime");
  }
  if (IS_BROWSER && typeof SharedArrayBuffer !== "function") {
    throw new Error("SharedArrayBuffer is unavailable: serve the page cross-origin isolated " + "(Cross-Origin-Opener-Policy: same-origin, " + "Cross-Origin-Embedder-Policy: require-corp).");
  }
  const WorkerCtor = poliWorker;
  const sanitizeBytes = sanitizePositiveInteger;
  const basePayloadConfig = resolvePayloadBufferOptions({
    options: payload
  });
  const resolvedPayloadConfig = useProcessWorkerRuntime ? withFixedPayloadConfig(basePayloadConfig) : basePayloadConfig;
  const resolvedAbortSignalCapacity = resolveAbortSignalCapacity(abortSignalCapacity);
  const requestedSignalBytes = sanitizeBytes(sab?.size);
  const externalSignalSab = sab?.sharedSab;
  if (useProcessWorkerRuntime && externalSignalSab != null) {
    throw new Error("process worker runtime cannot use an external signal buffer");
  }
  const signalBytes = Math.max(TRANSPORT_SIGNAL_BYTES, requestedSignalBytes ?? TRANSPORT_SIGNAL_BYTES);
  const abortBytes = stealPool === undefined && usesAbortSignal === true ? abortSignalByteLength(resolvedAbortSignalCapacity) : 0;
  const stealProcessMemory = stealPool?.processMemory;
  const processWorkerMemory = !useProcessWorkerRuntime ? undefined : stealProcessMemory === undefined ? createProcessWorkerMemoryLayout({
    signalBytes,
    abortBytes,
    payloadBytes: resolvedPayloadConfig.payloadMaxByteLength,
    thread,
    sharedMemory: processSharedMemorySettings
  }) : stealProcessMemory.workers[thread] ?? (() => {
    throw new RangeError(`stealing process pool has no shared-memory slice for worker ${thread}`);
  })();
  const processSharedMemory = processWorkerMemory === undefined ? createProcessSharedMemoryAllocator(debug) : undefined;
  const createControlBuffer = processSharedMemory?.createBuffer ?? createWasmSharedArrayBuffer;
  const createPayloadBuffer = processSharedMemory?.createBuffer;
  const makePayloadBuffer = () => createPayloadBuffer ? createPayloadBuffer(resolvedPayloadConfig.payloadMaxByteLength) : resolvedPayloadConfig.mode === "growable" ? createSharedArrayBuffer(resolvedPayloadConfig.payloadInitialBytes, resolvedPayloadConfig.payloadMaxByteLength) : createSharedArrayBuffer(resolvedPayloadConfig.payloadInitialBytes);
  const makeLockControlLayout = () => {
    return createLockControlCarpet({
      signalBytes,
      abortBytes,
      lockSectorBytes: LOCK_SECTOR_BYTE_LENGTH,
      headerSlotStrideU32: HEADER_SLOT_STRIDE_U32,
      slotCount: LockBound.slots,
      headerLayout: "split",
      createBuffer: createControlBuffer
    });
  };
  const controlLayout = processWorkerMemory?.controlLayout ?? makeLockControlLayout();
  const lockPayload = processWorkerMemory?.lockPayload ?? makePayloadBuffer();
  const lockBuffers = stealPool?.submitBuffers ?? {
    ...controlLayout.lock,
    payload: lockPayload,
    textCompat: probeLockBufferTextCompat({
      headers: controlLayout.lock.headers,
      payload: lockPayload
    })
  };
  const returnPayload = processWorkerMemory?.returnPayload ?? makePayloadBuffer();
  const returnLockBuffers = stealPool?.returnBuffers ?? {
    ...controlLayout.returnLock,
    payload: returnPayload,
    textCompat: probeLockBufferTextCompat({
      headers: controlLayout.returnLock.headers,
      payload: returnPayload
    })
  };
  const lock = stealPool?.hostSubmitLock ?? lock2({
    headers: lockBuffers.headers,
    headerSlotStrideU32: lockBuffers.headerSlotStrideU32,
    LockBoundSector: lockBuffers.lockSector,
    payload: lockBuffers.payload,
    payloadSector: lockBuffers.payloadSector,
    payloadConfig: resolvedPayloadConfig,
    textCompat: lockBuffers.textCompat,
    processBoundary: useProcessWorkerRuntime
  });
  const returnLock = stealPool?.hostReturnLock ?? lock2({
    headers: returnLockBuffers.headers,
    headerSlotStrideU32: returnLockBuffers.headerSlotStrideU32,
    LockBoundSector: returnLockBuffers.lockSector,
    payload: returnLockBuffers.payload,
    payloadSector: returnLockBuffers.payloadSector,
    payloadConfig: resolvedPayloadConfig,
    textCompat: returnLockBuffers.textCompat,
    processBoundary: useProcessWorkerRuntime
  });
  const abortSignalSAB = stealPool?.abortSignalSAB ?? (usesAbortSignal === true ? controlLayout.abortSignals : undefined);
  const abortSignals = abortSignalSAB && stealPool === undefined ? signalAbortFactory({
    sab: abortSignalSAB,
    maxSignals: resolvedAbortSignalCapacity
  }) : undefined;
  const signals = createSharedMemoryTransport({
    sabObject: externalSignalSab == null ? {
      size: requestedSignalBytes,
      sharedSab: controlLayout.signals
    } : sab,
    isMain: true,
    thread
  });
  const signalBox = signals;
  const nativeNotifySignal = createProcessWorkerNativeSignalNotifier({
    processRuntime: processWorkerRuntime,
    signal: signalBox.opView
  });
  const outstandingBorrowedReturns = bufferReferenceReturn === "borrow" && typeof WeakRef === "function" ? new Map : undefined;
  const releaseBorrowedReturnToken = (token) => {
    outstandingBorrowedReturns?.delete(token);
    worker?.postMessage?.(createBufferReferenceReturnReleaseMessage(token));
  };
  const revokeOutstandingBorrowedReturns = (copyBytes) => {
    if (outstandingBorrowedReturns === undefined)
      return;
    for (const [token, record] of outstandingBorrowedReturns) {
      try {
        const ref = record.ref.deref();
        if (ref !== undefined) {
          ref.revokeBorrow(copyBytes);
          continue;
        }
        const aliasBuffer = record.aliasBuffer?.deref();
        if (aliasBuffer !== undefined && detachArrayBufferBestEffort(record.runtime, aliasBuffer) && copyBytes) {
          releaseBorrowedReturnToken(token);
        }
      } catch {}
    }
    outstandingBorrowedReturns.clear();
  };
  const returnHooks = bufferReferenceReturn === "borrow" ? {
    release: releaseBorrowedReturnToken,
    track: (ref, token, aliasBuffer) => {
      if (outstandingBorrowedReturns === undefined)
        return;
      const record = outstandingBorrowedReturns.get(token);
      if (record !== undefined) {
        if (aliasBuffer !== undefined) {
          record.aliasBuffer = new WeakRef(aliasBuffer);
        }
        return;
      }
      outstandingBorrowedReturns.set(token, {
        ref: new WeakRef(ref),
        aliasBuffer: aliasBuffer === undefined ? undefined : new WeakRef(aliasBuffer),
        runtime: ref.runtime
      });
    }
  } : undefined;
  const queue = stealPool?.sharedQueue ?? createHostTxQueue({
    lock,
    returnLock,
    abortSignals,
    releaseBufferReferenceReturn: returnHooks
  });
  if (stealPool !== undefined) {
    stealPool.sharedQueue.setReturnHooks(stealPool.consumerId, returnHooks);
  }
  const {
    enqueue,
    rejectAll,
    txIdle
  } = queue;
  const thisSignal = signalBox.opView;
  const a_add = Atomics.add;
  const a_load2 = Atomics.load;
  const a_notify = Atomics.notify;
  const canNotifySignal = thisSignal.buffer instanceof SharedArrayBuffer;
  const notifySignal = nativeNotifySignal ?? (canNotifySignal ? () => a_notify(thisSignal, 0, 1) : undefined);
  const laneWake = () => {
    if (a_load2(signalBox.rxStatus, 0) === 0) {
      a_add(thisSignal, 0, 1);
      notifySignal?.();
    }
  };
  let dispatchSend = () => {};
  const send = () => dispatchSend();
  let channelHandler;
  const ownsChannel = sharedChannelHandler === undefined && stealPool === undefined;
  const ownChannel = sharedChannelHandler ?? new ChannelHandler;
  const { check: dispatcherCheck } = stealPool !== undefined ? { check: undefined } : hostDispatcherLoop({
    signalBox,
    queue,
    channelHandler: ownChannel,
    dispatcherOptions: host,
    notifySignal: nativeNotifySignal,
    crossProcess: useProcessWorkerRuntime
  });
  if (ownsChannel && dispatcherCheck !== undefined) {
    ownChannel.open(dispatcherCheck);
    channelHandler = ownChannel;
    dispatchSend = () => {
      if (dispatcherCheck.isRunning === true)
        return;
      dispatcherCheck.isRunning = true;
      Promise.resolve().then(dispatcherCheck);
      laneWake();
    };
  }
  let worker;
  const workerUrl = source ?? tsFileUrl;
  const workerMode = useProcessWorkerRuntime ? "process" : HAS_NODE_WORKER_THREADS ? "worker_threads" : "worker";
  hostDebug?.(`worker thread=${thread} mode=${workerMode}` + `${processWorkerRuntime ? ` runtime=${processWorkerRuntime}` : ""}` + ` url=${String(workerUrl)}`);
  const workerDataPayload = {
    sab: signals.sab,
    abortSignalSAB,
    abortSignalMax: stealPool?.abortSignalMax ?? (usesAbortSignal === true ? resolvedAbortSignalCapacity : undefined),
    list,
    ids,
    names,
    at,
    thread,
    debug,
    workerOptions: resolvedWorkerOptions,
    totalNumberOfThread,
    startAt: signalBox.startAt,
    lock: lockBuffers,
    returnLock: returnLockBuffers,
    payloadConfig: resolvedPayloadConfig,
    bufferReferenceReturn,
    permission,
    notifyOnHostPublish: !useProcessWorkerRuntime && host?.doorbell !== false && (RUNTIME === "bun" || RUNTIME === "node") && typeof Atomics.waitAsync === "function",
    steal: stealPool === undefined ? undefined : {
      consumers: stealPool.consumers,
      consumerId: stealPool.consumerId,
      regionLanes: stealPool.regionLanes
    }
  };
  const baseWorkerOptions = {
    type: "module",
    workerData: workerDataPayload
  };
  const withExecArgv = workerExecArgv && workerExecArgv.length > 0 ? { ...baseWorkerOptions, execArgv: workerExecArgv } : baseWorkerOptions;
  if (processWorkerMemory !== undefined) {
    worker = spawnProcessWorker({
      workerUrl,
      bootPayload: toProcessWorkerBootPayload(workerDataPayload, processWorkerMemory),
      memory: processWorkerMemory,
      processRuntime: processWorkerRuntime,
      commandPrefix: processWorkerCommandPrefix,
      permission
    });
  } else if (HAS_NODE_WORKER_THREADS) {
    try {
      worker = new WorkerCtor(workerUrl, withExecArgv);
    } catch (error) {
      if (error?.code === "ERR_WORKER_INVALID_EXEC_ARGV") {
        const fallbackExecArgv = toWorkerSafeExecArgv(withExecArgv.execArgv);
        if (fallbackExecArgv && fallbackExecArgv.length > 0) {
          try {
            worker = new WorkerCtor(workerUrl, { ...baseWorkerOptions, execArgv: fallbackExecArgv });
          } catch (fallbackError) {
            if (fallbackError?.code === "ERR_WORKER_INVALID_EXEC_ARGV") {
              const compatExecArgv = toWorkerCompatExecArgv(fallbackExecArgv);
              if (compatExecArgv && compatExecArgv.length > 0) {
                try {
                  worker = new WorkerCtor(workerUrl, { ...baseWorkerOptions, execArgv: compatExecArgv });
                } catch {
                  worker = new WorkerCtor(workerUrl, baseWorkerOptions);
                }
              } else {
                worker = new WorkerCtor(workerUrl, baseWorkerOptions);
              }
            } else {
              throw fallbackError;
            }
          }
        } else {
          worker = new WorkerCtor(workerUrl, baseWorkerOptions);
        }
      } else {
        throw error;
      }
    }
  } else {
    worker = new WorkerCtor(workerUrl, {
      type: "module"
    });
    worker.postMessage?.(workerDataPayload);
  }
  let closedReason;
  const deactivateStealConsumer = () => {
    stealPool?.hostSubmitLock.deactivateStealConsumer(stealPool.consumerId);
  };
  const terminateFailedWorker = () => {
    try {
      worker.unref?.();
      Promise.resolve(worker.terminate()).catch(() => {}).finally(deactivateStealConsumer);
    } catch {
      deactivateStealConsumer();
    }
  };
  const markWorkerClosed = (reason, workerBytesReadable = false) => {
    if (closedReason)
      return;
    closedReason = reason;
    revokeOutstandingBorrowedReturns(workerBytesReadable);
    rejectAll(reason);
    channelHandler?.close();
  };
  const onWorkerMessage = (message) => {
    if (!isWorkerFatalMessage(message))
      return;
    markWorkerClosed(`Worker startup failed: ${message[WORKER_FATAL_MESSAGE_KEY2]}`, true);
    terminateFailedWorker();
  };
  const onWorkerError = (error) => {
    const message = String(error?.message ?? error);
    markWorkerClosed(`Worker crashed: ${message}`);
    terminateFailedWorker();
  };
  const nodeWorker = worker;
  if (typeof nodeWorker.on === "function") {
    nodeWorker.on("message", onWorkerMessage);
    nodeWorker.on("error", onWorkerError);
    nodeWorker.on("exit", (code) => {
      deactivateStealConsumer();
      if (closedReason !== undefined)
        return;
      const normalized = typeof code === "number" ? code : -1;
      markWorkerClosed(`Worker exited with code ${normalized}`);
    });
  } else {
    const eventWorker = worker;
    if (typeof eventWorker.addEventListener === "function") {
      eventWorker.addEventListener("message", (event) => {
        onWorkerMessage(event?.data);
      });
      eventWorker.addEventListener("error", (event) => {
        onWorkerError(event?.error ?? event?.message ?? event);
      });
    } else {
      eventWorker.onmessage = (event) => {
        onWorkerMessage(event?.data);
      };
      eventWorker.onerror = (event) => {
        onWorkerError(event);
      };
    }
  }
  lock.setPromiseHandler((task, isRejected, value) => {
    queue.settlePromisePayload(task, isRejected, value);
    send();
  });
  const call = ({ fnNumber, timeout, abortSignal }) => {
    const enqueues = enqueue(fnNumber, timeout, abortSignal);
    return (args) => {
      const pending = enqueues(args);
      send();
      return pending;
    };
  };
  const context = {
    txIdle,
    call,
    kills: async () => {
      markWorkerClosed("Thread closed", true);
      const termination = terminateWorkerQuietly(worker);
      if (processWorkerMemory !== undefined)
        await termination;
      cleanupProcessWorkerMemoryQuietly(processWorkerMemory);
    },
    lock,
    processSharedMemoryBackings: processSharedMemory?.backings,
    dispatcherCheck,
    laneWake: sharedChannelHandler !== undefined || stealPool !== undefined ? laneWake : undefined,
    bindSend: sharedChannelHandler !== undefined || stealPool !== undefined ? (fn) => void (dispatchSend = fn) : undefined
  };
  return context;
};

// scripts/browser-stubs/permission.ts
var resolvePermissionProtocol = () => {
  return;
};
var toRuntimePermissionFlags = () => [];
var unavailable4 = () => {
  throw new Error("process workers are unavailable in the browser build");
};
var classifyProcessPermissionCompatibility = unavailable4;
var enforceProcessPermissionCompatibility = unavailable4;

// src/runtime/balancer.ts
var selectStrategy = (contexts, handlers, strategy) => {
  switch (strategy ?? "roundRobin") {
    case "roundRobin":
    case "robinRound":
      return roundRobin(contexts)(handlers)(handlers.length);
    case "firstIdle":
      return firstIdle(contexts)(handlers)(handlers.length);
    case "randomLane":
      return randomLane(contexts)(handlers)(handlers.length);
    case "firstIdleOrRandom":
      return firstIdleRandom(contexts)(handlers)(handlers.length);
  }
  throw new Error(`Unknown balancer: ${strategy}`);
};
var managerMethod = ({
  contexts,
  balancer,
  handlers,
  inlinerGate
}) => {
  const strategy = typeof balancer === "object" && balancer != null ? balancer.strategy : balancer;
  if (contexts.length < 2) {
    throw new Error(contexts.length === 0 ? "No threads available." : "Cannot rotate with a single thread.");
  }
  if (handlers.length === 0) {
    throw new Error("No handlers provided.");
  }
  const allInvoker = selectStrategy(contexts, handlers, strategy);
  if (!inlinerGate) {
    return allInvoker;
  }
  const inlinerIndex = inlinerGate.index | 0;
  const threshold = Number.isFinite(inlinerGate.threshold) ? Math.max(1, Math.floor(inlinerGate.threshold)) : 1;
  if (threshold <= 1 || inlinerIndex < 0 || inlinerIndex >= handlers.length) {
    return allInvoker;
  }
  const workerLaneCount = handlers.length - 1;
  if (workerLaneCount <= 0) {
    return allInvoker;
  }
  const workerHandlers = new Array(workerLaneCount);
  const workerContexts = new Array(workerLaneCount);
  for (let source = 0, lane = 0;source < handlers.length; source += 1) {
    if (source === inlinerIndex)
      continue;
    workerHandlers[lane] = handlers[source];
    workerContexts[lane] = contexts[source];
    lane += 1;
  }
  const workerOnlyInvoker = selectStrategy(workerContexts, workerHandlers, strategy);
  let inFlight = 0;
  const releaseResolved = (value) => {
    inFlight -= 1;
    return value;
  };
  const releaseRejected = (error) => {
    inFlight -= 1;
    throw error;
  };
  return (args) => {
    inFlight += 1;
    const invoker = inFlight >= threshold ? allInvoker : workerOnlyInvoker;
    try {
      return invoker(args).then(releaseResolved, releaseRejected);
    } catch (error) {
      inFlight -= 1;
      throw error;
    }
  };
};
function roundRobin(_contexts) {
  return (handlers) => {
    return (max) => {
      const top = Math.min(max, handlers.length);
      if (top <= 1) {
        return (args) => handlers[0](args);
      }
      let rrCursor = 0;
      return (args) => {
        const lane = rrCursor;
        rrCursor += 1;
        if (rrCursor === top)
          rrCursor = 0;
        return handlers[lane](args);
      };
    };
  };
}
function firstIdle(contexts) {
  const isSolved = contexts.map((ctx) => ctx.txIdle);
  return (handlers) => {
    return (max) => {
      const laneCount = Math.min(max, handlers.length);
      if (laneCount <= 1) {
        return (args) => handlers[0](args);
      }
      let rrCursor = 0;
      return (args) => {
        for (let lane = 0;lane < laneCount; lane += 1) {
          if (isSolved[lane]()) {
            return handlers[lane](args);
          }
        }
        const fallback = rrCursor;
        rrCursor += 1;
        if (rrCursor === laneCount)
          rrCursor = 0;
        return handlers[fallback](args);
      };
    };
  };
}
var randomLane = (_) => {
  return (handlers) => {
    return (max) => {
      const laneCount = Math.min(max, handlers.length);
      if (laneCount <= 1) {
        return (args) => handlers[0](args);
      }
      return (args) => {
        const lane = Math.random() * laneCount | 0;
        return handlers[lane](args);
      };
    };
  };
};
function firstIdleRandom(contexts) {
  const isSolved = contexts.map((ctx) => ctx.txIdle);
  return (handlers) => {
    return (max) => {
      const laneCount = Math.min(max, handlers.length);
      if (laneCount <= 1) {
        return (args) => handlers[0](args);
      }
      return (args) => {
        for (let lane = 0;lane < laneCount; lane += 1) {
          if (isSolved[lane]()) {
            return handlers[lane](args);
          }
        }
        const fallback = Math.random() * laneCount | 0;
        return handlers[fallback](args);
      };
    };
  };
}

// src/runtime/inline-executor.ts
var SlotStateMacro = {
  Free: -1,
  Pending: 0
};
var TimeoutKind2 = {
  Reject: 0,
  Resolve: 1
};
var normalizeTimeout2 = (timeout) => {
  if (timeout == null)
    return;
  if (typeof timeout === "number") {
    return timeout >= 0 ? { ms: timeout, kind: TimeoutKind2.Reject, value: new Error("Task timeout") } : undefined;
  }
  const ms = timeout.time;
  if (!(ms >= 0))
    return;
  if ("default" in timeout) {
    return { ms, kind: TimeoutKind2.Resolve, value: timeout.default };
  }
  if (timeout.maybe === true) {
    return { ms, kind: TimeoutKind2.Resolve, value: undefined };
  }
  if ("error" in timeout) {
    return { ms, kind: TimeoutKind2.Reject, value: timeout.error };
  }
  return { ms, kind: TimeoutKind2.Reject, value: new Error("Task timeout") };
};
var raceTimeout2 = (promise, spec) => new Promise((resolve, reject) => {
  let done = false;
  const timer = setTimeout(() => {
    if (done)
      return;
    done = true;
    if (spec.kind === TimeoutKind2.Resolve) {
      resolve(spec.value);
    } else {
      reject(spec.value);
    }
  }, spec.ms);
  promise.then((value) => {
    if (done)
      return;
    done = true;
    clearTimeout(timer);
    resolve(value);
  }, (err) => {
    if (done)
      return;
    done = true;
    clearTimeout(timer);
    reject(err);
  });
});
var INLINE_ABORT_TOOLKIT = (() => {
  const hasAborted = () => false;
  const now = () => performance.now();
  return {
    hasAborted,
    now
  };
})();
var composeInlineCallable = (fn, timeout, useAbortToolkit = false) => {
  const normalized = normalizeTimeout2(timeout);
  const run = useAbortToolkit ? (args) => fn(args, INLINE_ABORT_TOOLKIT) : fn;
  if (!normalized)
    return run;
  return (args) => {
    const result = run(args);
    return result instanceof Promise ? raceTimeout2(result, normalized) : result;
  };
};
var createInlineExecutor = ({
  tasks,
  genTaskID: genTaskID2,
  batchSize
}) => {
  const entries = Array.isArray(tasks) ? tasks : Object.values(tasks).sort((a, b) => a.name.localeCompare(b.name));
  const runners = entries.map((entry) => {
    if (entry.imported === true) {
      return () => {
        throw new Error("Imported task cannot run on the host inline lane");
      };
    }
    return composeInlineCallable(entry.f, entry.timeout, entry.abortSignal !== undefined);
  });
  const initCap = 16;
  let fnByIndex = new Int32Array(initCap);
  let stateByIndex = new Int8Array(initCap).fill(SlotStateMacro.Free);
  let argsByIndex = new Array(initCap);
  let taskIdByIndex = new Array(initCap).fill(-1);
  let deferredByIndex = new Array(initCap);
  const freeStack = new Array(initCap);
  let freeTop = initCap;
  for (let i = 0;i < initCap; i++)
    freeStack[i] = initCap - 1 - i;
  const pendingQueue = new RingQueue(initCap);
  let working = 0;
  let isInMacro = false;
  let isInMicro = false;
  const batchLimit = Number.isFinite(batchSize) ? Math.max(1, Math.floor(batchSize ?? 1)) : Number.POSITIVE_INFINITY;
  const channel = createRuntimeMessageChannel();
  const port1 = channel.port1;
  const port2 = channel.port2;
  const post2 = (message) => port2.postMessage(message);
  const hasPending = () => pendingQueue.isEmpty === false;
  const queueMicro = typeof queueMicrotask === "function" ? queueMicrotask : (callback) => Promise.resolve().then(callback);
  const scheduleMacro = () => {
    if (working === 0 || isInMacro)
      return;
    isInMacro = true;
    post2(null);
  };
  const send = () => {
    if (working === 0 || isInMacro || isInMicro)
      return;
    isInMicro = true;
    queueMicro(runMicroLoop);
  };
  const enqueue = (index) => {
    pendingQueue.push(index);
    send();
  };
  const enqueueIfCurrent = (index, taskID) => {
    if (stateByIndex[index] !== SlotStateMacro.Pending || taskIdByIndex[index] !== taskID)
      return;
    enqueue(index);
  };
  const settleIfCurrent = (index, taskID, isError, value) => {
    if (stateByIndex[index] !== SlotStateMacro.Pending || taskIdByIndex[index] !== taskID)
      return;
    const deferred = deferredByIndex[index];
    if (deferred) {
      if (isError)
        deferred.reject(value);
      else
        deferred.resolve(value);
    }
    cleanup(index);
  };
  function allocIndex() {
    if (freeTop > 0)
      return freeStack[--freeTop];
    const oldCap = fnByIndex.length;
    const newCap = oldCap << 1;
    const nextFnByIndex = new Int32Array(newCap);
    nextFnByIndex.set(fnByIndex);
    fnByIndex = nextFnByIndex;
    const nextStateByIndex = new Int8Array(newCap);
    nextStateByIndex.fill(SlotStateMacro.Free);
    nextStateByIndex.set(stateByIndex);
    stateByIndex = nextStateByIndex;
    argsByIndex.length = newCap;
    taskIdByIndex.length = newCap;
    taskIdByIndex.fill(-1, oldCap);
    deferredByIndex.length = newCap;
    for (let i = newCap - 1;i >= oldCap; --i) {
      freeStack[freeTop++] = i;
    }
    return freeStack[--freeTop];
  }
  function processLoop(fromMicro = false) {
    let processed = 0;
    while (processed < batchLimit) {
      const maybeIndex = pendingQueue.shiftNoClear();
      if (maybeIndex === undefined)
        break;
      const index = maybeIndex | 0;
      if (stateByIndex[index] !== SlotStateMacro.Pending)
        continue;
      const taskID = taskIdByIndex[index];
      try {
        const args = argsByIndex[index];
        const fnId = fnByIndex[index];
        const res = runners[fnId](args);
        if (!(res instanceof Promise)) {
          settleIfCurrent(index, taskID, false, res);
          processed++;
          continue;
        }
        res.then((value) => settleIfCurrent(index, taskID, false, value), (err) => settleIfCurrent(index, taskID, true, err));
        processed++;
      } catch (err) {
        settleIfCurrent(index, taskID, true, err);
        processed++;
      }
    }
    if (hasPending()) {
      if (fromMicro) {
        scheduleMacro();
      } else {
        post2(null);
      }
      return;
    }
    if (!fromMicro) {
      isInMacro = false;
    }
  }
  function runMicroLoop() {
    if (!isInMicro)
      return;
    processLoop(true);
    isInMicro = false;
  }
  function cleanup(index) {
    working--;
    stateByIndex[index] = SlotStateMacro.Free;
    fnByIndex[index] = 0;
    taskIdByIndex[index] = -1;
    argsByIndex[index] = undefined;
    deferredByIndex[index] = undefined;
    freeStack[freeTop++] = index;
    if (working === 0)
      isInMacro = false;
  }
  const call = ({ fnNumber }) => (args) => {
    const taskID = genTaskID2();
    const deferred = withResolvers();
    const index = allocIndex();
    taskIdByIndex[index] = taskID;
    argsByIndex[index] = args;
    fnByIndex[index] = fnNumber | 0;
    deferredByIndex[index] = deferred;
    stateByIndex[index] = SlotStateMacro.Pending;
    working++;
    if (args instanceof Promise) {
      args.then((value) => {
        if (taskIdByIndex[index] !== taskID)
          return;
        argsByIndex[index] = value;
        enqueueIfCurrent(index, taskID);
      }, (err) => settleIfCurrent(index, taskID, true, err));
    } else {
      enqueue(index);
    }
    return deferred.promise;
  };
  port1.onmessage = () => processLoop(false);
  return {
    kills: async () => {
      for (let index = 0;index < stateByIndex.length; index++) {
        if (stateByIndex[index] !== SlotStateMacro.Pending)
          continue;
        try {
          deferredByIndex[index]?.reject("Thread closed");
        } catch {}
      }
      port1.onmessage = null;
      port1.close?.();
      port2.onmessage = null;
      port2.close?.();
      pendingQueue.clear();
      freeTop = 0;
      freeStack.length = 0;
      argsByIndex.fill(undefined);
      taskIdByIndex.fill(-1);
      deferredByIndex.fill(undefined);
      fnByIndex.fill(0);
      stateByIndex.fill(SlotStateMacro.Free);
      working = 0;
      isInMacro = false;
      isInMicro = false;
    },
    call,
    txIdle: () => working === 0
  };
};

// src/api.ts
var hasDebugNamespace = (namespaces, namespace) => namespaces.has("*") || namespaces.has(namespace);
var createHostDebug = (namespaces) => {
  const enabled = (namespace) => hasDebugNamespace(namespaces, namespace);
  if (!enabled("host"))
    return;
  const base = performance.now();
  const tag = `host·${RUNTIME}`;
  const log = (message) => {
    const elapsed = (performance.now() - base).toFixed(1);
    console.error(`[${tag}·+${elapsed}ms] host: ${message}`);
  };
  return { log };
};
var readHostCwd = () => {
  const denoCwd = globalThis.Deno?.cwd;
  if (typeof denoCwd === "function") {
    try {
      return denoCwd();
    } catch {}
  }
  const nodeProcess4 = getNodeProcess();
  if (typeof nodeProcess4?.cwd === "function") {
    try {
      return nodeProcess4.cwd();
    } catch {
      return;
    }
  }
  return;
};
var formatDebugList = (values, empty = "(none)") => values && values.length > 0 ? values.join(",") : empty;
var MAX_FUNCTION_ID = 65535;
var MAX_FUNCTION_COUNT = MAX_FUNCTION_ID + 1;
var DEFAULT_IMPORT_EXPORT_NAME = "default";
var isMain = RUNTIME_IS_MAIN_THREAD;
var toListAndIds = (args) => {
  const result = args.reduce((acc, v) => (acc[0].add(v.importedFrom), acc[1].add(v.id), acc[2].add(v.at), acc[3].push(v.name), acc), [
    new Set,
    new Set,
    new Set,
    []
  ]);
  return {
    list: [...result[0]],
    ids: [...result[1]],
    at: [...result[2]],
    names: result[3]
  };
};
var resolveImportHref = (href, callerHref) => {
  try {
    return new URL(href, callerHref).href;
  } catch {
    return toModuleUrl(href);
  }
};
var resolveWorkerSettings = (worker, callerHref) => {
  if (worker === undefined)
    return;
  const usingPorffor = worker.processRuntime === "porffor";
  if (usingPorffor && worker.runtime !== undefined && worker.runtime !== "compiled") {
    throw new Error('worker.processRuntime "porffor" requires worker.runtime to be compiled or omitted');
  }
  const forcePorfforBuild = usingPorffor && worker.runtime === undefined;
  let resolved = usingPorffor ? {
    ...worker,
    runtime: "compiled",
    processRuntime: undefined,
    compiled: forcePorfforBuild ? { ...worker.compiled, build: "always" } : worker.compiled
  } : worker;
  const bootstrap = resolved.bootstrap;
  if (bootstrap !== undefined) {
    const name = bootstrap.name ?? DEFAULT_IMPORT_EXPORT_NAME;
    if (typeof bootstrap.href !== "string" || bootstrap.href.length === 0) {
      throw new TypeError("worker.bootstrap.href must be a non-empty string");
    }
    if (typeof name !== "string" || name.length === 0) {
      throw new TypeError("worker.bootstrap.name must be a non-empty string");
    }
    resolved = {
      ...resolved,
      bootstrap: {
        ...bootstrap,
        href: resolveImportHref(bootstrap.href, callerHref),
        name
      }
    };
  }
  const compiled = resolved.compiled;
  if (compiled !== undefined) {
    if (compiled.build !== undefined && typeof compiled.build !== "boolean" && compiled.build !== "always") {
      throw new TypeError('worker.compiled.build must be a boolean or "always"');
    }
    for (const [name, value] of Object.entries({
      artifact: compiled.artifact,
      manifest: compiled.manifest,
      compiler: compiled.compiler
    })) {
      if (value !== undefined && (typeof value !== "string" || value.length === 0)) {
        throw new TypeError("worker.compiled." + name + " must be a non-empty string");
      }
    }
    resolved = {
      ...resolved,
      compiled: {
        build: compiled.build,
        compiler: compiled.compiler === undefined ? undefined : compiled.compiler.startsWith(".") || compiled.compiler.startsWith("/") || compiled.compiler.startsWith("file:") || /^[A-Za-z]:[\\/]/.test(compiled.compiler) ? resolveImportHref(compiled.compiler, callerHref) : compiled.compiler,
        artifact: compiled.artifact === undefined ? undefined : resolveImportHref(compiled.artifact, callerHref),
        manifest: compiled.manifest === undefined ? undefined : resolveImportHref(compiled.manifest, callerHref)
      }
    };
  }
  return resolved;
};
var isTaskDefinition = (value) => value != null && typeof value === "object" && typeof value.f === "function";
var toPoolTaskEntries = (input, callerHref) => Object.entries(input).map(([name, value]) => {
  if (isTaskDefinition(value)) {
    return {
      ...value,
      name
    };
  }
  if (typeof value === "function") {
    return {
      f: value,
      id: -1,
      importedFrom: new URL(callerHref).href,
      at: -1,
      name,
      [endpointSymbol]: true
    };
  }
  throw new TypeError(`createPool task "${name}" must be a task definition or exported function`);
});
var createPool = ({
  threads,
  debug,
  inliner,
  balancer,
  payload,
  unsafe,
  abortSignalCapacity,
  source,
  worker,
  workerExecArgv,
  permission,
  host
}) => (tasks) => {
  const bufferReferenceReturn = unsafe?.BufferReferenceReturn;
  const debugRequested = DEBUG_ENABLED || debug !== undefined && debug !== false;
  let debugNamespaces;
  const getDebugNamespaces = () => debugNamespaces ??= resolveDebugNamespaces(debug);
  const hostDebug = debugRequested ? createHostDebug(getDebugNamespaces()) : undefined;
  const debugEnabled = (namespace) => debugRequested && hasDebugNamespace(getDebugNamespaces(), namespace);
  if (RUNTIME_IS_MAIN_THREAD === false) {
    if (debugEnabled("lifecycle")) {
      console.warn("createPool has been called with : " + JSON.stringify(RUNTIME_WORKER_DATA));
    }
    const notMainThreadError = () => {
      throw new Error("createPool can only be called in the main thread.");
    };
    const throwingProxyTarget = function() {
      return notMainThreadError();
    };
    const throwingProxyHandler = {
      get: function() {
        return notMainThreadError;
      }
    };
    const mainThreadOnlyProxy = new Proxy(throwingProxyTarget, throwingProxyHandler);
    return {
      shutdown: mainThreadOnlyProxy,
      [Symbol.dispose]: () => {},
      call: mainThreadOnlyProxy
    };
  }
  const callerHref = getCallerHref(3);
  const listOfFunctions = toPoolTaskEntries(tasks, callerHref).sort((a, b) => a.name.localeCompare(b.name));
  const { list, ids, names, at } = toListAndIds(listOfFunctions);
  hostDebug?.log(`cwd=${readHostCwd() ?? "(unknown)"} caller=${callerHref}`);
  listOfFunctions.forEach((fn) => {
    hostDebug?.log(`task name=${fn.name} id=${fn.id} from=${fn.importedFrom}`);
  });
  if (listOfFunctions.length > MAX_FUNCTION_COUNT) {
    throw new RangeError(`Too many tasks: received ${listOfFunctions.length}. ` + `Maximum is ${MAX_FUNCTION_COUNT} (Uint16 function IDs: 0..${MAX_FUNCTION_ID}).`);
  }
  const usingInliner = typeof inliner === "object" && inliner != null;
  const totalNumberOfThread = (threads ?? 1) + (usingInliner ? 1 : 0);
  const permissionProtocol = resolvePermissionProtocol({
    permission: permission ?? {
      mode: "strict",
      allowImport: true
    },
    modules: list
  });
  const permissionExecArgv = toRuntimePermissionFlags(permissionProtocol);
  const nodeProcess4 = getNodeProcess();
  const allowedFlags = nodeProcess4?.allowedNodeEnvironmentFlags ?? null;
  const isNodePermissionFlag = (flag) => {
    const key = flag.split("=", 1)[0];
    return key === "--permission" || key === "--experimental-permission" || key === "--allow-fs-read" || key === "--allow-fs-write" || key === "--allow-worker" || key === "--allow-child-process" || key === "--allow-net" || key === "--allow-addons" || key === "--allow-ffi" || key === "--allow-wasi";
  };
  const stripNodePermissionFlags = (flags) => flags?.filter((flag) => !isNodePermissionFlag(flag));
  const dedupeFlags = (flags) => {
    const out = [];
    const seen = new Set;
    for (const flag of flags) {
      if (seen.has(flag))
        continue;
      seen.add(flag);
      out.push(flag);
    }
    return out;
  };
  const sanitizeExecArgv = (flags) => {
    if (!flags || flags.length === 0)
      return;
    if (!allowedFlags)
      return flags;
    const filtered = flags.filter((flag) => {
      const key = flag.split("=", 1)[0];
      return allowedFlags.has(key);
    });
    return filtered.length > 0 ? filtered : undefined;
  };
  const inheritedExecArgv = Array.isArray(nodeProcess4?.execArgv) ? nodeProcess4.execArgv : undefined;
  const defaultExecArgvCandidate = workerExecArgv ?? (inheritedExecArgv ? allowedFlags?.has("--expose-gc") === true ? inheritedExecArgv.includes("--expose-gc") ? inheritedExecArgv : [...inheritedExecArgv, "--expose-gc"] : inheritedExecArgv : undefined);
  const defaultExecArgv = permissionProtocol?.unsafe === true ? stripNodePermissionFlags(defaultExecArgvCandidate) : defaultExecArgvCandidate;
  const combinedExecArgv = dedupeFlags([
    ...permissionExecArgv,
    ...defaultExecArgv ?? []
  ]);
  const execArgv = sanitizeExecArgv(combinedExecArgv.length > 0 ? combinedExecArgv : undefined);
  hostDebug?.log(`pool runtime=${RUNTIME} workers=${threads ?? 1}` + ` lanes=${totalNumberOfThread} inliner=${usingInliner ? "on" : "off"}`);
  hostDebug?.log(`modules=${formatDebugList(list)}`);
  hostDebug?.log(`permission=${permissionProtocol?.mode ?? "off"} execArgv=${formatDebugList(execArgv)}`);
  const usesAbortSignal = listOfFunctions.some((fn) => fn.abortSignal !== undefined);
  const resolvedWorker = resolveWorkerSettings(worker, callerHref);
  const dispatcherEnv = nodeProcess4?.env?.KNITTING_DISPATCHER;
  const stealEnvRaw = nodeProcess4?.env?.KNITTING_STEAL?.trim().toLowerCase();
  const stealEnv = stealEnvRaw === "1" || stealEnvRaw === "true" ? true : stealEnvRaw === "0" || stealEnvRaw === "false" ? false : undefined;
  const dispatcherExplicitlySelected = host?.dispatcher !== undefined || dispatcherEnv === "serial-channel" || dispatcherEnv === "per-thread";
  const stealDefaultCompatible = balancer === undefined && !dispatcherExplicitlySelected && (threads ?? 1) <= MAX_STEAL_CONSUMERS;
  const stealRequested = host?.steal ?? stealEnv ?? stealDefaultCompatible;
  const usingCompiledWorker = resolvedWorker?.runtime === "compiled";
  if (resolvedWorker?.compiled !== undefined && !usingCompiledWorker) {
    throw new Error("worker.compiled requires worker.runtime to be compiled");
  }
  if (usingCompiledWorker) {
    const unsupported = [];
    if (usingInliner)
      unsupported.push("inliner");
    if (payload !== undefined)
      unsupported.push("payload");
    if (unsafe !== undefined)
      unsupported.push("unsafe");
    if (source !== undefined)
      unsupported.push("source");
    if (workerExecArgv !== undefined)
      unsupported.push("workerExecArgv");
    if (permission !== undefined)
      unsupported.push("permission");
    if (host !== undefined)
      unsupported.push("host");
    if (resolvedWorker.bootstrap !== undefined) {
      unsupported.push("worker.bootstrap");
    }
    if (resolvedWorker.timers !== undefined)
      unsupported.push("worker.timers");
    if (resolvedWorker.processRuntime !== undefined) {
      unsupported.push("worker.processRuntime");
    }
    if (resolvedWorker.processCommandPrefix !== undefined) {
      unsupported.push("worker.processCommandPrefix");
    }
    if (resolvedWorker.processSharedMemory !== undefined) {
      unsupported.push("worker.processSharedMemory");
    }
    if (resolvedWorker.resolveAfterFinishingAll !== undefined) {
      unsupported.push("worker.resolveAfterFinishingAll");
    }
    if (listOfFunctions.some((fn) => fn.timeout !== undefined)) {
      unsupported.push("task timeout");
    }
    if (listOfFunctions.some((fn) => fn.imported === true)) {
      unsupported.push("importTask");
    }
    if (unsupported.length > 0) {
      throw new Error("Compiled workers do not support: " + unsupported.join(", "));
    }
  }
  if (resolvedWorker?.bootstrap !== undefined) {
    hostDebug?.log(`bootstrap href=${resolvedWorker.bootstrap.href}` + ` name=${resolvedWorker.bootstrap.name}`);
  }
  if (usingInliner && resolvedWorker?.bootstrap !== undefined) {
    throw new Error("worker.bootstrap cannot be used with the inliner");
  }
  if (resolvedWorker?.runtime === "process") {
    const processRuntime = readProcessWorkerRuntime(resolvedWorker);
    enforceProcessPermissionCompatibility(classifyProcessPermissionCompatibility({
      permission,
      resolved: permissionProtocol,
      target: {
        runtime: processRuntime,
        nodeMajor: processRuntime === "node" ? readProcessWorkerNodeMajor(resolvedWorker) : undefined
      }
    }));
  }
  const hardTimeoutMs = Number.isFinite(resolvedWorker?.hardTimeoutMs) ? Math.max(1, Math.floor(resolvedWorker?.hardTimeoutMs)) : undefined;
  if (RUNTIME_POOL_DEPTH >= 1) {
    throw new Error(`createPool() tried to spawn workers from inside a worker process ` + `(pool depth ${RUNTIME_POOL_DEPTH}). This usually means a pool is ` + `created at module scope in a module your workers import, so every ` + `worker spawns its own pool recursively. Is your createPool protected ` + `by isMain? Guard pool creation behind \`if (isMain) { ... }\` ` + `(import { isMain } from "knitting") so only the main program starts ` + `the pool.`);
  }
  const explicitDispatcher = host?.dispatcher ?? (dispatcherEnv === "serial-channel" || dispatcherEnv === "per-thread" ? dispatcherEnv : undefined);
  const autoDispatcher = (() => {
    if (RUNTIME === "bun")
      return "per-thread";
    if ((threads ?? 1) <= 1)
      return "per-thread";
    return "serial-channel";
  })();
  const dispatcher = explicitDispatcher ?? autoDispatcher;
  const useSteal = stealRequested && !usingCompiledWorker && (threads ?? 1) > 1 && !usingInliner;
  const stealBuffers = useSteal ? createStealPoolBuffers({
    threads: threads ?? 1,
    payload,
    regionLanes: host?.stealRegionLanes,
    abortSignalCapacity,
    usesAbortSignal,
    processWorker: resolvedWorker?.runtime === "process" ? {
      signalBytes: TRANSPORT_SIGNAL_BYTES,
      sharedMemory: readProcessSharedMemorySettings(resolvedWorker)
    } : undefined
  }) : undefined;
  const serialChannel = !usingCompiledWorker && !useSteal && dispatcher === "serial-channel";
  const serialDispatcherChannel = serialChannel ? new ChannelHandler("channel") : undefined;
  let workers = Array.from({
    length: threads ?? 1
  }).map((_, thread) => spawnWorkerContext({
    list,
    ids,
    names,
    at,
    thread,
    debug,
    hostDebug: hostDebug?.log,
    totalNumberOfThread,
    source,
    workerOptions: resolvedWorker,
    workerExecArgv: execArgv,
    host,
    payload,
    bufferReferenceReturn,
    abortSignalCapacity,
    usesAbortSignal,
    permission: permissionProtocol,
    sharedChannelHandler: serialDispatcherChannel,
    stealPool: stealBuffers === undefined ? undefined : {
      submitBuffers: stealBuffers.submitBuffers,
      returnBuffers: stealBuffers.returnBuffers[thread],
      hostSubmitLock: stealBuffers.hostSubmitLock,
      hostReturnLock: stealBuffers.hostReturnLocks[thread],
      sharedQueue: stealBuffers.sharedQueue,
      consumers: threads ?? 1,
      consumerId: thread,
      regionLanes: stealBuffers.regionLanes,
      abortSignalSAB: stealBuffers.abortSignalSAB,
      abortSignalMax: stealBuffers.abortSignalMax,
      processMemory: stealBuffers.processMemory
    }
  }));
  const stealChannel = useSteal ? new ChannelHandler : undefined;
  if (useSteal) {
    const channel = stealChannel;
    const queue = stealBuffers.sharedQueue;
    let wakeCursor = 0;
    const wakeOne = () => {
      const lanes = workers.length;
      if (lanes === 0)
        return;
      const lane = wakeCursor;
      wakeCursor = wakeCursor + 1 < lanes ? wakeCursor + 1 : 0;
      workers[lane].laneWake?.();
    };
    const signalWords = new Int32Array(createSharedArrayBuffer(3 * Int32Array.BYTES_PER_ELEMENT));
    const { check } = hostDispatcherLoop({
      signalBox: {
        opView: signalWords.subarray(0, 1),
        txStatus: signalWords.subarray(1, 2),
        rxStatus: signalWords.subarray(2, 3)
      },
      queue,
      channelHandler: channel,
      dispatcherOptions: host,
      notifySignal: wakeOne,
      crossProcess: resolvedWorker?.runtime === "process"
    });
    channel.open(check);
    workers.forEach((context) => {
      context.bindSend(() => {
        if (check.isRunning !== true) {
          check.isRunning = true;
          Promise.resolve().then(check);
        }
        wakeOne();
      });
    });
    hostDebug?.log(`dispatcher=steal lanes=${workers.length} g=${stealBuffers.regionLanes}`);
  }
  const sharedDispatcherChannel = serialDispatcherChannel;
  if (serialChannel) {
    const channel = serialDispatcherChannel;
    const checks = workers.map((context) => context.dispatcherCheck);
    const laneIdle = workers.map((context) => context.txIdle);
    let serialScheduled = false;
    let serialInFlight = false;
    let serialRerun = false;
    const active = [];
    const isActive = new Uint8Array(checks.length);
    const markActive = (lane) => {
      if (isActive[lane] === 1)
        return;
      isActive[lane] = 1;
      active.push(lane);
    };
    const runSerialChecks = () => {
      if (serialInFlight) {
        serialRerun = true;
        return;
      }
      serialInFlight = true;
      do {
        serialRerun = false;
        serialScheduled = false;
        for (let index = active.length - 1;index >= 0; index--) {
          const lane = active[index];
          const check = checks[lane];
          if (check.isRunning !== true)
            check.isRunning = true;
          check();
          if (laneIdle[lane]()) {
            isActive[lane] = 0;
            const last = active.pop();
            if (index < active.length)
              active[index] = last;
          }
        }
      } while (serialRerun);
      serialInFlight = false;
    };
    const scheduleSerialCheck = () => {
      if (serialInFlight) {
        serialRerun = true;
        return;
      }
      if (serialScheduled)
        return;
      serialScheduled = true;
      Promise.resolve().then(runSerialChecks);
    };
    channel.open(runSerialChecks);
    workers.forEach((context, lane) => {
      const wake = context.laneWake;
      context.bindSend(() => {
        markActive(lane);
        scheduleSerialCheck();
        wake();
      });
    });
    hostDebug?.log(`dispatcher=serial-channel lanes=${checks.length}`);
  } else {
    hostDebug?.log(`dispatcher=per-thread lanes=${workers.length}`);
  }
  if (usingInliner) {
    const mainThread = createInlineExecutor({
      tasks: listOfFunctions,
      genTaskID,
      batchSize: inliner?.batchSize ?? 1
    });
    if (inliner?.position === "first") {
      workers = [
        mainThread,
        ...workers
      ];
    } else {
      workers.push(mainThread);
    }
  }
  const inlinerIndex = usingInliner ? inliner?.position === "first" ? 0 : workers.length - 1 : -1;
  const inlinerDispatchThreshold = Number.isFinite(inliner?.dispatchThreshold) ? Math.max(1, Math.floor(inliner?.dispatchThreshold ?? 1)) : 1;
  let closing = false;
  let closePromise;
  let shutdownPromise;
  const closePoolNow = () => {
    if (closePromise)
      return closePromise;
    closing = true;
    closePromise = Promise.allSettled(workers.map((context) => context.kills())).then(() => {
      sharedDispatcherChannel?.close();
      stealChannel?.close();
    });
    return closePromise;
  };
  const wrapGuardedInvoke = ({
    invoke,
    taskName
  }) => (args) => {
    if (closing) {
      return Promise.reject(new Error("Pool is shut down"));
    }
    const pending = invoke(args);
    if (!hardTimeoutMs)
      return pending;
    return new Promise((resolve, reject) => {
      let settled = false;
      const timeoutId = setTimeout(() => {
        if (settled)
          return;
        settled = true;
        reject(new Error(`Task hard timeout after ${hardTimeoutMs}ms (${taskName}); pool force-shutdown`));
        closePoolNow();
      }, hardTimeoutMs);
      pending.then((value) => {
        if (settled)
          return;
        settled = true;
        clearTimeout(timeoutId);
        resolve(value);
      }, (error) => {
        if (settled)
          return;
        settled = true;
        clearTimeout(timeoutId);
        reject(error);
      });
    });
  };
  const shutdownWithDelay = (delayMs) => {
    if (closePromise)
      return closePromise;
    if (shutdownPromise)
      return shutdownPromise;
    const ms = Number.isFinite(delayMs) ? Math.max(0, Math.floor(delayMs)) : 0;
    shutdownPromise = (async () => {
      if (closePromise)
        return await closePromise;
      if (ms > 0) {
        await new Promise((resolve) => setTimeout(resolve, ms));
      }
      if (closePromise)
        return await closePromise;
      await closePoolNow();
    })();
    return shutdownPromise;
  };
  const disposePool = () => {
    shutdownWithDelay();
  };
  const indexedFunctions = listOfFunctions.map((fn, index) => ({
    name: fn.name,
    index,
    timeout: fn.timeout,
    abortSignal: fn.abortSignal,
    imported: fn.imported === true
  }));
  const callHandlers = new Map;
  for (const { name } of indexedFunctions) {
    callHandlers.set(name, []);
  }
  for (const worker2 of workers) {
    for (const { name, index, timeout, abortSignal } of indexedFunctions) {
      callHandlers.get(name).push(wrapGuardedInvoke({
        taskName: name,
        invoke: worker2.call({
          fnNumber: index,
          timeout,
          abortSignal
        })
      }));
    }
  }
  const useDirectHandler = (threads ?? 1) === 1 && !usingInliner;
  const buildImportedInvoker = (handlers) => {
    const workerHandlers = [];
    const workerContexts = [];
    for (let lane = 0;lane < handlers.length; lane += 1) {
      if (lane === inlinerIndex)
        continue;
      workerHandlers.push(handlers[lane]);
      workerContexts.push(workers[lane]);
    }
    if (workerHandlers.length === 0) {
      throw new Error("Imported task has no worker lane to run on: the pool only has the " + "host inliner. Imported tasks are never inlined on the host; add at " + "least one worker thread.");
    }
    if (workerHandlers.length === 1)
      return workerHandlers[0];
    return managerMethod({
      contexts: workerContexts,
      balancer,
      handlers: workerHandlers
    });
  };
  const buildInvoker = (handlers, imported) => {
    if (imported && usingInliner) {
      return buildImportedInvoker(handlers);
    }
    return useDirectHandler ? handlers[0] : managerMethod({
      contexts: workers,
      balancer,
      handlers,
      inlinerGate: usingInliner ? {
        index: inlinerIndex,
        threshold: inlinerDispatchThreshold
      } : undefined
    });
  };
  let callEntries;
  try {
    callEntries = indexedFunctions.map(({ name, imported }) => [name, buildInvoker(callHandlers.get(name), imported)]);
  } catch (error) {
    closePoolNow();
    throw error;
  }
  return {
    shutdown: shutdownWithDelay,
    [Symbol.dispose]: disposePool,
    call: Object.fromEntries(callEntries)
  };
};
var SINGLE_TASK_KEY = "__task__";
var createSingleTaskPool = (single, options) => {
  const pool = createPool(options ?? {})({
    [SINGLE_TASK_KEY]: single
  });
  return {
    call: pool.call[SINGLE_TASK_KEY],
    shutdown: pool.shutdown,
    [Symbol.dispose]: pool[Symbol.dispose]
  };
};
var buildTaskDefinitionFromCaller = (input, callerHref, at, imported = false) => {
  const importedFrom = new URL(callerHref).href;
  const out = {
    ...input,
    id: stableTaskID(importedFrom, at),
    importedFrom,
    at,
    imported,
    [endpointSymbol]: true
  };
  out.createPool = (options) => {
    if (RUNTIME_IS_MAIN_THREAD === false) {
      return out;
    }
    return createSingleTaskPool(out, options);
  };
  return out;
};
var buildTaskDefinition = (input, callerOffset) => {
  const [href, at] = getCallerFilePath(callerOffset);
  return buildTaskDefinitionFromCaller(input, href, at);
};
var createImportedTaskFn = (href, exportName) => {
  let cachedFn;
  let cachedLoad;
  const loadFn = async () => {
    if (cachedFn)
      return cachedFn;
    if (!cachedLoad) {
      cachedLoad = import(href).then((module) => {
        const record = module;
        const selected = exportName === DEFAULT_IMPORT_EXPORT_NAME ? record.default : record[exportName];
        if (typeof selected !== "function") {
          const available = Object.keys(record).join(", ");
          throw new TypeError(`importTask expected export "${exportName}" from "${href}" to be a function. Available exports: ${available || "(none)"}`);
        }
        cachedFn = selected;
        return cachedFn;
      });
    }
    return cachedLoad;
  };
  return async (...args) => {
    const fn = await loadFn();
    return fn(...args);
  };
};
function task(I) {
  return buildTaskDefinition(I, 4);
}
function importTask(options) {
  const [callerHref, at] = getCallerFilePath(3);
  const {
    href,
    name = DEFAULT_IMPORT_EXPORT_NAME,
    ...rest
  } = options;
  const resolvedHref = resolveImportHref(href, callerHref);
  return buildTaskDefinitionFromCaller({
    ...rest,
    f: createImportedTaskFn(resolvedHref, name)
  }, callerHref, at, true);
}
export {
  Envelope,
  NumericArray,
  createPool,
  importTask,
  isMain,
  isNumericArray,
  setModuleUrl,
  task,
  workerMainLoop
};
