// src/worker/loop.ts
import {
  isMainThread as isMainThread2,
  workerData,
  MessageChannel,
  parentPort
} from "node:worker_threads";

// src/ipc/tools/RingQueue.ts
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

// src/memory/regionRegistry.ts
var SLOT_META_PACKED_MASK = 4294967264;
var register = ({ lockSector }) => {
  const lockSAB = lockSector ?? new SharedArrayBuffer(LOCK_SECTOR_BYTE_LENGTH);
  const hostBits = new Int32Array(lockSAB, PAYLOAD_LOCK_HOST_BITS_OFFSET_BYTES, 1);
  const workerBits = new Int32Array(lockSAB, PAYLOAD_LOCK_WORKER_BITS_OFFSET_BYTES, 1);
  const startAndIndex = new Uint32Array(32 /* slots */);
  const size64bit = new Uint32Array(32 /* slots */);
  const clz32 = Math.clz32;
  const EMPTY = 4294967295 >>> 0;
  const SLOT_MASK = TASK_SLOT_INDEX_MASK;
  const START_MASK = ~SLOT_MASK >>> 0;
  startAndIndex.fill(EMPTY);
  let tableLength = 0;
  let usedBits = 0 | 0;
  let hostLast = 0 | 0;
  let workerLast = 0 | 0;
  let updateTableCounter = 0;
  const startAndIndexToArray = (length) => Array.from(startAndIndex.subarray(0, length));
  const updateTable = () => {
    const w = Atomics.load(workerBits, 0) | 0;
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
    const sai = startAndIndex;
    let nextLength = 0 | 0;
    for (let i = 0;i < tableLength; i++) {
      const v = sai[i];
      if (v === EMPTY)
        continue;
      if ((freeBits & 1 << (v & SLOT_MASK)) !== 0)
        continue;
      sai[nextLength++] = v;
    }
    usedBits &= ~freeBits;
    tableLength = nextLength;
  };
  const findAndInsert = (task, size) => {
    const freeBits = ~usedBits >>> 0;
    const freeBit = (freeBits & -freeBits) >>> 0;
    if (freeBit === 0)
      return -1;
    const tl = tableLength;
    if (tl >= 32 /* slots */)
      return -1;
    const slotIndex = 31 - clz32(freeBit);
    const sai = startAndIndex;
    const sz = size64bit;
    if (tl === 0) {
      sai[0] = slotIndex;
      sz[slotIndex] = size;
      task[3 /* Start */] = 0;
      task[6 /* slotBuffer */] = (task[6 /* slotBuffer */] & SLOT_META_PACKED_MASK | slotIndex) >>> 0;
      tableLength = 1;
      usedBits |= freeBit;
      hostLast ^= freeBit;
      return slotIndex;
    }
    const firstStart = sai[0] & START_MASK;
    if (firstStart >= size >>> 0) {
      sai.copyWithin(1, 0, tl);
      sai[0] = slotIndex;
      sz[slotIndex] = size;
      task[3 /* Start */] = 0;
      task[6 /* slotBuffer */] = (task[6 /* slotBuffer */] & SLOT_META_PACKED_MASK | slotIndex) >>> 0;
      tableLength = tl + 1;
      usedBits |= freeBit;
      hostLast ^= freeBit;
      return slotIndex;
    }
    let prevEnd = firstStart + (sz[sai[0] & SLOT_MASK] >>> 0) >>> 0;
    for (let at = 0;at + 1 < tl; at++) {
      const next = sai[at + 1];
      const nextStart = next & START_MASK;
      if (nextStart - prevEnd >>> 0 < size >>> 0) {
        prevEnd = nextStart + (sz[next & SLOT_MASK] >>> 0) >>> 0;
        continue;
      }
      sai.copyWithin(at + 2, at + 1, tl);
      sai[at + 1] = (prevEnd | slotIndex) >>> 0;
      sz[slotIndex] = size;
      task[3 /* Start */] = prevEnd;
      task[6 /* slotBuffer */] = (task[6 /* slotBuffer */] & SLOT_META_PACKED_MASK | slotIndex) >>> 0;
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
    task[3 /* Start */] = newStart;
    task[6 /* slotBuffer */] = (task[6 /* slotBuffer */] & SLOT_META_PACKED_MASK | slotIndex) >>> 0;
    tableLength = tl + 1;
    usedBits |= freeBit;
    hostLast ^= freeBit;
    return slotIndex;
  };
  const allocTask = (task) => {
    updateTable();
    const payloadLen = task[5 /* PayloadLen */] | 0;
    const size = payloadLen + 63 & ~63;
    const slotIndex = findAndInsert(task, size);
    if (slotIndex === -1)
      return -1;
    Atomics.store(hostBits, 0, hostLast);
    return slotIndex;
  };
  const setSlotLength = (slotIndex, payloadLen) => {
    slotIndex = slotIndex & TASK_SLOT_INDEX_MASK;
    const bit = 1 << slotIndex;
    if ((usedBits & bit) === 0)
      return false;
    const current = size64bit[slotIndex] >>> 0;
    const aligned = (payloadLen | 0) + 63 & ~63;
    if (aligned < 0)
      return false;
    if (aligned >>> 0 > current)
      return false;
    size64bit[slotIndex] = aligned >>> 0;
    return true;
  };
  const free = (index) => {
    index = index & TASK_SLOT_INDEX_MASK;
    workerLast ^= 1 << index;
    Atomics.store(workerBits, 0, workerLast);
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

// src/memory/createSharedBufferIO.ts
import { Buffer as NodeBuffer } from "node:buffer";

// src/common/runtime.ts
var globals = globalThis;
var IS_DENO = typeof globals.Deno?.version?.deno === "string";
var IS_BUN = typeof globals.Bun?.version === "string";
var IS_NODE = typeof process !== "undefined" && typeof process.versions?.node === "string";
var RUNTIME = IS_DENO ? "deno" : IS_BUN ? "bun" : IS_NODE ? "node" : "unknown";
var SET_IMMEDIATE = typeof globals.setImmediate === "function" ? globals.setImmediate : undefined;
var WASM_MEMORY_PAGE_BYTES = 64 * 1024;
var wasmSharedBufferMemory = new WeakMap;
var wasmSharedBufferMaxByteLength = new WeakMap;
var hasSharedWasmMemory = (() => {
  if (typeof WebAssembly?.Memory !== "function")
    return false;
  try {
    new WebAssembly.Memory({ initial: 0, maximum: 1, shared: true });
    return true;
  } catch {
    return false;
  }
})();
var roundupWasmPages = (byteLength) => Math.ceil(Math.max(0, byteLength) / WASM_MEMORY_PAGE_BYTES);
var createSharedWasmBuffer = (byteLength, maxByteLength) => {
  const memory = new WebAssembly.Memory({
    initial: roundupWasmPages(byteLength),
    maximum: Math.max(roundupWasmPages(byteLength), roundupWasmPages(maxByteLength)),
    shared: true
  });
  const buffer = memory.buffer;
  wasmSharedBufferMemory.set(buffer, memory);
  wasmSharedBufferMaxByteLength.set(buffer, maxByteLength);
  return buffer;
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
  return HAS_SAB_GROW && isGrowableSharedArrayBuffer(sab);
};
var sharedBufferMaxByteLength = (sab) => {
  if (sab == null)
    return;
  return toPositiveInteger(sharedArrayBufferMaxByteLength(sab));
};
var resolvePayloadBufferOptions = ({
  options,
  sab
}) => {
  const requestedMode = options?.mode;
  const modeDefault = HAS_SAB_GROW ? "growable" : "fixed";
  let mode = requestedMode ?? modeDefault;
  if (mode === "growable" && sab != null && !canGrowSharedBuffer(sab)) {
    mode = "fixed";
  }
  if (mode === "growable" && !HAS_SAB_GROW) {
    mode = "fixed";
  }
  const payloadMaxByteLength = toPositiveInteger(options?.payloadMaxByteLength) ?? sharedBufferMaxByteLength(sab) ?? PAYLOAD_DEFAULT_MAX_BYTE_LENGTH;
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

// src/memory/createSharedBufferIO.ts
var page = 1024 * 4;
var textEncode = new TextEncoder;
var DYNAMIC_HEADER_BYTES = 64;
var DYNAMIC_SAFE_PADDING_BYTES = page;
var alignUpto64 = (n) => n + (64 - 1) & ~(64 - 1);
var canonicalDynamicUint8Array = (src) => src.constructor === Uint8Array ? src : new Uint8Array(src.buffer, src.byteOffset, src.byteLength);
var createSharedDynamicBufferIO = ({
  sab,
  payloadConfig
}) => {
  const resolvedPayload = resolvePayloadBufferOptions({
    sab,
    options: payloadConfig
  });
  const canGrow = resolvedPayload.mode === "growable";
  let lockSAB = sab ?? (canGrow ? createSharedArrayBuffer(resolvedPayload.payloadInitialBytes, resolvedPayload.payloadMaxByteLength) : createSharedArrayBuffer(resolvedPayload.payloadInitialBytes));
  let u8 = new Uint8Array(lockSAB, DYNAMIC_HEADER_BYTES);
  const requireBufferView = (buffer) => {
    const view = NodeBuffer.from(buffer, DYNAMIC_HEADER_BYTES);
    if (view.buffer !== buffer) {
      throw new Error("Buffer view does not alias SharedArrayBuffer");
    }
    return view;
  };
  let buf = requireBufferView(lockSAB);
  let f64 = new Float64Array(lockSAB, DYNAMIC_HEADER_BYTES);
  const capacityBytes = () => lockSAB.byteLength - DYNAMIC_HEADER_BYTES;
  const ensureCapacity = (neededBytes) => {
    if (capacityBytes() >= neededBytes)
      return true;
    if (!canGrow)
      return false;
    try {
      lockSAB = growSharedArrayBuffer(lockSAB, alignUpto64(DYNAMIC_HEADER_BYTES + neededBytes + DYNAMIC_SAFE_PADDING_BYTES));
    } catch {
      return false;
    }
    u8 = new Uint8Array(lockSAB, DYNAMIC_HEADER_BYTES, lockSAB.byteLength - DYNAMIC_HEADER_BYTES);
    buf = requireBufferView(lockSAB);
    f64 = new Float64Array(lockSAB, DYNAMIC_HEADER_BYTES, lockSAB.byteLength - DYNAMIC_HEADER_BYTES >>> 3);
    return true;
  };
  const readUtf8 = (start, end) => {
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
    const length = Math.max(0, end - start | 0);
    const out = NodeBuffer.allocUnsafe(length);
    if (length === 0)
      return out;
    buf.copy(out, 0, start, end);
    return out;
  };
  const readBytesArrayBufferCopy = (start, end) => {
    const length = Math.max(0, end - start | 0);
    if (length === 0)
      return new ArrayBuffer(0);
    const out = NodeBuffer.allocUnsafeSlow(length);
    buf.copy(out, 0, start, end);
    return out.buffer;
  };
  const read8BytesFloatCopy = (start, end) => f64.slice(start >>> 3, end >>> 3);
  const read8BytesFloatView = (start, end) => f64.subarray(start >>> 3, end >>> 3);
  const writeUtf8 = (str, start, reservedBytes = str.length * 3) => {
    if (!ensureCapacity(start + reservedBytes)) {
      return -1;
    }
    const { read, written } = textEncode.encodeInto(str, u8.subarray(start, start + reservedBytes));
    if (read !== str.length)
      return -1;
    return written;
  };
  return {
    readUtf8,
    writeBinary,
    write8Binary,
    readBytesCopy,
    readBytesView,
    readBytesBufferCopy,
    readBytesArrayBufferCopy,
    read8BytesFloatCopy,
    read8BytesFloatView,
    writeUtf8
  };
};
var createSharedStaticBufferIO = ({
  headersBuffer
}) => {
  const u32Bytes = Uint32Array.BYTES_PER_ELEMENT;
  const slotStride = 0 /* header */ + 144 /* TotalBuff */;
  const writableBytes = (144 /* TotalBuff */ - 8 /* Size */) * u32Bytes;
  const slotOffset = (at) => at * slotStride + 0 /* header */;
  const slotStartBytes = (at) => (slotOffset(at) + 8 /* Size */) * u32Bytes;
  const arrU8Sec = Array.from({
    length: 32 /* slots */
  }, (_, i) => new Uint8Array(headersBuffer, slotStartBytes(i), writableBytes));
  const arrBuffSec = Array.from({ length: 32 /* slots */ }, (_, i) => NodeBuffer.from(headersBuffer, slotStartBytes(i), writableBytes));
  const arrF64Sec = Array.from({
    length: 32 /* slots */
  }, (_, i) => new Float64Array(headersBuffer, slotStartBytes(i), writableBytes >>> 3));
  const canWrite = (start, length) => (start | 0) >= 0 && start + length <= writableBytes;
  const writeUtf8 = (str, at) => {
    const { read, written } = textEncode.encodeInto(str, arrU8Sec[at]);
    if (read !== str.length)
      return -1;
    return written;
  };
  const readUtf8 = (start, end, at) => {
    return arrBuffSec[at].toString("utf8", start, end);
  };
  const writeBinary = (src, at, start = 0) => {
    if (!canWrite(start, src.byteLength))
      return -1;
    arrU8Sec[at].set(src, start);
    return src.byteLength;
  };
  const write8Binary = (src, at, start = 0) => {
    const bytes = src.byteLength;
    if (!canWrite(start, bytes))
      return -1;
    arrF64Sec[at].set(src, start >>> 3);
    return bytes;
  };
  const readBytesCopy = (start, end, at) => arrU8Sec[at].slice(start, end);
  const readBytesView = (start, end, at) => arrU8Sec[at].subarray(start, end);
  const readBytesBufferCopy = (start, end, at) => {
    const length = Math.max(0, end - start | 0);
    const out = NodeBuffer.allocUnsafe(length);
    if (length === 0)
      return out;
    arrBuffSec[at].copy(out, 0, start, end);
    return out;
  };
  const readBytesArrayBufferCopy = (start, end, at) => {
    const length = Math.max(0, end - start | 0);
    if (length === 0)
      return new ArrayBuffer(0);
    const out = NodeBuffer.allocUnsafeSlow(length);
    arrBuffSec[at].copy(out, 0, start, end);
    return out.buffer;
  };
  const read8BytesFloatCopy = (start, end, at) => arrF64Sec[at].slice(start >>> 3, end >>> 3);
  const read8BytesFloatView = (start, end, at) => arrF64Sec[at].subarray(start >>> 3, end >>> 3);
  return {
    writeUtf8,
    readUtf8,
    writeBinary,
    write8Binary,
    readBytesCopy,
    readBytesView,
    readBytesBufferCopy,
    readBytesArrayBufferCopy,
    read8BytesFloatCopy,
    read8BytesFloatView,
    maxBytes: writableBytes
  };
};

// src/memory/payloadCodec.ts
import { Buffer as NodeBuffer2 } from "node:buffer";

// src/error.ts
import { isMainThread } from "node:worker_threads";
var promisePayloadMarker = Symbol.for("knitting.promise.payload");
var reasonFrom = (task, type, detail) => {
  switch (type) {
    case 0 /* Function */: {
      const name = typeof task.value === "function" ? task.value.name || "<anonymous>" : "<unknown>";
      return `KNT_ERROR_0: Function is not a valid type; name: ${name}`;
    }
    case 1 /* Symbol */:
      return "KNT_ERROR_1: Symbol must use Symbol.for(...) keys";
    case 2 /* Json */:
      return detail == null || detail.length === 0 ? "KNT_ERROR_2: JSON stringify failed; payload must be JSON-safe" : `KNT_ERROR_2: JSON stringify failed; ${detail}`;
    case 3 /* Serializable */:
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
  if (!isMainThread) {
    task.value = reason;
    task[0 /* FlagsToHost */] = 1 /* Reject */;
    return false;
  }
  if (onPromise == null) {
    throw new TypeError(reason);
  }
  const markedTask = task;
  if (markedTask[promisePayloadMarker] === true)
    return false;
  markedTask[promisePayloadMarker] = true;
  queueMicrotask(() => {
    markedTask[promisePayloadMarker] = false;
    task[PromisePayloadStatusSymbol] = 2 /* Rejected */;
    task.value = reason;
    const result = getPromisePayloadResult(task);
    result.status = "rejected";
    result.value = undefined;
    result.reason = reason;
    onPromise(task, result);
  });
  return false;
};

// src/common/envelope.ts
class Envelope {
  header;
  payload;
  constructor(header, payload) {
    this.header = header;
    this.payload = payload;
  }
}

// src/memory/payloadCodec.ts
var memory = new ArrayBuffer(8);
var Float64View = new Float64Array(memory);
var BigInt64View = new BigInt64Array(memory);
var Uint32View = new Uint32Array(memory);
var BIGINT64_MIN = -(1n << 63n);
var BIGINT64_MAX = (1n << 63n) - 1n;
var { parse: parseJSON, stringify: stringifyJSON } = JSON;
var { for: symbolFor, keyFor: symbolKeyFor } = Symbol;
var objectGetPrototypeOf = Object.getPrototypeOf;
var objectHasOwn = Object.prototype.hasOwnProperty;
var arrayIsArray = Array.isArray;
var objectPrototype = Object.prototype;
var UNSUPPORTED_OBJECT_DETAIL = "Unsupported object type. Allowed: plain object, array, Error, Date, Envelope, Buffer, ArrayBuffer, DataView, and typed arrays. Serialize it yourself.";
var ENVELOPE_PAYLOAD_DETAIL = "Envelope payload must be an ArrayBuffer.";
var ENVELOPE_HEADER_DETAIL = "Envelope header must be a JSON-like value or string.";
var ENVELOPE_PROMISE_DETAIL = "Envelope header cannot contain Promise values.";
var DYNAMIC_PAYLOAD_LIMIT_DETAIL = "Dynamic payload exceeds maxPayloadBytes.";
var DYNAMIC_PAYLOAD_CAPACITY_DETAIL = "Dynamic payload buffer capacity exceeded.";
var isPlainJsonObject = (value) => {
  const proto = objectGetPrototypeOf(value);
  return proto === objectPrototype || proto === null;
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
var initStaticIO = (headersBuffer) => {
  const u32Bytes = Uint32Array.BYTES_PER_ELEMENT;
  const slotStride = 0 /* header */ + 144 /* TotalBuff */;
  const slotOffset = (at) => at * slotStride + 0 /* header */;
  const slotStartBytes = (at) => (slotOffset(at) + 8 /* Size */) * u32Bytes;
  const writableBytes = (144 /* TotalBuff */ - 8 /* Size */) * u32Bytes;
  const requiredBytes = slotStartBytes(32 /* slots */ - 1) + writableBytes;
  if (headersBuffer.byteLength < requiredBytes)
    return null;
  return createSharedStaticBufferIO({
    headersBuffer: headersBuffer.buffer
  });
};
var requireStaticIO = (headersBuffer) => {
  const staticIO = initStaticIO(headersBuffer);
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
  onPromise,
  sharedRegister
}) => {
  const payloadSab = payload?.sab ?? sab;
  const resolvedPayloadConfig = resolvePayloadBufferOptions({
    sab: payloadSab,
    options: payload?.config ?? payloadConfig
  });
  const maxPayloadBytes = resolvedPayloadConfig.maxPayloadBytes;
  const { allocTask, setSlotLength, free } = sharedRegister ?? register({
    lockSector
  });
  const {
    writeBinary: writeDynamicBinary,
    write8Binary: writeDynamic8Binary,
    writeUtf8: writeDynamicUtf8
  } = createSharedDynamicBufferIO({
    sab: payloadSab,
    payloadConfig: resolvedPayloadConfig
  });
  const {
    maxBytes: staticMaxBytes,
    writeBinary: writeStaticBinary,
    write8Binary: writeStatic8Binary,
    writeUtf8: writeStaticUtf8
  } = requireStaticIO(headersBuffer);
  const dynamicLimitError = (task, actualBytes, label) => encoderError({
    task,
    type: 3 /* Serializable */,
    onPromise,
    detail: `${DYNAMIC_PAYLOAD_LIMIT_DETAIL} limit=${maxPayloadBytes}; ` + `actual=${actualBytes}; type=${label}.`
  });
  const dynamicCapacityError = (task) => encoderError({
    task,
    type: 3 /* Serializable */,
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
    const exactBytes = NodeBuffer2.byteLength(text, "utf8");
    const exactTotal = exactBytes + extraBytes;
    if (exactTotal > maxPayloadBytes) {
      dynamicLimitError(task, exactTotal, label);
      return -1;
    }
    return exactBytes;
  };
  const dynamicUtf8ReserveBytes = (task, text, label) => dynamicUtf8ReserveBytesWithExtra(task, text, 0, label);
  const reserveDynamic = (task, bytes) => {
    task[5 /* PayloadLen */] = bytes;
    return allocTask(task);
  };
  let objectDynamicSlot = -1;
  const reserveDynamicObject = (task, bytes) => {
    task[5 /* PayloadLen */] = bytes;
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
        type: 3 /* Serializable */,
        onPromise,
        detail
      });
    }
    const reserveBytes = dynamicUtf8ReserveBytes(task, text, "Error");
    if (reserveBytes < 0)
      return false;
    task[2 /* Type */] = 24 /* Error */;
    const reservedSlot = reserveDynamicObject(task, reserveBytes);
    if (reservedSlot === -1)
      return false;
    const written = writeDynamicUtf8(text, task[3 /* Start */], reserveBytes);
    if (written < 0)
      return failDynamicWriteAfterReserve(task, reservedSlot);
    task[5 /* PayloadLen */] = written;
    setSlotLength(reservedSlot, written);
    task.value = null;
    return true;
  };
  const encodeObjectBinary = (task, slotIndex, bytesView, dynamicType, staticType) => {
    const bytes = bytesView.byteLength;
    if (bytes <= staticMaxBytes) {
      const written2 = writeStaticBinary(bytesView, slotIndex);
      if (written2 !== -1) {
        task[2 /* Type */] = staticType;
        task[5 /* PayloadLen */] = written2;
        task.value = null;
        return true;
      }
    }
    task[2 /* Type */] = dynamicType;
    if (!ensureWithinDynamicLimit(task, bytes, PayloadBuffer[dynamicType])) {
      return false;
    }
    const reservedSlot = reserveDynamicObject(task, bytes);
    if (reservedSlot === -1)
      return false;
    const written = writeDynamicBinary(bytesView, task[3 /* Start */]);
    if (written < 0)
      return failDynamicWriteAfterReserve(task, reservedSlot);
    task[5 /* PayloadLen */] = written;
    setSlotLength(reservedSlot, written);
    task.value = null;
    return true;
  };
  const encodeObjectFloat64Array = (task, slotIndex, float64) => {
    const bytes = float64.byteLength;
    if (bytes <= staticMaxBytes) {
      const written2 = writeStatic8Binary(float64, slotIndex);
      if (written2 !== -1) {
        task[2 /* Type */] = 32 /* StaticFloat64Array */;
        task[5 /* PayloadLen */] = written2;
        task.value = null;
        return true;
      }
    }
    task[2 /* Type */] = 20 /* Float64Array */;
    if (!ensureWithinDynamicLimit(task, bytes, "Float64Array"))
      return false;
    const reservedSlot = reserveDynamicObject(task, bytes);
    if (reservedSlot === -1)
      return false;
    const written = writeDynamic8Binary(float64, task[3 /* Start */]);
    if (written < 0)
      return failDynamicWriteAfterReserve(task, reservedSlot);
    task[5 /* PayloadLen */] = written;
    setSlotLength(reservedSlot, written);
    task.value = null;
    return true;
  };
  const encodeObjectArrayBuffer = (task, slotIndex, arrayBuffer) => {
    const bytes = arrayBuffer.byteLength;
    let bytesView;
    if (bytes <= staticMaxBytes) {
      bytesView = new Uint8Array(arrayBuffer);
      const written2 = writeStaticBinary(bytesView, slotIndex);
      if (written2 !== -1) {
        task[2 /* Type */] = 37 /* StaticArrayBuffer */;
        task[5 /* PayloadLen */] = written2;
        task.value = null;
        return true;
      }
    }
    task[2 /* Type */] = 36 /* ArrayBuffer */;
    if (!ensureWithinDynamicLimit(task, bytes, "ArrayBuffer"))
      return false;
    const reservedSlot = reserveDynamicObject(task, bytes);
    if (reservedSlot === -1)
      return false;
    const written = writeDynamicBinary(bytesView ?? new Uint8Array(arrayBuffer), task[3 /* Start */]);
    if (written < 0)
      return failDynamicWriteAfterReserve(task, reservedSlot);
    task[5 /* PayloadLen */] = written;
    setSlotLength(reservedSlot, written);
    task.value = null;
    return true;
  };
  const encodeObjectDate = (task, date) => {
    Float64View[0] = date.getTime();
    task[2 /* Type */] = 25 /* Date */;
    task[3 /* Start */] = Uint32View[0];
    task[4 /* End */] = Uint32View[1];
    task.value = null;
    return true;
  };
  const encodeObjectEnvelope = (task, slotIndex, envelope) => {
    const header = envelope.header;
    const payload2 = envelope.payload;
    if (!(payload2 instanceof ArrayBuffer)) {
      return encoderError({
        task,
        type: 3 /* Serializable */,
        onPromise,
        detail: ENVELOPE_PAYLOAD_DETAIL
      });
    }
    if (hasPromiseInEnvelopeHeader(header)) {
      return encoderError({
        task,
        type: 3 /* Serializable */,
        onPromise,
        detail: ENVELOPE_PROMISE_DETAIL
      });
    }
    let headerText;
    try {
      headerText = stringifyJSON(header);
    } catch (error) {
      const detail = error instanceof Error ? error.message : String(error);
      return encoderError({
        task,
        type: 2 /* Json */,
        onPromise,
        detail
      });
    }
    if (typeof headerText !== "string") {
      return encoderError({
        task,
        type: 3 /* Serializable */,
        onPromise,
        detail: ENVELOPE_HEADER_DETAIL
      });
    }
    const payloadBytes = new Uint8Array(payload2);
    const payloadLength = payloadBytes.byteLength;
    const payloadReserveBytes = payloadLength > 0 ? payloadLength : 1;
    const staticHeaderWritten = writeStaticUtf8(headerText, slotIndex);
    if (staticHeaderWritten !== -1) {
      if (!ensureWithinDynamicLimit(task, payloadReserveBytes, "EnvelopeStaticHeaderPayload"))
        return false;
      const reservedSlot2 = reserveDynamicObject(task, payloadReserveBytes);
      if (reservedSlot2 === -1)
        return false;
      task[2 /* Type */] = 40 /* EnvelopeStaticHeader */;
      task[5 /* PayloadLen */] = staticHeaderWritten;
      task[4 /* End */] = payloadLength;
      if (payloadLength > 0) {
        const payloadWritten = writeDynamicBinary(payloadBytes, task[3 /* Start */]);
        if (payloadWritten < 0) {
          return failDynamicWriteAfterReserve(task, reservedSlot2);
        }
        setSlotLength(reservedSlot2, payloadWritten);
      }
      task.value = null;
      return true;
    }
    const headerReserveBytes = dynamicUtf8ReserveBytesWithExtra(task, headerText, payloadLength, "EnvelopeDynamicHeader");
    if (headerReserveBytes < 0)
      return false;
    task[2 /* Type */] = 41 /* EnvelopeDynamicHeader */;
    const reservedSlot = reserveDynamicObject(task, headerReserveBytes + payloadLength);
    if (reservedSlot === -1)
      return false;
    const baseStart = task[3 /* Start */];
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
    task[5 /* PayloadLen */] = writtenHeaderBytes;
    task[4 /* End */] = payloadLength;
    setSlotLength(reservedSlot, writtenHeaderBytes + payloadLength);
    task.value = null;
    return true;
  };
  const encodeObjectPromise = (task, promise) => {
    const markedTask = task;
    markedTask[PromisePayloadHandlerSymbol] = onPromise;
    if (markedTask[PromisePayloadMarker] !== true) {
      markedTask[PromisePayloadMarker] = true;
      markedTask[PromisePayloadStatusSymbol] = 0 /* Idle */;
      promise.then(markedTask[PromisePayloadFulfillSymbol], markedTask[PromisePayloadRejectSymbol]);
    }
    return false;
  };
  const encodeDispatch = (task, slotIndex) => {
    const args = task.value;
    switch (typeof args) {
      case "bigint":
        if (args < BIGINT64_MIN || args > BIGINT64_MAX) {
          const binaryBytes = encodeBigIntIntoScratch(args);
          const binary = bigintScratch.subarray(0, binaryBytes);
          if (binaryBytes <= staticMaxBytes) {
            const written2 = writeStaticBinary(binary, slotIndex);
            if (written2 !== -1) {
              task[2 /* Type */] = 29 /* StaticBigInt */;
              task[5 /* PayloadLen */] = written2;
              clearBigIntScratch(binaryBytes);
              task.value = null;
              return true;
            }
          }
          task[2 /* Type */] = 28 /* BigInt */;
          if (!ensureWithinDynamicLimit(task, binaryBytes, "BigInt")) {
            clearBigIntScratch(binaryBytes);
            return false;
          }
          const reservedSlot = reserveDynamic(task, binaryBytes);
          if (reservedSlot < 0) {
            clearBigIntScratch(binaryBytes);
            return false;
          }
          const written = writeDynamicBinary(binary, task[3 /* Start */]);
          if (written < 0) {
            clearBigIntScratch(binaryBytes);
            return failDynamicWriteAfterReserve(task, reservedSlot);
          }
          task[5 /* PayloadLen */] = written;
          setSlotLength(reservedSlot, written);
          clearBigIntScratch(binaryBytes);
          task.value = null;
          return true;
        }
        BigInt64View[0] = args;
        task[2 /* Type */] = 2 /* BigInt */;
        task[3 /* Start */] = Uint32View[0];
        task[4 /* End */] = Uint32View[1];
        task.value = null;
        return true;
      case "boolean":
        task[2 /* Type */] = task.value === true ? 3 /* True */ : 4 /* False */;
        return true;
      case "function":
        return encoderError({
          task,
          type: 0 /* Function */,
          onPromise
        });
      case "number":
        if (args !== args) {
          task[2 /* Type */] = 6 /* NaN */;
          return true;
        }
        Float64View[0] = args;
        task[2 /* Type */] = 9 /* Float64 */;
        task[3 /* Start */] = Uint32View[0];
        task[4 /* End */] = Uint32View[1];
        return true;
      case "object":
        if (args === null) {
          task[2 /* Type */] = 10 /* Null */;
          return true;
        }
        objectDynamicSlot = -1;
        try {
          const objectValue = args;
          if (arrayIsArray(objectValue) || isPlainJsonObject(objectValue)) {
            let text;
            try {
              text = stringifyJSON(objectValue);
            } catch (error) {
              const detail = error instanceof Error ? error.message : String(error);
              return encoderError({
                task,
                type: 2 /* Json */,
                onPromise,
                detail
              });
            }
            if (text.length <= staticMaxBytes) {
              const written2 = writeStaticUtf8(text, slotIndex);
              if (written2 !== -1) {
                task[2 /* Type */] = 16 /* StaticJson */;
                task[5 /* PayloadLen */] = written2;
                task.value = null;
                return true;
              }
            }
            task[2 /* Type */] = 12 /* Json */;
            const reserveBytes = dynamicUtf8ReserveBytes(task, text, "Json");
            if (reserveBytes < 0)
              return false;
            const reservedSlot = reserveDynamicObject(task, reserveBytes);
            if (reservedSlot === -1)
              return false;
            const written = writeDynamicUtf8(text, task[3 /* Start */], reserveBytes);
            if (written < 0)
              return failDynamicWriteAfterReserve(task, reservedSlot);
            task[5 /* PayloadLen */] = written;
            setSlotLength(reservedSlot, written);
            task.value = null;
            return true;
          }
          if (NodeBuffer2.isBuffer(objectValue)) {
            return encodeObjectBinary(task, slotIndex, objectValue, 38 /* Buffer */, 39 /* StaticBuffer */);
          }
          switch (objectValue.constructor) {
            case Uint8Array:
              return encodeObjectBinary(task, slotIndex, objectValue, 17 /* Binary */, 18 /* StaticBinary */);
            case ArrayBuffer:
              return encodeObjectArrayBuffer(task, slotIndex, objectValue);
            case Int32Array: {
              const int32 = objectValue;
              return encodeObjectBinary(task, slotIndex, new Uint8Array(int32.buffer, int32.byteOffset, int32.byteLength), 19 /* Int32Array */, 31 /* StaticInt32Array */);
            }
            case Float64Array:
              return encodeObjectFloat64Array(task, slotIndex, objectValue);
            case BigInt64Array: {
              const bigInt64 = objectValue;
              return encodeObjectBinary(task, slotIndex, new Uint8Array(bigInt64.buffer, bigInt64.byteOffset, bigInt64.byteLength), 21 /* BigInt64Array */, 33 /* StaticBigInt64Array */);
            }
            case BigUint64Array: {
              const bigUint64 = objectValue;
              return encodeObjectBinary(task, slotIndex, new Uint8Array(bigUint64.buffer, bigUint64.byteOffset, bigUint64.byteLength), 22 /* BigUint64Array */, 34 /* StaticBigUint64Array */);
            }
            case DataView: {
              const dataView = objectValue;
              return encodeObjectBinary(task, slotIndex, new Uint8Array(dataView.buffer, dataView.byteOffset, dataView.byteLength), 23 /* DataView */, 35 /* StaticDataView */);
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
          if (objectValue instanceof Date)
            return encodeObjectDate(task, objectValue);
          if (objectValue instanceof Envelope) {
            return encodeObjectEnvelope(task, slotIndex, objectValue);
          }
          if (objectValue instanceof Promise) {
            return encodeObjectPromise(task, objectValue);
          }
          if (objectValue instanceof Error) {
            return encodeErrorObject(task, objectValue);
          }
          return encoderError({
            task,
            type: 3 /* Serializable */,
            onPromise,
            detail: UNSUPPORTED_OBJECT_DETAIL
          });
        } catch (error) {
          rollbackObjectDynamic();
          const detail = error instanceof Error ? error.message : String(error);
          return encoderError({
            task,
            type: 3 /* Serializable */,
            onPromise,
            detail
          });
        }
      case "string": {
        const text = args;
        if (text.length <= staticMaxBytes) {
          const written2 = writeStaticUtf8(text, slotIndex);
          if (written2 !== -1) {
            task[2 /* Type */] = 15 /* StaticString */;
            task[5 /* PayloadLen */] = written2;
            task.value = null;
            return true;
          }
        }
        task[2 /* Type */] = 11 /* String */;
        const reserveBytes = dynamicUtf8ReserveBytes(task, text, "String");
        if (reserveBytes < 0)
          return false;
        const reservedSlot = reserveDynamic(task, reserveBytes);
        if (reservedSlot < 0)
          return false;
        const written = writeDynamicUtf8(text, task[3 /* Start */], reserveBytes);
        if (written < 0)
          return failDynamicWriteAfterReserve(task, reservedSlot);
        task[5 /* PayloadLen */] = written;
        setSlotLength(reservedSlot, written);
        task.value = null;
        return true;
      }
      case "symbol": {
        const key = symbolKeyFor(args);
        if (key === undefined) {
          return encoderError({
            task,
            type: 1 /* Symbol */,
            onPromise
          });
        }
        if (key.length * 3 <= staticMaxBytes) {
          const written2 = writeStaticUtf8(key, slotIndex);
          if (written2 !== -1) {
            task[2 /* Type */] = 27 /* StaticSymbol */;
            task[5 /* PayloadLen */] = written2;
            task.value = null;
            return true;
          }
        }
        task[2 /* Type */] = 26 /* Symbol */;
        const reserveBytes = dynamicUtf8ReserveBytes(task, key, "Symbol");
        if (reserveBytes < 0)
          return false;
        const reservedSlot = reserveDynamic(task, reserveBytes);
        if (reservedSlot < 0)
          return false;
        const written = writeDynamicUtf8(key, task[3 /* Start */], reserveBytes);
        if (written < 0)
          return failDynamicWriteAfterReserve(task, reservedSlot);
        task[5 /* PayloadLen */] = written;
        setSlotLength(reservedSlot, written);
        task.value = null;
        return true;
      }
      case "undefined":
        task[2 /* Type */] = 5 /* Undefined */;
        return true;
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
  host,
  sharedRegister
}) => {
  const payloadSab = payload?.sab ?? sab;
  const resolvedPayloadConfig = resolvePayloadBufferOptions({
    sab: payloadSab,
    options: payload?.config ?? payloadConfig
  });
  const { free } = sharedRegister ?? register({
    lockSector
  });
  const freeTaskSlot = (task) => free(getTaskSlotIndex(task));
  const {
    readUtf8: readDynamicUtf8,
    readBytesCopy: readDynamicBytesCopy,
    readBytesBufferCopy: readDynamicBufferCopy,
    readBytesArrayBufferCopy: readDynamicArrayBufferCopy,
    read8BytesFloatCopy: readDynamic8BytesFloatCopy,
    read8BytesFloatView: readDynamic8BytesFloatView
  } = createSharedDynamicBufferIO({
    sab: payloadSab,
    payloadConfig: resolvedPayloadConfig
  });
  const {
    readUtf8: readStaticUtf8,
    readBytesCopy: readStaticBytesCopy,
    readBytesBufferCopy: readStaticBufferCopy,
    readBytesArrayBufferCopy: readStaticArrayBufferCopy,
    read8BytesFloatCopy: readStatic8BytesFloatCopy
  } = requireStaticIO(headersBuffer);
  return (task, slotIndex, specialFlags) => {
    switch (task[2 /* Type */]) {
      case 2 /* BigInt */:
        Uint32View[0] = task[3 /* Start */];
        Uint32View[1] = task[4 /* End */];
        task.value = BigInt64View[0];
        return;
      case 3 /* True */:
        task.value = true;
        return;
      case 4 /* False */:
        task.value = false;
        return;
      case 9 /* Float64 */:
        Uint32View[0] = task[3 /* Start */];
        Uint32View[1] = task[4 /* End */];
        task.value = Float64View[0];
        return;
      case 6 /* NaN */:
        task.value = NaN;
        return;
      case 10 /* Null */:
        task.value = null;
        return;
      case 5 /* Undefined */:
        task.value = undefined;
        return;
      case 11 /* String */:
        task.value = readDynamicUtf8(task[3 /* Start */], task[3 /* Start */] + task[5 /* PayloadLen */]);
        freeTaskSlot(task);
        return;
      case 15 /* StaticString */:
        task.value = readStaticUtf8(0, task[5 /* PayloadLen */], slotIndex);
        return;
      case 12 /* Json */:
        task.value = parseJSON(readDynamicUtf8(task[3 /* Start */], task[3 /* Start */] + task[5 /* PayloadLen */]));
        freeTaskSlot(task);
        return;
      case 16 /* StaticJson */:
        task.value = parseJSON(readStaticUtf8(0, task[5 /* PayloadLen */], slotIndex));
        return;
      case 40 /* EnvelopeStaticHeader */: {
        const header = parseJSON(readStaticUtf8(0, task[5 /* PayloadLen */], slotIndex));
        const payloadLength = task[4 /* End */];
        const payload2 = payloadLength > 0 ? readDynamicArrayBufferCopy(task[3 /* Start */], task[3 /* Start */] + payloadLength) : new ArrayBuffer(0);
        task.value = new Envelope(header, payload2);
        freeTaskSlot(task);
        return;
      }
      case 41 /* EnvelopeDynamicHeader */: {
        const headerStart = task[3 /* Start */];
        const payloadStart = headerStart + task[5 /* PayloadLen */];
        const payloadLength = task[4 /* End */];
        const header = parseJSON(readDynamicUtf8(headerStart, payloadStart));
        const payload2 = payloadLength > 0 ? readDynamicArrayBufferCopy(payloadStart, payloadStart + payloadLength) : new ArrayBuffer(0);
        task.value = new Envelope(header, payload2);
        freeTaskSlot(task);
        return;
      }
      case 28 /* BigInt */:
        task.value = decodeBigIntBinary(readDynamicBufferCopy(task[3 /* Start */], task[3 /* Start */] + task[5 /* PayloadLen */]));
        freeTaskSlot(task);
        return;
      case 29 /* StaticBigInt */:
        task.value = decodeBigIntBinary(readStaticBufferCopy(0, task[5 /* PayloadLen */], slotIndex));
        return;
      case 26 /* Symbol */:
        task.value = symbolFor(readDynamicUtf8(task[3 /* Start */], task[3 /* Start */] + task[5 /* PayloadLen */]));
        freeTaskSlot(task);
        return;
      case 27 /* StaticSymbol */:
        task.value = symbolFor(readStaticUtf8(0, task[5 /* PayloadLen */], slotIndex));
        return;
      case 19 /* Int32Array */: {
        const bytes = readDynamicBufferCopy(task[3 /* Start */], task[3 /* Start */] + task[5 /* PayloadLen */]);
        task.value = new Int32Array(bytes.buffer, bytes.byteOffset, bytes.byteLength >>> 2);
        freeTaskSlot(task);
        return;
      }
      case 31 /* StaticInt32Array */: {
        const bytes = readStaticBufferCopy(0, task[5 /* PayloadLen */], slotIndex);
        task.value = new Int32Array(bytes.buffer, bytes.byteOffset, bytes.byteLength >>> 2);
        return;
      }
      case 20 /* Float64Array */: {
        task.value = readDynamic8BytesFloatCopy(task[3 /* Start */], task[3 /* Start */] + task[5 /* PayloadLen */]);
        freeTaskSlot(task);
        return;
      }
      case 32 /* StaticFloat64Array */:
        task.value = readStatic8BytesFloatCopy(0, task[5 /* PayloadLen */], slotIndex);
        return;
      case 21 /* BigInt64Array */: {
        const bytes = readDynamicBufferCopy(task[3 /* Start */], task[3 /* Start */] + task[5 /* PayloadLen */]);
        task.value = new BigInt64Array(bytes.buffer, bytes.byteOffset, bytes.byteLength >>> 3);
        freeTaskSlot(task);
        return;
      }
      case 33 /* StaticBigInt64Array */: {
        const bytes = readStaticBufferCopy(0, task[5 /* PayloadLen */], slotIndex);
        task.value = new BigInt64Array(bytes.buffer, bytes.byteOffset, bytes.byteLength >>> 3);
        return;
      }
      case 22 /* BigUint64Array */: {
        const bytes = readDynamicBufferCopy(task[3 /* Start */], task[3 /* Start */] + task[5 /* PayloadLen */]);
        task.value = new BigUint64Array(bytes.buffer, bytes.byteOffset, bytes.byteLength >>> 3);
        freeTaskSlot(task);
        return;
      }
      case 34 /* StaticBigUint64Array */: {
        const bytes = readStaticBufferCopy(0, task[5 /* PayloadLen */], slotIndex);
        task.value = new BigUint64Array(bytes.buffer, bytes.byteOffset, bytes.byteLength >>> 3);
        return;
      }
      case 23 /* DataView */: {
        const bytes = readDynamicBufferCopy(task[3 /* Start */], task[3 /* Start */] + task[5 /* PayloadLen */]);
        task.value = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
        freeTaskSlot(task);
        return;
      }
      case 35 /* StaticDataView */: {
        const bytes = readStaticBufferCopy(0, task[5 /* PayloadLen */], slotIndex);
        task.value = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
        return;
      }
      case 25 /* Date */:
        Uint32View[0] = task[3 /* Start */];
        Uint32View[1] = task[4 /* End */];
        task.value = new Date(Float64View[0]);
        return;
      case 24 /* Error */:
        task.value = parseErrorPayload(readDynamicUtf8(task[3 /* Start */], task[3 /* Start */] + task[5 /* PayloadLen */]));
        freeTaskSlot(task);
        return;
      case 17 /* Binary */:
        {
          const buffer = readDynamicBufferCopy(task[3 /* Start */], task[3 /* Start */] + task[5 /* PayloadLen */]);
          task.value = new Uint8Array(buffer.buffer, buffer.byteOffset, buffer.byteLength);
        }
        freeTaskSlot(task);
        return;
      case 18 /* StaticBinary */:
        task.value = readStaticBufferCopy(0, task[5 /* PayloadLen */], slotIndex);
        return;
      case 36 /* ArrayBuffer */:
        task.value = readDynamicArrayBufferCopy(task[3 /* Start */], task[3 /* Start */] + task[5 /* PayloadLen */]);
        freeTaskSlot(task);
        return;
      case 37 /* StaticArrayBuffer */:
        task.value = readStaticArrayBufferCopy(0, task[5 /* PayloadLen */], slotIndex);
        return;
      case 38 /* Buffer */:
        task.value = readDynamicBufferCopy(task[3 /* Start */], task[3 /* Start */] + task[5 /* PayloadLen */]);
        freeTaskSlot(task);
        return;
      case 39 /* StaticBuffer */:
        task.value = readStaticBufferCopy(0, task[5 /* PayloadLen */], slotIndex);
        return;
    }
  };
};

// src/memory/lock.ts
var PayloadBuffer;
((PayloadBuffer2) => {
  PayloadBuffer2[PayloadBuffer2["BORDER_SIGNAL_BUFFER"] = 11] = "BORDER_SIGNAL_BUFFER";
  PayloadBuffer2[PayloadBuffer2["String"] = 11] = "String";
  PayloadBuffer2[PayloadBuffer2["Json"] = 12] = "Json";
  PayloadBuffer2[PayloadBuffer2["StaticString"] = 15] = "StaticString";
  PayloadBuffer2[PayloadBuffer2["StaticJson"] = 16] = "StaticJson";
  PayloadBuffer2[PayloadBuffer2["Binary"] = 17] = "Binary";
  PayloadBuffer2[PayloadBuffer2["StaticBinary"] = 18] = "StaticBinary";
  PayloadBuffer2[PayloadBuffer2["Int32Array"] = 19] = "Int32Array";
  PayloadBuffer2[PayloadBuffer2["Float64Array"] = 20] = "Float64Array";
  PayloadBuffer2[PayloadBuffer2["BigInt64Array"] = 21] = "BigInt64Array";
  PayloadBuffer2[PayloadBuffer2["BigUint64Array"] = 22] = "BigUint64Array";
  PayloadBuffer2[PayloadBuffer2["DataView"] = 23] = "DataView";
  PayloadBuffer2[PayloadBuffer2["Error"] = 24] = "Error";
  PayloadBuffer2[PayloadBuffer2["Date"] = 25] = "Date";
  PayloadBuffer2[PayloadBuffer2["Symbol"] = 26] = "Symbol";
  PayloadBuffer2[PayloadBuffer2["StaticSymbol"] = 27] = "StaticSymbol";
  PayloadBuffer2[PayloadBuffer2["BigInt"] = 28] = "BigInt";
  PayloadBuffer2[PayloadBuffer2["StaticBigInt"] = 29] = "StaticBigInt";
  PayloadBuffer2[PayloadBuffer2["StaticInt32Array"] = 31] = "StaticInt32Array";
  PayloadBuffer2[PayloadBuffer2["StaticFloat64Array"] = 32] = "StaticFloat64Array";
  PayloadBuffer2[PayloadBuffer2["StaticBigInt64Array"] = 33] = "StaticBigInt64Array";
  PayloadBuffer2[PayloadBuffer2["StaticBigUint64Array"] = 34] = "StaticBigUint64Array";
  PayloadBuffer2[PayloadBuffer2["StaticDataView"] = 35] = "StaticDataView";
  PayloadBuffer2[PayloadBuffer2["ArrayBuffer"] = 36] = "ArrayBuffer";
  PayloadBuffer2[PayloadBuffer2["StaticArrayBuffer"] = 37] = "StaticArrayBuffer";
  PayloadBuffer2[PayloadBuffer2["Buffer"] = 38] = "Buffer";
  PayloadBuffer2[PayloadBuffer2["StaticBuffer"] = 39] = "StaticBuffer";
  PayloadBuffer2[PayloadBuffer2["EnvelopeStaticHeader"] = 40] = "EnvelopeStaticHeader";
  PayloadBuffer2[PayloadBuffer2["EnvelopeDynamicHeader"] = 41] = "EnvelopeDynamicHeader";
})(PayloadBuffer ||= {});
var LOCK_CACHE_LINE_BYTES = 64;
var LOCK_SECTOR_BYTES = 256;
var PromisePayloadMarker = Symbol.for("knitting.promise.payload");
var PromisePayloadHandlerSymbol = Symbol.for("knitting.promise.payload.handler");
var PromisePayloadStatusSymbol = Symbol.for("knitting.promise.payload.status");
var PromisePayloadResultSymbol = Symbol.for("knitting.promise.payload.result");
var PromisePayloadFulfillSymbol = Symbol.for("knitting.promise.payload.fulfill");
var PromisePayloadRejectSymbol = Symbol.for("knitting.promise.payload.reject");
var getPromisePayloadResult = (task) => task[PromisePayloadResultSymbol];
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
var getTaskFunctionMeta = (task) => task[0 /* FunctionID */] >>> TASK_FUNCTION_ID_BITS & TASK_FUNCTION_META_VALUE_MASK;
var getTaskSlotIndex = (task) => task[6 /* slotBuffer */] & TASK_SLOT_INDEX_MASK;
var getTaskSlotMeta = (task) => task[6 /* slotBuffer */] >>> TASK_SLOT_INDEX_BITS & TASK_SLOT_META_VALUE_MASK;
var LOCK_WORD_BYTES = Int32Array.BYTES_PER_ELEMENT;
var LOCK_HOST_BITS_OFFSET_BYTES = 0 /* paddingLock */;
var LOCK_WORKER_BITS_OFFSET_BYTES = LOCK_CACHE_LINE_BYTES;
var LOCK_SECTOR_BYTE_LENGTH = LOCK_SECTOR_BYTES;
var PAYLOAD_LOCK_HOST_BITS_OFFSET_BYTES = LOCK_CACHE_LINE_BYTES * 2;
var PAYLOAD_LOCK_WORKER_BITS_OFFSET_BYTES = LOCK_CACHE_LINE_BYTES * 3;
var HEADER_SLOT_STRIDE_U32 = 0 /* header */ + 144 /* TotalBuff */;
var HEADER_U32_LENGTH = 0 /* header */ + HEADER_SLOT_STRIDE_U32 * 32 /* slots */;
var HEADER_BYTE_LENGTH = HEADER_U32_LENGTH * Uint32Array.BYTES_PER_ELEMENT;
var INDEX_ID = 0;
var def = (_) => {};
var createTaskShell = () => {
  const task = new Uint32Array(8 /* Size */);
  task.value = null;
  task.resolve = def;
  task.reject = def;
  task[PromisePayloadMarker] = false;
  task[PromisePayloadHandlerSymbol] = undefined;
  task[PromisePayloadStatusSymbol] = 0 /* Idle */;
  task[PromisePayloadResultSymbol] = {
    status: "fulfilled",
    value: undefined,
    reason: undefined
  };
  task[PromisePayloadFulfillSymbol] = (value) => {
    task[PromisePayloadMarker] = false;
    task[PromisePayloadStatusSymbol] = 1 /* Fulfilled */;
    task.value = value;
    const result = task[PromisePayloadResultSymbol];
    result.status = "fulfilled";
    result.value = value;
    result.reason = undefined;
    task[PromisePayloadHandlerSymbol](task, result);
  };
  task[PromisePayloadRejectSymbol] = (reason) => {
    task[PromisePayloadMarker] = false;
    task[PromisePayloadStatusSymbol] = 2 /* Rejected */;
    task.value = reason;
    const result = task[PromisePayloadResultSymbol];
    result.status = "rejected";
    result.value = undefined;
    result.reason = reason;
    task[PromisePayloadHandlerSymbol](task, result);
  };
  return task;
};
var makeTask = () => {
  const task = createTaskShell();
  task[1 /* ID */] = INDEX_ID++;
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
};
var makeTaskFrom = (array, at) => {
  const task = createTaskShell();
  fillTaskFrom(task, array, at);
  return task;
};
var settleTask = (task) => {
  if (task[0 /* FlagsToHost */] === 0) {
    task.resolve(task.value);
  } else {
    task.reject(task.value);
    task[0 /* FlagsToHost */] = 0;
  }
};
var lock2 = ({
  headers,
  LockBoundSector,
  payload,
  payloadConfig,
  payloadSector,
  resultList,
  toSentList,
  recycleList
}) => {
  const LockBoundSAB = LockBoundSector ?? new SharedArrayBuffer(LOCK_SECTOR_BYTE_LENGTH);
  const hostBits = new Int32Array(LockBoundSAB, LOCK_HOST_BITS_OFFSET_BYTES, 1);
  const workerBits = new Int32Array(LockBoundSAB, LOCK_WORKER_BITS_OFFSET_BYTES, 1);
  const bufferHeadersBuffer = headers ?? new SharedArrayBuffer(HEADER_BYTE_LENGTH);
  const headersBuffer = new Uint32Array(bufferHeadersBuffer);
  const resolvedPayloadConfig = resolvePayloadBufferOptions({
    sab: payload,
    options: payloadConfig
  });
  const payloadSAB = payload ?? (resolvedPayloadConfig.mode === "growable" ? createSharedArrayBuffer(resolvedPayloadConfig.payloadInitialBytes, resolvedPayloadConfig.payloadMaxByteLength) : createSharedArrayBuffer(resolvedPayloadConfig.payloadInitialBytes));
  const payloadLockSAB = payloadSector ?? LockBoundSAB;
  const payloadRegister = register({
    lockSector: payloadLockSAB
  });
  let promiseHandler;
  const encodeTask = encodePayload({
    payload: {
      sab: payloadSAB,
      config: resolvedPayloadConfig
    },
    headersBuffer,
    lockSector: payloadLockSAB,
    onPromise: (task, result) => promiseHandler?.(task, result),
    sharedRegister: payloadRegister
  });
  const decodeTask = decodePayload({
    payload: {
      sab: payloadSAB,
      config: resolvedPayloadConfig
    },
    headersBuffer,
    lockSector: payloadLockSAB,
    sharedRegister: payloadRegister
  });
  let LastLocal = 0 | 0;
  let LastWorker = 0 | 0;
  let lastTake = 32 | 0;
  const toBeSent = toSentList ?? new RingQueue;
  const recyclecList = recycleList ?? new RingQueue;
  const resolved = resultList ?? new RingQueue;
  const a_load = Atomics.load;
  const a_store = Atomics.store;
  const toBeSentPush = (task) => toBeSent.push(task);
  const toBeSentShift = () => toBeSent.shiftNoClear();
  const toBeSentUnshift = (task) => toBeSent.unshift(task);
  const recycleShift = () => recyclecList.shiftNoClear();
  const resolvedPush = (task) => resolved.push(task);
  const SLOT_SIZE = HEADER_SLOT_STRIDE_U32;
  const clz32 = Math.clz32;
  const slotOffset = (at) => at * SLOT_SIZE + 0 /* header */;
  const takeTask = ({ queue }) => (at) => {
    const off = slotOffset(at);
    const task = queue[headersBuffer[off + 1 /* ID */]];
    fillTaskFrom(task, headersBuffer, off);
    return task;
  };
  const enlist = (task) => toBeSentPush(task);
  let selectedSlotIndex = 0 | 0, selectedSlotBit = 0 >>> 0;
  const encodeWithState = (task, state) => {
    const free = ~state;
    if (free === 0)
      return 0;
    if (!encodeTask(task, selectedSlotIndex = 31 - clz32(free)))
      return 0;
    encodeAt(task, selectedSlotIndex, selectedSlotBit = 1 << selectedSlotIndex);
    return selectedSlotBit;
  };
  const encodeManyFrom = (list) => {
    let state = LastLocal ^ a_load(workerBits, 0) | 0;
    let encoded = 0 | 0;
    if (list === toBeSent) {
      while (true) {
        const task = toBeSentShift();
        if (!task)
          break;
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
  const encodeAll = () => {
    if (toBeSent.isEmpty)
      return true;
    encodeManyFrom(toBeSent);
    return toBeSent.isEmpty;
  };
  const storeHost = (bit) => a_store(hostBits, 0, LastLocal = LastLocal ^ bit | 0);
  const storeWorker = (bit) => a_store(workerBits, 0, LastWorker = LastWorker ^ bit | 0);
  const encode = (task, state = LastLocal ^ a_load(workerBits, 0) | 0) => {
    const free = ~state;
    if (free === 0)
      return false;
    if (!encodeTask(task, selectedSlotIndex = 31 - clz32(free)))
      return false;
    return encodeAt(task, selectedSlotIndex, selectedSlotBit = 1 << selectedSlotIndex);
  };
  const encodeAt = (task, at, bit) => {
    const off = slotOffset(at);
    headersBuffer[off] = task[0];
    headersBuffer[off + 1] = task[1];
    headersBuffer[off + 2] = task[2];
    headersBuffer[off + 3] = task[3];
    headersBuffer[off + 4] = task[4];
    headersBuffer[off + 5] = task[5];
    headersBuffer[off + 6] = task[6];
    headersBuffer[off + 7] = task[7];
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
  const resolveHost = ({
    queue,
    onResolved
  }) => {
    const getTask = takeTask({ queue });
    const HAS_RESOLVE = onResolved ? true : false;
    let lastResolved = 32;
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
        settleTask(task);
        if (HAS_RESOLVE) {
          onResolved(task);
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
        settleTask(task);
        if (HAS_RESOLVE) {
          onResolved(task);
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
  const decodeAt = (at) => {
    const off = slotOffset(at);
    const recycled = recycleShift();
    let task;
    if (recycled) {
      fillTaskFrom(recycled, headersBuffer, off);
      recycled.value = null;
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
  return {
    enlist,
    encode,
    encodeManyFrom,
    encodeAll,
    decode,
    hasSpace,
    resolved,
    hostBits,
    workerBits,
    recyclecList,
    resolveHost,
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
var throwIfAborted = (signal, hasAborted) => {
  if (signal === NO_ABORT_SIGNAL)
    return;
  if (hasAborted(signal))
    throw new Error("Task aborted");
};
var makeToolkitCache = (hasAborted) => {
  const bySignal = [];
  return (signal) => {
    let toolkit = bySignal[signal];
    if (toolkit)
      return toolkit;
    const hasAbortedMethod = () => hasAborted(signal);
    toolkit = {
      hasAborted: hasAbortedMethod
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
  const getToolkit = makeToolkitCache(hasAborted);
  if (!timeout) {
    return (slot) => {
      const signal = readSignal(slot);
      throwIfAborted(signal, hasAborted);
      if (signal === NO_ABORT_SIGNAL)
        return job(slot.value);
      return job(slot.value, getToolkit(signal));
    };
  }
  return (slot) => {
    const signal = readSignal(slot);
    throwIfAborted(signal, hasAborted);
    const result = signal === NO_ABORT_SIGNAL ? job(slot.value) : job(slot.value, getToolkit(signal));
    if (!(result instanceof Promise))
      return result;
    return applyTimeoutBudget(result, slot, timeout, nowTime);
  };
};

// src/worker/rx-queue.ts
var createWorkerRxQueue = ({
  listOfFunctions,
  workerOptions,
  lock,
  returnLock,
  hasAborted,
  now
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
  const IDX_FLAGS = 0 /* FlagsToHost */;
  const FLAG_REJECT = 1 /* Reject */;
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
  const resolvedShift = resolved.shiftNoClear.bind(resolved);
  const enqueueLock = () => {
    if (!decode())
      return false;
    let task = resolvedShift();
    while (task) {
      task.resolve = PLACE_HOLDER;
      task.reject = PLACE_HOLDER;
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
    hasAnythingFinished--;
    recyclePush(slot);
    return true;
  };
  const settleNow = (slot, isError, value, wasAwaited) => {
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
      while (toWork.size !== 0) {
        const slot = toWorkShift();
        try {
          const fnIndex = slot[0 /* FunctionID */] & FUNCTION_ID_MASK;
          const result = runByIndex[fnIndex](slot);
          slot[IDX_FLAGS] = 0;
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
    hasAwaiting: () => awaiting > 0,
    getAwaiting: () => awaiting
  };
};

// src/ipc/transport/shared-memory.ts
var page2 = 1024 * 4;
var CACHE_LINE_BYTES = 64;
var SIGNAL_OFFSETS = {
  op: 0,
  rxStatus: CACHE_LINE_BYTES,
  txStatus: CACHE_LINE_BYTES * 2
};
var a_store = Atomics.store;
var createSharedMemoryTransport = ({ sabObject, isMain, startTime }) => {
  const toGrow = sabObject?.size ?? page2;
  const roundedSize = toGrow + (page2 - toGrow % page2) % page2;
  const sab = sabObject?.sharedSab ? sabObject.sharedSab : createSharedArrayBuffer(roundedSize, page2 * page2);
  const startAt = startTime ?? performance.now();
  const opView = new Int32Array(sab, SIGNAL_OFFSETS.op, 1);
  if (isMain)
    a_store(opView, 0, 0);
  const rxStatus = new Int32Array(sab, SIGNAL_OFFSETS.rxStatus, 1);
  a_store(rxStatus, 0, 1);
  return {
    sab,
    op: opView,
    startAt,
    opView,
    rxStatus,
    txStatus: new Int32Array(sab, SIGNAL_OFFSETS.txStatus, 1)
  };
};

// src/common/task-symbol.ts
var endpointSymbol = Symbol.for("task");

// src/common/module-url.ts
import { pathToFileURL } from "node:url";
var WINDOWS_DRIVE_PATH = /^[A-Za-z]:[\\/]/;
var WINDOWS_UNC_PATH = /^\\\\[^\\/?]+\\[^\\/?]+/;
var encodeFilePath = (path) => encodeURI(path).replace(/\?/g, "%3F").replace(/#/g, "%23");
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
    return pathToFileURL(specifier).href;
  }
};

// src/worker/get-functions.ts
var normalizeTimeout = (timeout) => {
  if (timeout == null)
    return;
  if (typeof timeout === "number") {
    const ms2 = Math.floor(timeout);
    return ms2 >= 0 ? { ms: ms2, kind: 0 /* Reject */, value: new Error("Task timeout") } : undefined;
  }
  const ms = Math.floor(timeout.time);
  if (!(ms >= 0))
    return;
  if ("default" in timeout) {
    return { ms, kind: 1 /* Resolve */, value: timeout.default };
  }
  if (timeout.maybe === true) {
    return { ms, kind: 1 /* Resolve */, value: undefined };
  }
  if ("error" in timeout) {
    return { ms, kind: 0 /* Reject */, value: timeout.error };
  }
  return { ms, kind: 0 /* Reject */, value: new Error("Task timeout") };
};
var composeWorkerCallable = (fixed, _permission) => {
  return fixed.f;
};
var getFunctions = async ({ list, ids, at, permission }) => {
  const modules = list.map((specifier) => toModuleUrl(specifier));
  const results = await Promise.all(modules.map(async (imports) => {
    const module = await import(imports);
    return Object.entries(module).filter(([_, value]) => value != null && typeof value === "object" && value?.[endpointSymbol] === true).map(([name, value]) => ({
      ...value,
      name
    }));
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
var maybeGc = (() => {
  const host = globalThis;
  const gc = typeof host.gc === "function" ? host.gc.bind(globalThis) : undefined;
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
var a_pause = "pause" in Atomics ? Atomics.pause : undefined;
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
  write
}) => {
  const pause = pauseInNanoseconds !== undefined ? whilePausing({ pauseInNanoseconds }) : pauseGeneric;
  const tryProgress = () => {
    let progressed = false;
    if (enqueueLock())
      progressed = true;
    if (write) {
      const wrote = write();
      if (typeof wrote === "number") {
        if (wrote > 0)
          progressed = true;
      } else if (wrote === true) {
        progressed = true;
      }
    }
    return progressed;
  };
  return (value, spinMicroseconds, parkMs) => {
    const until = p_now2() + spinMicroseconds / 1000;
    maybeGc();
    let spinChecks = 0;
    while (true) {
      if (a_load(opView, at) !== value || txStatus[0 /* thisIsAHint */] === 1)
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
    a_wait(opView, at, value, parkMs ?? 60);
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
  if (typeof process === "undefined")
    return;
  const proc = process;
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
  if (typeof process === "undefined" || typeof process.on !== "function") {
    return;
  }
  const proc = process;
  if (proc.__knittingUnhandledRejectionSilencer === true)
    return;
  proc.__knittingUnhandledRejectionSilencer = true;
  process.on("unhandledRejection", () => {});
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
var hasLockBuffers = (value) => !!value?.headers && !!value?.lockSector && !!value?.payload && !!value?.payloadSector;
var assertWorkerSharedMemoryBootData = ({ sab, lock, returnLock }) => {
  if (!sab) {
    throw new Error("worker missing transport SAB");
  }
  if (!hasLockBuffers(lock)) {
    throw new Error("worker missing lock SABs");
  }
  if (!hasLockBuffers(returnLock)) {
    throw new Error("worker missing return lock SABs");
  }
};
var assertWorkerImportsResolved = ({ debug, list, ids, listOfFunctions }) => {
  if (debug?.logImportedUrl === true) {
    console.log(list);
  }
  if (listOfFunctions.length > 0)
    return;
  console.log(list);
  console.log(ids);
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
  const atomicView = new Uint32Array(sab);
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
  constructor(deferred, onSettle) {
    const settleOnce = (fn) => (...args) => {
      if (this.#triggered)
        return;
      this.#triggered = true;
      onSettle();
      fn(...args);
    };
    deferred.resolve = settleOnce(deferred.resolve);
    deferred.reject = settleOnce(deferred.reject);
    deferred.promise.reject = deferred.reject;
  }
}

// src/worker/loop.ts
var jsrIsGreatAndWorkWithoutBugs = () => null;
var WORKER_FATAL_MESSAGE_KEY = "__knittingWorkerFatal";
var reportWorkerStartupFatal = (error) => {
  const message = String(error?.message ?? error);
  const payload = {
    [WORKER_FATAL_MESSAGE_KEY]: message
  };
  try {
    parentPort?.postMessage(payload);
    return;
  } catch {}
  try {
    globalThis.postMessage?.(payload);
  } catch {}
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
    permission,
    totalNumberOfThread,
    list,
    ids,
    at
  } = startupData;
  scrubWorkerDataSensitiveBuffers(startupData);
  assertWorkerSharedMemoryBootData({ sab, lock, returnLock });
  var Comment;
  ((Comment2) => {
    Comment2[Comment2["thisIsAHint"] = 0] = "thisIsAHint";
  })(Comment ||= {});
  const signals = createSharedMemoryTransport({
    sabObject: {
      sharedSab: sab
    },
    isMain: false,
    thread,
    debug,
    startTime: startAt
  });
  const lockState = lock2({
    headers: lock.headers,
    LockBoundSector: lock.lockSector,
    payload: lock.payload,
    payloadSector: lock.payloadSector,
    payloadConfig
  });
  const returnLockState = lock2({
    headers: returnLock.headers,
    LockBoundSector: returnLock.lockSector,
    payload: returnLock.payload,
    payloadSector: returnLock.payloadSector,
    payloadConfig
  });
  const timers = workerOptions?.timers;
  const spinMicroseconds = timers?.spinMicroseconds ?? Math.max(1, totalNumberOfThread) * 50;
  const parkMs = timers?.parkMs ?? Math.max(1, totalNumberOfThread) * 50;
  const pauseSpin = (() => {
    const fn = typeof timers?.pauseNanoseconds === "number" ? whilePausing({ pauseInNanoseconds: timers.pauseNanoseconds }) : pauseGeneric;
    return () => fn();
  })();
  const { opView, rxStatus, txStatus } = signals;
  const a_store3 = Atomics.store;
  const a_load2 = Atomics.load;
  const listOfFunctions = await getFunctions({
    list,
    isWorker: true,
    ids,
    at,
    permission
  });
  assertWorkerImportsResolved({ debug, list, ids, listOfFunctions });
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
    getAwaiting
  } = createWorkerRxQueue({
    listOfFunctions,
    workerOptions,
    lock: lockState,
    returnLock: returnLockState,
    hasAborted: abortSignals?.hasAborted
  });
  a_store3(rxStatus, 0, 1);
  const WRITE_MAX = 64;
  const pauseUntil = sleepUntilChanged({
    opView,
    at: 0,
    rxStatus,
    txStatus,
    pauseInNanoseconds: timers?.pauseNanoseconds,
    enqueueLock,
    write: () => hasCompleted() ? writeBatch(WRITE_MAX) : 0
  });
  const channel = new MessageChannel;
  const port1 = channel.port1;
  const port2 = channel.port2;
  const post2 = port2.postMessage.bind(port2);
  let isInMacro = false;
  let awaitingSpins = 0;
  let lastAwaiting = 0;
  const MAX_AWAITING_MS = 10;
  let wakeSeq = a_load2(opView, 0);
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
  const _enqueueLock = enqueueLock;
  const _hasCompleted = hasCompleted;
  const _writeBatch = writeBatch;
  const _hasPending = hasPending;
  const _serviceBatchImmediate = serviceBatchImmediate;
  const _getAwaiting = getAwaiting;
  const _pauseSpin = pauseSpin;
  const _pauseUntil = pauseUntil;
  const loop = () => {
    isInMacro = false;
    let progressed = true;
    let awaiting = 0;
    while (true) {
      progressed = _enqueueLock();
      if (_hasCompleted()) {
        if (_writeBatch(WRITE_MAX) > 0)
          progressed = true;
      }
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
        if (txStatus[0 /* thisIsAHint */] === 1) {
          _pauseSpin();
          continue;
        }
        _pauseUntil(wakeSeq, spinMicroseconds, parkMs);
        wakeSeq = a_load2(opView, 0);
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
  scheduleMacro();
};
var isWebWorkerScope = () => {
  const scopeCtor = globalThis.WorkerGlobalScope;
  if (typeof scopeCtor !== "function")
    return false;
  try {
    return globalThis instanceof scopeCtor;
  } catch {
    return false;
  }
};
var isLockBuffers = (value) => {
  if (!value || typeof value !== "object")
    return false;
  const candidate = value;
  return candidate.headers instanceof SharedArrayBuffer && candidate.lockSector instanceof SharedArrayBuffer && candidate.payload instanceof SharedArrayBuffer && candidate.payloadSector instanceof SharedArrayBuffer;
};
var isWorkerBootPayload = (value) => {
  if (!value || typeof value !== "object")
    return false;
  const candidate = value;
  return candidate.sab instanceof SharedArrayBuffer && Array.isArray(candidate.list) && Array.isArray(candidate.ids) && Array.isArray(candidate.at) && typeof candidate.thread === "number" && typeof candidate.totalNumberOfThread === "number" && typeof candidate.startAt === "number" && isLockBuffers(candidate.lock) && isLockBuffers(candidate.returnLock);
};
var installWebWorkerBootstrap = () => {
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
if (isMainThread2 === false && isWorkerBootPayload(workerData)) {
  workerMainLoop(workerData).catch(reportWorkerStartupFatal);
} else if (isWebWorkerScope()) {
  installWebWorkerBootstrap();
}

// src/common/others.ts
var genTaskID = ((counter) => () => counter++)(0);
var INTERNAL_CALLER_HINTS = [
  "/src/common/others.ts",
  "\\src\\common\\others.ts",
  "/src/api.ts",
  "\\src\\api.ts"
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
var resolveCallerHref = (offset) => {
  const frames = collectStackFrames();
  const direct = frames[offset];
  const caller = (direct && !isInternalFrame(direct) ? direct.file : undefined) ?? frames.find((frame) => !isInternalFrame(frame))?.file ?? frames.find((frame) => !isRuntimeInternalFrame(frame.file))?.file;
  if (!caller) {
    throw new Error("Unable to determine caller file.");
  }
  return toModuleUrl(caller);
};
var linkingMap = new Map;
var getCallerFilePath = (offset = 3) => {
  const href = resolveCallerHref(offset);
  const at = linkingMap.get(href) ?? 0;
  linkingMap.set(href, at + 1);
  return [href, at];
};

// src/common/with-resolvers.ts
var withResolvers = () => {
  const native = Promise.withResolvers;
  if (typeof native === "function") {
    return native.call(Promise);
  }
  let resolve;
  let reject;
  const promise = new Promise((res, rej) => {
    resolve = res;
    reject = rej;
  });
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
  abortSignals,
  now
}) {
  const PLACE_HOLDER = (_) => {
    throw "UNREACHABLE FROM PLACE HOLDER (main)";
  };
  const newSlot = (id) => {
    const task = makeTask();
    task[1 /* ID */] = id;
    task[0 /* FunctionID */] = 0;
    task.value = undefined;
    task.resolve = PLACE_HOLDER;
    task.reject = PLACE_HOLDER;
    return task;
  };
  const initialSize = max ?? 10;
  const queue = Array.from({ length: initialSize }, (_, index) => newSlot(index));
  const freeSockets = Array.from({ length: initialSize }, (_, i) => i);
  const toBeSent = new RingQueue;
  const toBeSentPush = (task) => toBeSent.push(task);
  const toBeSentShift = () => toBeSent.shiftNoClear();
  const freePush = (id) => freeSockets.push(id);
  const freePop = () => freeSockets.pop();
  const queuePush = (task) => queue.push(task);
  const { encode, encodeManyFrom } = lock;
  let toBeSentCount = 0 | 0;
  let inUsed = 0 | 0;
  let pendingPromises = 0 | 0;
  const resetSignal = abortSignals?.resetSignal;
  const nowTime = now ?? p_now3;
  const isPromisePending = (task) => task[PromisePayloadMarker] === true;
  const resolveReturn = returnLock.resolveHost({
    queue,
    onResolved: (task) => {
      inUsed = inUsed - 1 | 0;
      freePush(task[1 /* ID */]);
    }
  });
  const hasPendingFrames = () => toBeSentCount > 0;
  const txIdle = () => toBeSentCount === 0 && inUsed === pendingPromises;
  const handleEncodeFailure = (task) => {
    if (isPromisePending(task)) {
      pendingPromises = pendingPromises + 1 | 0;
      return;
    }
    toBeSentPush(task);
    toBeSentCount = toBeSentCount + 1 | 0;
  };
  const rejectAll = (reason) => {
    for (let index = 0;index < queue.length; index++) {
      const slot = queue[index];
      if (slot.reject !== PLACE_HOLDER) {
        try {
          slot.reject(reason);
        } catch {}
        slot.resolve = PLACE_HOLDER;
        slot.reject = PLACE_HOLDER;
        queue[index] = newSlot(index);
      }
    }
    while (toBeSent.size > 0) {
      toBeSentShift();
    }
    toBeSentCount = 0 | 0;
    inUsed = 0 | 0;
    pendingPromises = 0 | 0;
  };
  const flushToWorker = () => {
    if (toBeSentCount === 0)
      return false;
    const encoded = encodeManyFrom(toBeSent) | 0;
    if (encoded === 0)
      return false;
    toBeSentCount = toBeSentCount - encoded | 0;
    return true;
  };
  const enqueueKnown = (task) => {
    if (!encode(task)) {
      handleEncodeFailure(task);
      return false;
    }
    return true;
  };
  return {
    rejectAll,
    hasPendingFrames,
    txIdle,
    completeFrame: resolveReturn,
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
        slot[0 /* FunctionID */] = functionIDMasked;
        if (USE_SIGNAL) {
          const maybeSignal = abortSignals.getSignal();
          if (maybeSignal === abortSignals.closeNow) {
            return Promise.reject(AbortSignalPoolExhausted);
          }
          new OneShotDeferred(deferred, () => resetSignal?.(maybeSignal));
          const encodedSignalMeta = (maybeSignal + ABORT_SIGNAL_META_OFFSET2 & FUNCTION_META_MASK) >>> 0;
          slot[0 /* FunctionID */] = (encodedSignalMeta << FUNCTION_META_SHIFT | functionIDMasked) >>> 0;
        }
        slot.value = rawArgs;
        slot[1 /* ID */] = index;
        slot.resolve = deferred.resolve;
        slot.reject = deferred.reject;
        if (HAS_TIMER) {
          slot[6 /* slotBuffer */] = (slot[6 /* slotBuffer */] & SLOT_INDEX_MASK | (nowTime() >>> 0 & SLOT_META_MASK) << SLOT_META_SHIFT >>> 0) >>> 0;
        }
        if (!encode(slot)) {
          handleEncodeFailure(slot);
        }
        inUsed = inUsed + 1 | 0;
        return deferred.promise;
      };
    },
    flushToWorker,
    enqueueKnown,
    settlePromisePayload: (task) => {
      if (task.reject === PLACE_HOLDER)
        return false;
      if (pendingPromises > 0)
        pendingPromises = pendingPromises - 1 | 0;
      const promiseStatus = task[PromisePayloadStatusSymbol];
      task[PromisePayloadStatusSymbol] = 0 /* Idle */;
      if (promiseStatus === 2 /* Rejected */) {
        try {
          task.reject(task.value);
        } catch {}
        inUsed = inUsed - 1 | 0;
        freePush(task[1 /* ID */]);
        return false;
      }
      return enqueueKnown(task);
    }
  };
}

// src/runtime/dispatcher.ts
import { MessageChannel as MessageChannel2 } from "node:worker_threads";
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
    txIdle
  },
  channelHandler,
  dispatcherOptions
}) => {
  const a_load2 = Atomics.load;
  const a_store3 = Atomics.store;
  const a_notify = Atomics.notify;
  const notify = channelHandler.notify.bind(channelHandler);
  let stallCount = 0 | 0;
  const STALL_FREE_LOOPS = Math.max(0, (dispatcherOptions?.stallFreeLoops ?? 128) | 0);
  const MAX_BACKOFF_MS = Math.max(0, (dispatcherOptions?.maxBackoffMs ?? 10) | 0);
  let backoffTimer;
  let inFlight = false;
  const check = () => {
    if (inFlight) {
      check.rerun = true;
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
        a_notify(opView, 0, 1);
      }
      let anyProgressed = false;
      let progressed = true;
      while (progressed) {
        progressed = false;
        if (completeFrame() > 0) {
          progressed = true;
          anyProgressed = true;
        }
        while (hasPendingFrames()) {
          if (!flushToWorker())
            break;
          progressed = true;
          anyProgressed = true;
        }
      }
      txStatus[0] = 0;
      if (!txIdle()) {
        if (anyProgressed || hasPendingFrames()) {
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
    if (stallCount <= STALL_FREE_LOOPS) {
      notify();
      return;
    }
    if (backoffTimer !== undefined)
      return;
    let delay = stallCount - STALL_FREE_LOOPS - 1 | 0;
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
  #post2;
  constructor() {
    this.channel = new MessageChannel2;
    this.port1 = this.channel.port1;
    this.port2 = this.channel.port2;
    this.#post2 = this.port2.postMessage.bind(this.port2);
  }
  notify() {
    this.#post2(null);
  }
  open(f) {
    const port1 = this.port1;
    if (typeof port1.on === "function") {
      port1.on("message", f);
    } else {
      port1.onmessage = f;
    }
    this.port1.start?.();
    this.port2.start?.();
  }
  close() {
    this.port1.onmessage = null;
    this.port2.onmessage = null;
    this.port1.close();
    this.port2.close();
  }
}

// src/runtime/pool.ts
import { Worker } from "node:worker_threads";
var poliWorker = Worker;
var WORKER_FATAL_MESSAGE_KEY2 = "__knittingWorkerFatal";
var execFlagKey = (flag) => flag.split("=", 1)[0];
var NODE_PERMISSION_EXEC_FLAGS = new Set([
  "--permission",
  "--experimental-permission",
  "--allow-fs-read",
  "--allow-fs-write",
  "--allow-worker",
  "--allow-child-process",
  "--allow-addons",
  "--allow-wasi"
]);
var NODE_WORKER_SAFE_EXEC_FLAGS = new Set([
  "--experimental-transform-types",
  "--expose-gc",
  "--no-warnings",
  ...NODE_PERMISSION_EXEC_FLAGS
]);
var isWorkerFatalMessage = (value) => !!value && typeof value === "object" && typeof value[WORKER_FATAL_MESSAGE_KEY2] === "string";
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
var toPositiveInteger2 = (value) => {
  if (!Number.isFinite(value))
    return;
  const int = Math.floor(value);
  return int > 0 ? int : undefined;
};
var toNodeWorkerResourceLimits = (limits) => {
  if (!limits)
    return;
  const out = {
    maxOldGenerationSizeMb: toPositiveInteger2(limits.maxOldGenerationSizeMb),
    maxYoungGenerationSizeMb: toPositiveInteger2(limits.maxYoungGenerationSizeMb),
    codeRangeSizeMb: toPositiveInteger2(limits.codeRangeSizeMb),
    stackSizeMb: toPositiveInteger2(limits.stackSizeMb)
  };
  return Object.values(out).some((value) => value !== undefined) ? out : undefined;
};
var terminateWorkerQuietly = (worker) => {
  try {
    Promise.resolve(worker.terminate()).catch(() => {});
  } catch {}
};
var spawnWorkerContext = ({
  list,
  ids,
  sab,
  thread,
  debug,
  totalNumberOfThread,
  source,
  at,
  workerOptions,
  workerExecArgv,
  permission,
  host,
  payload,
  payloadInitialBytes,
  payloadMaxBytes,
  bufferMode,
  maxPayloadBytes,
  abortSignalCapacity,
  usesAbortSignal
}) => {
  const tsFileUrl = new URL(import.meta.url);
  if (debug?.logHref === true) {
    console.log(tsFileUrl);
    jsrIsGreatAndWorkWithoutBugs();
  }
  const sanitizeBytes = (value) => {
    if (!Number.isFinite(value))
      return;
    const bytes = Math.floor(value);
    return bytes > 0 ? bytes : undefined;
  };
  const resolvedPayloadConfig = resolvePayloadBufferOptions({
    options: {
      ...payload,
      mode: payload?.mode ?? bufferMode,
      maxPayloadBytes: payload?.maxPayloadBytes ?? maxPayloadBytes,
      payloadInitialBytes: payload?.payloadInitialBytes ?? sanitizeBytes(payloadInitialBytes),
      payloadMaxByteLength: payload?.payloadMaxByteLength ?? sanitizeBytes(payloadMaxBytes)
    }
  });
  const makePayloadBuffer = () => resolvedPayloadConfig.mode === "growable" ? createSharedArrayBuffer(resolvedPayloadConfig.payloadInitialBytes, resolvedPayloadConfig.payloadMaxByteLength) : createSharedArrayBuffer(resolvedPayloadConfig.payloadInitialBytes);
  const defaultAbortSignalCapacity = 258;
  const requestedAbortSignalCapacity = sanitizeBytes(abortSignalCapacity);
  const resolvedAbortSignalCapacity = requestedAbortSignalCapacity ?? defaultAbortSignalCapacity;
  const makeLockBuffers = () => {
    const lockSector = new SharedArrayBuffer(LOCK_SECTOR_BYTE_LENGTH);
    return {
      headers: new SharedArrayBuffer(HEADER_BYTE_LENGTH),
      lockSector,
      payload: makePayloadBuffer(),
      payloadSector: lockSector
    };
  };
  const lockBuffers = makeLockBuffers();
  const returnLockBuffers = makeLockBuffers();
  const lock = lock2({
    headers: lockBuffers.headers,
    LockBoundSector: lockBuffers.lockSector,
    payload: lockBuffers.payload,
    payloadSector: lockBuffers.payloadSector,
    payloadConfig: resolvedPayloadConfig
  });
  const returnLock = lock2({
    headers: returnLockBuffers.headers,
    LockBoundSector: returnLockBuffers.lockSector,
    payload: returnLockBuffers.payload,
    payloadSector: returnLockBuffers.payloadSector,
    payloadConfig: resolvedPayloadConfig
  });
  const abortSignalWords = Math.max(1, Math.ceil(resolvedAbortSignalCapacity / 32));
  const abortSignalSAB = usesAbortSignal === true ? new SharedArrayBuffer(Uint32Array.BYTES_PER_ELEMENT * abortSignalWords) : undefined;
  const abortSignals = abortSignalSAB ? signalAbortFactory({
    sab: abortSignalSAB,
    maxSignals: resolvedAbortSignalCapacity
  }) : undefined;
  const signals = createSharedMemoryTransport({
    sabObject: sab,
    isMain: true,
    thread,
    debug
  });
  const signalBox = signals;
  const queue = createHostTxQueue({
    lock,
    returnLock,
    abortSignals
  });
  const {
    enqueue,
    rejectAll,
    txIdle
  } = queue;
  const channelHandler = new ChannelHandler;
  const { check } = hostDispatcherLoop({
    signalBox,
    queue,
    channelHandler,
    dispatcherOptions: host
  });
  channelHandler.open(check);
  let worker;
  const workerUrl = source ?? tsFileUrl;
  const workerDataPayload = {
    sab: signals.sab,
    abortSignalSAB,
    abortSignalMax: usesAbortSignal === true ? resolvedAbortSignalCapacity : undefined,
    list,
    ids,
    at,
    thread,
    debug,
    workerOptions,
    totalNumberOfThread,
    startAt: signalBox.startAt,
    lock: lockBuffers,
    returnLock: returnLockBuffers,
    payloadConfig: resolvedPayloadConfig,
    permission
  };
  const baseWorkerOptions = {
    type: "module",
    workerData: workerDataPayload
  };
  const nodeResourceLimits = toNodeWorkerResourceLimits(workerOptions?.resourceLimits);
  const baseNodeWorkerOptions = nodeResourceLimits ? { ...baseWorkerOptions, resourceLimits: nodeResourceLimits } : baseWorkerOptions;
  const withExecArgv = workerExecArgv && workerExecArgv.length > 0 ? { ...baseNodeWorkerOptions, execArgv: workerExecArgv } : baseNodeWorkerOptions;
  try {
    worker = new poliWorker(workerUrl, withExecArgv);
  } catch (error) {
    if (error?.code === "ERR_WORKER_INVALID_EXEC_ARGV") {
      const fallbackExecArgv = toWorkerSafeExecArgv(withExecArgv.execArgv);
      if (fallbackExecArgv && fallbackExecArgv.length > 0) {
        try {
          worker = new poliWorker(workerUrl, { ...baseNodeWorkerOptions, execArgv: fallbackExecArgv });
        } catch (fallbackError) {
          if (fallbackError?.code === "ERR_WORKER_INVALID_EXEC_ARGV") {
            const compatExecArgv = toWorkerCompatExecArgv(fallbackExecArgv);
            if (compatExecArgv && compatExecArgv.length > 0) {
              try {
                worker = new poliWorker(workerUrl, { ...baseNodeWorkerOptions, execArgv: compatExecArgv });
              } catch {
                worker = new poliWorker(workerUrl, baseNodeWorkerOptions);
              }
            } else {
              worker = new poliWorker(workerUrl, baseNodeWorkerOptions);
            }
          } else {
            throw fallbackError;
          }
        }
      } else {
        worker = new poliWorker(workerUrl, baseNodeWorkerOptions);
      }
    } else {
      throw error;
    }
  }
  let closedReason;
  const markWorkerClosed = (reason) => {
    if (closedReason)
      return;
    closedReason = reason;
    rejectAll(reason);
    channelHandler.close();
  };
  const nodeWorker = worker;
  nodeWorker.on?.("message", (message) => {
    if (!isWorkerFatalMessage(message))
      return;
    markWorkerClosed(`Worker startup failed: ${message[WORKER_FATAL_MESSAGE_KEY2]}`);
    terminateWorkerQuietly(worker);
  });
  nodeWorker.on?.("error", (error) => {
    const message = String(error?.message ?? error);
    markWorkerClosed(`Worker crashed: ${message}`);
  });
  nodeWorker.on?.("exit", (code) => {
    if (typeof code === "number" && code === 0)
      return;
    const normalized = typeof code === "number" ? code : -1;
    markWorkerClosed(`Worker exited with code ${normalized}`);
  });
  const thisSignal = signalBox.opView;
  const a_add = Atomics.add;
  const a_load2 = Atomics.load;
  const a_notify = Atomics.notify;
  const send = () => {
    if (check.isRunning === true)
      return;
    check.isRunning = true;
    Promise.resolve().then(check);
    if (a_load2(signalBox.rxStatus, 0) === 0) {
      a_add(thisSignal, 0, 1);
      a_notify(thisSignal, 0, 1);
    }
  };
  lock.setPromiseHandler((task) => {
    queue.settlePromisePayload(task);
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
      markWorkerClosed("Thread closed");
      try {
        Promise.resolve(worker.terminate()).catch(() => {});
      } catch {}
    },
    lock
  };
  return context;
};

// src/api.ts
import { isMainThread as isMainThread3, workerData as workerData2 } from "node:worker_threads";

// src/permission/protocol.ts
import path2 from "node:path";
import { existsSync, realpathSync } from "node:fs";
import { fileURLToPath } from "node:url";

// src/common/path-canonical.ts
import path from "node:path";
var toCanonicalPath = (candidate, fsApi = {}) => {
  const absolute = path.resolve(candidate);
  const { existsSync, realpathSync } = fsApi;
  if (typeof realpathSync === "function") {
    try {
      return path.resolve(realpathSync(absolute));
    } catch {}
  } else {
    return absolute;
  }
  if (typeof existsSync !== "function")
    return absolute;
  const missingSegments = [];
  let cursor = absolute;
  while (!existsSync(cursor)) {
    const parent = path.dirname(cursor);
    if (parent === cursor)
      return absolute;
    missingSegments.push(path.basename(cursor));
    cursor = parent;
  }
  let base = cursor;
  try {
    base = realpathSync(cursor);
  } catch {}
  let rebuilt = base;
  for (let i = missingSegments.length - 1;i >= 0; i--) {
    rebuilt = path.join(rebuilt, missingSegments[i]);
  }
  return path.resolve(rebuilt);
};

// src/permission/protocol.ts
var DEFAULT_ENV_FILE = ".env";
var DEFAULT_DENO_LOCK_FILE = "deno.lock";
var NODE_MODULES_DIR = "node_modules";
var DEFAULT_DENY_RELATIVE = [
  ".env",
  ".git",
  ".npmrc",
  ".docker",
  ".secrets"
];
var DEFAULT_ALLOW_IMPORT_HOSTS = ["deno.land", "esm.sh", "jsr.io"];
var SUPPORTED_SYS_API_NAMES = [
  "hostname",
  "osRelease",
  "osUptime",
  "loadavg",
  "networkInterfaces",
  "systemMemoryInfo",
  "uid",
  "gid"
];
var SUPPORTED_SYS_API_NAME_SET = new Set(SUPPORTED_SYS_API_NAMES);
var L3_KEYS = {
  deno: [],
  node: [
    "denyRead",
    "denyWrite",
    "net",
    "denyNet",
    "env.allow",
    "env.deny",
    "denyRun",
    "denyFfi",
    "sys",
    "denySys",
    "allowImport"
  ]
};
var cloneL3Keys = () => ({
  deno: [...L3_KEYS.deno],
  node: [...L3_KEYS.node]
});
var DEFAULT_DENY_HOME = [
  ".ssh",
  ".gnupg",
  ".aws",
  ".azure",
  ".config/gcloud",
  ".kube"
];
var DEFAULT_DENY_ABSOLUTE_POSIX = [
  "/proc",
  "/proc/self",
  "/proc/self/environ",
  "/proc/self/mem",
  "/sys",
  "/dev",
  "/etc"
];
var normalizeList = (values) => {
  const out = [];
  const seen = new Set;
  for (const value of values) {
    if (seen.has(value))
      continue;
    seen.add(value);
    out.push(value);
  }
  return out;
};
var normalizeStringList = (values) => {
  if (!values || values.length === 0)
    return [];
  const cleaned = [];
  for (const value of values) {
    if (typeof value !== "string")
      continue;
    const trimmed = value.trim();
    if (trimmed.length === 0)
      continue;
    cleaned.push(trimmed);
  }
  return normalizeList(cleaned);
};
var normalizeSysApiList = (values) => {
  if (!values || values.length === 0)
    return [];
  const out = [];
  const seen = new Set;
  for (const raw of values) {
    if (typeof raw !== "string")
      continue;
    const value = raw.trim();
    if (value.length === 0 || seen.has(value))
      continue;
    if (!SUPPORTED_SYS_API_NAME_SET.has(value))
      continue;
    seen.add(value);
    out.push(value);
  }
  return out;
};
var hasOwn = (value, key) => Object.prototype.hasOwnProperty.call(value, key);
var normalizeProtocolInput = (input) => !input ? undefined : typeof input === "string" ? { mode: input } : input;
var isWindows = () => {
  if (typeof process !== "undefined")
    return process.platform === "win32";
  const g = globalThis;
  return g.Deno?.build?.os === "windows";
};
var getCwd = () => {
  try {
    if (typeof process !== "undefined" && typeof process.cwd === "function") {
      return process.cwd();
    }
  } catch {}
  const g = globalThis;
  try {
    if (typeof g.Deno?.cwd === "function")
      return g.Deno.cwd();
  } catch {}
  return ".";
};
var getHome = () => {
  try {
    if (typeof process !== "undefined" && typeof process.env === "object") {
      const home = process.env.HOME ?? process.env.USERPROFILE;
      if (typeof home === "string" && home.length > 0)
        return home;
    }
  } catch {}
  const g = globalThis;
  try {
    const home = g.Deno?.env?.get?.("HOME") ?? g.Deno?.env?.get?.("USERPROFILE");
    if (typeof home === "string" && home.length > 0)
      return home;
  } catch {}
  return;
};
var expandHomePath = (value, home) => {
  if (!home)
    return value;
  if (value === "~")
    return home;
  if (value.startsWith("~/") || value.startsWith("~\\")) {
    return path2.resolve(home, value.slice(2));
  }
  return value;
};
var toAbsolutePath = (value, cwd, home) => {
  if (value instanceof URL) {
    if (value.protocol !== "file:")
      return;
    return path2.resolve(fileURLToPath(value));
  }
  const expanded = expandHomePath(value, home);
  if (path2.isAbsolute(expanded)) {
    return path2.resolve(expanded);
  }
  try {
    const parsed = new URL(expanded);
    if (parsed.protocol !== "file:")
      return;
    return path2.resolve(fileURLToPath(parsed));
  } catch {
    return path2.resolve(cwd, expanded);
  }
};
var toPath = (value, cwd, home) => value == null ? undefined : toAbsolutePath(value, cwd, home);
var toPathList = (values, cwd, home) => {
  if (!values?.length)
    return [];
  const out = [];
  for (const value of values) {
    const resolved = toPath(value, cwd, home);
    if (resolved)
      out.push(resolved);
  }
  return out;
};
var toUniquePathList = (values, cwd, home) => normalizeList(toPathList(values, cwd, home));
var toEnvFiles = (input, cwd, home) => {
  const values = Array.isArray(input) ? input : input ? [input] : [DEFAULT_ENV_FILE];
  return toUniquePathList(values, cwd, home);
};
var rawRealpathSync = realpathSync.native ?? realpathSync;
var toCanonicalPath2 = (candidate) => {
  return toCanonicalPath(candidate, {
    existsSync,
    realpathSync: rawRealpathSync
  });
};
var isPathWithin = (base, candidate) => {
  const canonicalBase = toCanonicalPath2(base);
  const canonicalCandidate = toCanonicalPath2(candidate);
  const relative = path2.relative(canonicalBase, canonicalCandidate);
  return relative === "" || !relative.startsWith("..") && !path2.isAbsolute(relative);
};
var defaultSensitiveProjectAndHomePaths = (cwd, home) => {
  const projectSensitive = DEFAULT_DENY_RELATIVE.map((entry) => path2.resolve(cwd, entry));
  const homeSensitive = home ? DEFAULT_DENY_HOME.map((entry) => path2.resolve(home, entry)) : [];
  return normalizeList([...projectSensitive, ...homeSensitive]);
};
var defaultSensitiveReadDenyPaths = (cwd, home) => {
  const projectAndHome = defaultSensitiveProjectAndHomePaths(cwd, home);
  const osSensitive = isWindows() ? [] : DEFAULT_DENY_ABSOLUTE_POSIX.map((entry) => path2.resolve(entry));
  return normalizeList([...projectAndHome, ...osSensitive]);
};
var collectWritePaths = (cwd, values) => {
  const out = normalizeList(values.length > 0 ? values : [cwd]);
  if (!out.some((entry) => isPathWithin(entry, cwd) || isPathWithin(cwd, entry))) {
    out.unshift(cwd);
  }
  return normalizeList(out);
};
var collectReadPaths = ({
  cwd,
  read,
  moduleFiles,
  envFiles,
  denoLock
}) => {
  const out = [
    cwd,
    path2.resolve(cwd, NODE_MODULES_DIR),
    ...read,
    ...moduleFiles,
    ...envFiles
  ];
  if (denoLock)
    out.push(denoLock);
  return normalizeList(out);
};
var resolveDenoLock = (input, cwd, home) => {
  if (input === false)
    return;
  if (input && input !== true) {
    return toPath(input, cwd, home);
  }
  return path2.resolve(cwd, DEFAULT_DENO_LOCK_FILE);
};
var resolveNodePermissionActivationFlag = () => {
  try {
    if (typeof process !== "undefined") {
      const raw = process.versions?.node;
      const major = Number.parseInt(String(raw).split(".", 1)[0] ?? "", 10);
      if (Number.isFinite(major) && major > 0 && major < 22) {
        return "--experimental-permission";
      }
    }
  } catch {}
  return "--permission";
};
var toNodeFlags = ({
  read,
  readAll,
  write,
  writeAll,
  envFiles,
  node
}) => {
  const modelFlags = [];
  if (readAll) {
    modelFlags.push("--allow-fs-read=*");
  } else if (read.length > 0) {
    modelFlags.push(`--allow-fs-read=${read.join(",")}`);
  }
  if (writeAll) {
    modelFlags.push("--allow-fs-write=*");
  } else if (write.length > 0) {
    modelFlags.push(`--allow-fs-write=${write.join(",")}`);
  }
  if (node.allowWorker)
    modelFlags.push("--allow-worker");
  if (node.allowChildProcess)
    modelFlags.push("--allow-child-process");
  if (node.allowAddons)
    modelFlags.push("--allow-addons");
  if (node.allowWasi)
    modelFlags.push("--allow-wasi");
  const flags = [];
  if (modelFlags.length > 0) {
    flags.push(resolveNodePermissionActivationFlag(), ...modelFlags);
  }
  for (const file of envFiles) {
    flags.push(`--env-file-if-exists=${file}`);
  }
  return flags;
};
var toDenoFlags = ({
  read,
  readAll,
  write,
  writeAll,
  denyRead,
  denyWrite,
  net,
  netAll,
  denyNet,
  allowImport,
  allowImportAll,
  envAllow,
  envAllowAll,
  envDeny,
  envFiles,
  run,
  runAll,
  denyRun,
  ffi,
  ffiAll,
  denyFfi,
  sys,
  sysAll,
  denySys,
  denoLock,
  denoLockEnabled,
  frozen
}) => {
  const flags = [];
  if (readAll) {
    flags.push("--allow-read");
  } else if (read.length > 0) {
    flags.push(`--allow-read=${read.join(",")}`);
  }
  if (writeAll) {
    flags.push("--allow-write");
  } else if (write.length > 0) {
    flags.push(`--allow-write=${write.join(",")}`);
  }
  if (denyRead.length > 0) {
    flags.push(`--deny-read=${denyRead.join(",")}`);
  }
  if (denyWrite.length > 0) {
    flags.push(`--deny-write=${denyWrite.join(",")}`);
  }
  if (netAll) {
    flags.push("--allow-net");
  } else if (net.length > 0) {
    flags.push(`--allow-net=${net.join(",")}`);
  }
  if (denyNet.length > 0) {
    flags.push(`--deny-net=${denyNet.join(",")}`);
  }
  if (allowImportAll) {
    flags.push("--allow-import");
  } else if (allowImport.length > 0) {
    flags.push(`--allow-import=${allowImport.join(",")}`);
  }
  if (envAllowAll) {
    flags.push("--allow-env");
  } else if (envAllow.length > 0) {
    flags.push(`--allow-env=${envAllow.join(",")}`);
  }
  if (envDeny.length > 0) {
    flags.push(`--deny-env=${envDeny.join(",")}`);
  }
  for (const file of envFiles) {
    flags.push(`--env-file=${file}`);
  }
  if (runAll) {
    flags.push("--allow-run");
  } else if (run.length > 0) {
    flags.push(`--allow-run=${run.join(",")}`);
  }
  if (denyRun.length > 0) {
    flags.push(`--deny-run=${denyRun.join(",")}`);
  }
  if (ffiAll) {
    flags.push("--allow-ffi");
  } else if (ffi.length > 0) {
    flags.push(`--allow-ffi=${ffi.join(",")}`);
  }
  if (denyFfi.length > 0) {
    flags.push(`--deny-ffi=${denyFfi.join(",")}`);
  }
  if (sysAll) {
    flags.push("--allow-sys");
  } else if (sys.length > 0) {
    flags.push(`--allow-sys=${sys.join(",")}`);
  }
  if (denySys.length > 0) {
    flags.push(`--deny-sys=${denySys.join(",")}`);
  }
  if (!denoLockEnabled) {
    flags.push("--no-lock");
  } else if (denoLock) {
    flags.push(`--lock=${denoLock}`);
    if (frozen)
      flags.push("--frozen=true");
  }
  return flags;
};
var resolvePermissionProtocol = ({
  permission,
  modules
}) => {
  const input = normalizeProtocolInput(permission);
  if (!input)
    return;
  const rawMode = input.mode;
  const mode = rawMode === "unsafe" || rawMode === "off" ? "unsafe" : rawMode === "custom" ? "custom" : "strict";
  const unsafe = mode === "unsafe";
  const allowConsole = input.console ?? unsafe;
  const cwd = path2.resolve(input.cwd ?? getCwd());
  const home = getHome();
  const envFiles = toEnvFiles(input.env?.files, cwd, home);
  const moduleFiles = toUniquePathList(modules, cwd, home);
  const denoLockInput = input.deno?.lock;
  const denoLockEnabled = denoLockInput !== false;
  const denoLock = resolveDenoLock(denoLockInput, cwd, home);
  if (unsafe) {
    return {
      enabled: true,
      mode,
      unsafe: true,
      allowConsole,
      cwd,
      read: [],
      readAll: true,
      write: [],
      writeAll: true,
      denyRead: [],
      denyWrite: [],
      net: [],
      netAll: true,
      denyNet: [],
      allowImport: [],
      allowImportAll: true,
      env: {
        allow: [],
        allowAll: true,
        deny: [],
        files: envFiles
      },
      envFiles,
      run: [],
      runAll: true,
      denyRun: [],
      workers: true,
      ffi: [],
      ffiAll: true,
      denyFfi: [],
      sys: [],
      sysAll: true,
      denySys: [],
      wasi: true,
      lockFiles: {
        deno: denoLock
      },
      node: {
        allowWorker: true,
        allowChildProcess: true,
        allowAddons: true,
        allowWasi: true,
        flags: []
      },
      deno: {
        frozen: false,
        allowRun: true,
        flags: []
      },
      l3: cloneL3Keys()
    };
  }
  const nodeModulesPath = path2.resolve(cwd, NODE_MODULES_DIR);
  const hasExplicitDenyRead = hasOwn(input, "denyRead");
  const hasExplicitDenyWrite = hasOwn(input, "denyWrite");
  const hasExplicitRead = hasOwn(input, "read");
  const hasExplicitWrite = hasOwn(input, "write");
  const denyReadDefaults = defaultSensitiveReadDenyPaths(cwd, home);
  const denyWriteDefaults = normalizeList([
    ...defaultSensitiveProjectAndHomePaths(cwd, home),
    nodeModulesPath
  ]);
  const denyRead = normalizeList([
    ...toPathList(input.denyRead, cwd, home),
    ...mode === "custom" && hasExplicitDenyRead ? [] : denyReadDefaults
  ]);
  const denyWrite = normalizeList([
    ...toPathList(input.denyWrite, cwd, home),
    ...mode === "custom" && hasExplicitDenyWrite ? [] : denyWriteDefaults
  ]);
  const readAll = input.read === true;
  const writeAll = input.write === true;
  const configuredRead = readAll ? [] : toPathList(Array.isArray(input.read) ? input.read : undefined, cwd, home);
  const configuredWrite = writeAll ? [] : toPathList(Array.isArray(input.write) ? input.write : undefined, cwd, home);
  const resolvedRead = readAll ? [] : hasExplicitRead ? normalizeList(configuredRead) : collectReadPaths({
    cwd,
    read: configuredRead,
    moduleFiles,
    envFiles,
    denoLock
  });
  const resolvedWrite = writeAll ? [] : hasExplicitWrite ? normalizeList(configuredWrite) : collectWritePaths(cwd, configuredWrite);
  const netAll = input.net === true;
  const net = netAll ? [] : normalizeStringList(Array.isArray(input.net) ? input.net : []);
  const denyNet = normalizeStringList(input.denyNet);
  const allowImportAll = input.allowImport === true;
  const allowImport = allowImportAll ? [] : normalizeStringList(Array.isArray(input.allowImport) ? input.allowImport : [...DEFAULT_ALLOW_IMPORT_HOSTS]);
  const envAllowAll = input.env?.allow === true;
  const envAllow = envAllowAll ? [] : normalizeStringList(Array.isArray(input.env?.allow) ? input.env.allow : []);
  const envDeny = normalizeStringList(input.env?.deny);
  const legacyRunEnabled = input.node?.allowChildProcess === true || input.deno?.allowRun === true;
  const runSource = hasOwn(input, "run") ? input.run : legacyRunEnabled ? true : [];
  const runAll = runSource === true;
  const run = runAll ? [] : normalizeStringList(Array.isArray(runSource) ? runSource : []);
  const denyRun = normalizeStringList(input.denyRun);
  const workers = hasOwn(input, "workers") ? input.workers === true : input.node?.allowWorker === true;
  const ffiSource = hasOwn(input, "ffi") ? input.ffi : input.node?.allowAddons === true ? true : false;
  const ffiAll = ffiSource === true;
  const ffi = ffiAll ? [] : toUniquePathList(Array.isArray(ffiSource) ? ffiSource : undefined, cwd, home);
  const denyFfi = toUniquePathList(input.denyFfi, cwd, home);
  const sysSource = input.sys;
  const sysAll = sysSource === true;
  const sys = sysAll ? [] : normalizeSysApiList(Array.isArray(sysSource) ? sysSource : []);
  const denySys = normalizeSysApiList(input.denySys);
  const wasi = hasOwn(input, "wasi") ? input.wasi === true : input.node?.allowWasi === true;
  const nodeSettings = {
    allowWorker: workers,
    allowChildProcess: runAll || run.length > 0,
    allowAddons: ffiAll || ffi.length > 0,
    allowWasi: wasi
  };
  const denoSettings = {
    frozen: input.deno?.frozen !== false,
    allowRun: runAll || run.length > 0
  };
  return {
    enabled: true,
    mode,
    unsafe: false,
    allowConsole,
    cwd,
    read: resolvedRead,
    readAll,
    write: resolvedWrite,
    writeAll,
    denyRead,
    denyWrite,
    net,
    netAll,
    denyNet,
    allowImport,
    allowImportAll,
    env: {
      allow: envAllow,
      allowAll: envAllowAll,
      deny: envDeny,
      files: envFiles
    },
    envFiles,
    run,
    runAll,
    denyRun,
    workers,
    ffi,
    ffiAll,
    denyFfi,
    sys,
    sysAll,
    denySys,
    wasi,
    lockFiles: {
      deno: denoLock
    },
    node: {
      ...nodeSettings,
      flags: toNodeFlags({
        read: resolvedRead,
        readAll,
        write: resolvedWrite,
        writeAll,
        envFiles,
        node: nodeSettings
      })
    },
    deno: {
      ...denoSettings,
      flags: toDenoFlags({
        read: resolvedRead,
        readAll,
        write: resolvedWrite,
        writeAll,
        denyRead,
        denyWrite,
        net,
        netAll,
        denyNet,
        allowImport,
        allowImportAll,
        envAllow,
        envAllowAll,
        envDeny,
        envFiles,
        run,
        runAll,
        denyRun,
        ffi,
        ffiAll,
        denyFfi,
        sys,
        sysAll,
        denySys,
        denoLock,
        denoLockEnabled,
        frozen: denoSettings.frozen
      })
    },
    l3: cloneL3Keys()
  };
};
var toRuntimePermissionFlags = (protocol) => protocol?.enabled === true && protocol.unsafe !== true ? RUNTIME === "node" ? protocol.node.flags : RUNTIME === "deno" ? protocol.deno.flags : [] : [];
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
import { MessageChannel as MessageChannel3 } from "node:worker_threads";
var normalizeTimeout2 = (timeout) => {
  if (timeout == null)
    return;
  if (typeof timeout === "number") {
    return timeout >= 0 ? { ms: timeout, kind: 0 /* Reject */, value: new Error("Task timeout") } : undefined;
  }
  const ms = timeout.time;
  if (!(ms >= 0))
    return;
  if ("default" in timeout) {
    return { ms, kind: 1 /* Resolve */, value: timeout.default };
  }
  if (timeout.maybe === true) {
    return { ms, kind: 1 /* Resolve */, value: undefined };
  }
  if ("error" in timeout) {
    return { ms, kind: 0 /* Reject */, value: timeout.error };
  }
  return { ms, kind: 0 /* Reject */, value: new Error("Task timeout") };
};
var raceTimeout2 = (promise, spec) => new Promise((resolve, reject) => {
  let done = false;
  const timer = setTimeout(() => {
    if (done)
      return;
    done = true;
    if (spec.kind === 1 /* Resolve */) {
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
  return {
    hasAborted
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
  const entries = Object.values(tasks).sort((a, b) => a.id - b.id);
  const runners = entries.map((entry) => composeInlineCallable(entry.f, entry.timeout, entry.abortSignal !== undefined));
  const initCap = 16;
  let fnByIndex = new Int32Array(initCap);
  let stateByIndex = new Int8Array(initCap).fill(-1 /* Free */);
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
  const channel = new MessageChannel3;
  const port1 = channel.port1;
  const port2 = channel.port2;
  const post2 = port2.postMessage.bind(port2);
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
    if (stateByIndex[index] !== 0 /* Pending */ || taskIdByIndex[index] !== taskID)
      return;
    enqueue(index);
  };
  const settleIfCurrent = (index, taskID, isError, value) => {
    if (stateByIndex[index] !== 0 /* Pending */ || taskIdByIndex[index] !== taskID)
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
    nextStateByIndex.fill(-1 /* Free */);
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
      if (stateByIndex[index] !== 0 /* Pending */)
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
    stateByIndex[index] = -1 /* Free */;
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
    stateByIndex[index] = 0 /* Pending */;
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
        if (stateByIndex[index] !== 0 /* Pending */)
          continue;
        try {
          deferredByIndex[index]?.reject("Thread closed");
        } catch {}
      }
      port1.onmessage = null;
      port1.close();
      port2.onmessage = null;
      port2.close();
      pendingQueue.clear();
      freeTop = 0;
      freeStack.length = 0;
      argsByIndex.fill(undefined);
      taskIdByIndex.fill(-1);
      deferredByIndex.fill(undefined);
      fnByIndex.fill(0);
      stateByIndex.fill(-1 /* Free */);
      working = 0;
      isInMacro = false;
      isInMicro = false;
    },
    call,
    txIdle: () => working === 0
  };
};

// src/api.ts
var MAX_FUNCTION_ID = 65535;
var MAX_FUNCTION_COUNT = MAX_FUNCTION_ID + 1;
var isMain = isMainThread3;
var toListAndIds = (args) => {
  const result = Object.values(args).reduce((acc, v) => (acc[0].add(v.importedFrom), acc[1].add(v.id), acc[2].add(v.at), acc), [
    new Set,
    new Set,
    new Set
  ]);
  return {
    list: [...result[0]],
    ids: [...result[1]],
    at: [...result[2]]
  };
};
var createPool = ({
  threads,
  debug,
  inliner,
  balancer,
  payload,
  payloadInitialBytes,
  payloadMaxBytes,
  bufferMode,
  maxPayloadBytes,
  abortSignalCapacity,
  source,
  worker,
  workerExecArgv,
  permission,
  dispatcher,
  host
}) => (tasks) => {
  if (isMainThread3 === false) {
    if (debug?.extras === true) {
      console.warn("createPool has been called with : " + JSON.stringify(workerData2));
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
      call: mainThreadOnlyProxy
    };
  }
  const { list, ids, at } = toListAndIds(tasks), listOfFunctions = Object.entries(tasks).map(([k, v]) => ({
    ...v,
    name: k
  })).sort((a, b) => a.name.localeCompare(b.name));
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
  const allowedFlags = typeof process !== "undefined" && process.allowedNodeEnvironmentFlags ? process.allowedNodeEnvironmentFlags : null;
  const isNodePermissionFlag = (flag) => {
    const key = flag.split("=", 1)[0];
    return key === "--permission" || key === "--experimental-permission" || key === "--allow-fs-read" || key === "--allow-fs-write" || key === "--allow-worker" || key === "--allow-child-process" || key === "--allow-addons" || key === "--allow-wasi";
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
  const defaultExecArgvCandidate = workerExecArgv ?? (typeof process !== "undefined" && Array.isArray(process.execArgv) ? allowedFlags?.has("--expose-gc") === true ? process.execArgv.includes("--expose-gc") ? process.execArgv : [...process.execArgv, "--expose-gc"] : process.execArgv : undefined);
  const defaultExecArgv = permissionProtocol?.unsafe === true ? stripNodePermissionFlags(defaultExecArgvCandidate) : defaultExecArgvCandidate;
  const combinedExecArgv = dedupeFlags([
    ...permissionExecArgv,
    ...defaultExecArgv ?? []
  ]);
  const execArgv = sanitizeExecArgv(combinedExecArgv.length > 0 ? combinedExecArgv : undefined);
  const hostDispatcher = host ?? dispatcher;
  const usesAbortSignal = listOfFunctions.some((fn) => fn.abortSignal !== undefined);
  const hardTimeoutMs = Number.isFinite(worker?.hardTimeoutMs) ? Math.max(1, Math.floor(worker?.hardTimeoutMs)) : undefined;
  let workers = Array.from({
    length: threads ?? 1
  }).map((_, thread) => spawnWorkerContext({
    list,
    ids,
    at,
    thread,
    debug,
    totalNumberOfThread,
    source,
    workerOptions: worker,
    workerExecArgv: execArgv,
    host: hostDispatcher,
    payload,
    payloadInitialBytes,
    payloadMaxBytes,
    bufferMode,
    maxPayloadBytes,
    abortSignalCapacity,
    usesAbortSignal,
    permission: permissionProtocol
  }));
  if (usingInliner) {
    const mainThread = createInlineExecutor({
      tasks,
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
      return;
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
  const indexedFunctions = listOfFunctions.map((fn, index) => ({
    name: fn.name,
    index,
    timeout: fn.timeout,
    abortSignal: fn.abortSignal
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
  const buildInvoker = (handlers) => useDirectHandler ? handlers[0] : managerMethod({
    contexts: workers,
    balancer,
    handlers,
    inlinerGate: usingInliner ? {
      index: inlinerIndex,
      threshold: inlinerDispatchThreshold
    } : undefined
  });
  const callEntries = Array.from(callHandlers.entries(), ([name, handlers]) => [name, buildInvoker(handlers)]);
  return {
    shutdown: shutdownWithDelay,
    call: Object.fromEntries(callEntries)
  };
};
var SINGLE_TASK_KEY = "__task__";
var DEFAULT_IMPORT_EXPORT_NAME = "default";
var createSingleTaskPool = (single, options) => {
  const pool = createPool(options ?? {})({
    [SINGLE_TASK_KEY]: single
  });
  return {
    call: pool.call[SINGLE_TASK_KEY],
    shutdown: pool.shutdown
  };
};
var buildTaskDefinitionFromCaller = (input, callerHref, at) => {
  const importedFrom = new URL(callerHref).href;
  const out = {
    ...input,
    id: genTaskID(),
    importedFrom,
    at,
    [endpointSymbol]: true
  };
  out.createPool = (options) => {
    if (isMainThread3 === false) {
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
var resolveImportHref = (href, callerHref) => {
  try {
    return new URL(href, callerHref).href;
  } catch {
    return toModuleUrl(href);
  }
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
  }, callerHref, at);
}
export {
  workerMainLoop,
  task,
  isMain,
  importTask,
  createPool,
  Envelope
};
