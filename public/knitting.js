// src/worker/loop.ts
import {
  isMainThread as isMainThread3,
  MessageChannel,
  workerData,
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
    while (cap < capacity) {
      cap <<= 1;
    }
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
    if (minCapacity <= this.capacity) {
      return;
    }
    let cap = this.capacity;
    while (cap < minCapacity) {
      cap <<= 1;
    }
    this.#growTo(cap);
  }
  #growIfFull() {
    if (this.#size !== this.#mask + 1) {
      return;
    }
    this.#growTo(this.#mask + 1 << 1);
  }
  #growTo(newCap) {
    const oldBuf = this.#buf;
    const oldCap = this.#mask + 1;
    const n = this.#size;
    const next = new Array(newCap).fill(null);
    const head = this.#head;
    const firstLen = Math.min(n, oldCap - head);
    for (let i = 0; i < firstLen; i++) {
      next[i] = oldBuf[head + i];
    }
    for (let i = firstLen; i < n; i++) {
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
    if (size === 0) {
      return;
    }
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
    if (size === 0) {
      return;
    }
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
      if (v !== null) {
        yield v;
      }
      idx = idx + 1 & mask;
      i++;
    }
  }
  toArray() {
    const out = new Array(this.#size);
    const buf = this.#buf;
    const mask = this.#mask;
    let idx = this.#head;
    for (let i = 0; i < out.length; i++) {
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
var register = ({ lockSector }) => {
  const lockSAB = lockSector ?? new SharedArrayBuffer(LOCK_SECTOR_BYTE_LENGTH);
  const hostBits = new Int32Array(lockSAB, LOCK_HOST_BITS_OFFSET_BYTES, 1);
  const workerBits = new Int32Array(lockSAB, LOCK_WORKER_BITS_OFFSET_BYTES, 1);
  const startAndIndex = new Uint32Array(32 /* slots */);
  const size64bit = new Uint32Array(32 /* slots */);
  const a_load = Atomics.load;
  const a_store = Atomics.store;
  const saiCopyWithin = startAndIndex.copyWithin.bind(startAndIndex);
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
  const startAndIndexToArray = (length) =>
    Array.from(startAndIndex.subarray(0, length));
  const compactSectorStable = (b) => {
    const sai = startAndIndex;
    let w = 0 | 0;
    let r = 0 | 0;
    b = b | 0;
    for (; r + 3 < b; r += 4) {
      const v0 = sai[r];
      const v1 = sai[r + 1];
      const v2 = sai[r + 2];
      const v3 = sai[r + 3];
      if (v0 !== EMPTY) {
        sai[w++] = v0;
      }
      if (v1 !== EMPTY) {
        sai[w++] = v1;
      }
      if (v2 !== EMPTY) {
        sai[w++] = v2;
      }
      if (v3 !== EMPTY) {
        sai[w++] = v3;
      }
    }
    for (; r < b; r++) {
      const v = sai[r];
      if (v !== EMPTY) {
        sai[w++] = v;
      }
    }
    return w;
  };
  const updateTable = () => {
    const w = a_load(workerBits, 0) | 0;
    const state = (hostLast ^ w) >>> 0;
    let freeBits = ~state >>> 0;
    if (tableLength === 0 || freeBits === 0) {
      return;
    }
    if (freeBits === EMPTY) {
      tableLength = 0;
      usedBits = 0 | 0;
      return;
    }
    freeBits &= usedBits;
    if (freeBits === 0) {
      return;
    }
    const sai = startAndIndex;
    for (let i = 0; i < tableLength; i++) {
      const v = sai[i];
      if (v === EMPTY) {
        continue;
      }
      if ((freeBits & 1 << (v & SLOT_MASK)) !== 0) {
        sai[i] = EMPTY;
      }
    }
    usedBits &= ~freeBits;
    tableLength = compactSectorStable(tableLength);
  };
  const allocTask = (task) => {
    updateTableCounter = updateTableCounter + 1 & 3;
    if (updateTableCounter === 0) {
      updateTable();
    }
    const payloadLen = task[5 /* PayloadLen */] | 0;
    const size = payloadLen + 63 & ~63;
    const freeBits = ~usedBits >>> 0;
    const freeBit = (freeBits & -freeBits) >>> 0;
    if (freeBit === 0) {
      return -1;
    }
    if (tableLength >= 32 /* slots */) {
      return -1;
    }
    const slotIndex = 31 - clz32(freeBit);
    const sai = startAndIndex;
    const sz = size64bit;
    const tl = tableLength;
    if (tl === 0) {
      sai[0] = slotIndex;
      sz[slotIndex] = size;
      task[3 /* Start */] = 0;
      setTaskSlotIndex(task, slotIndex);
      tableLength = 1;
      usedBits |= freeBit;
      hostLast ^= freeBit;
      return a_store(hostBits, 0, hostLast);
    }
    const firstStart = sai[0] & START_MASK;
    if (firstStart >= size >>> 0) {
      saiCopyWithin(1, 0, tl);
      sai[0] = slotIndex;
      sz[slotIndex] = size;
      task[3 /* Start */] = 0;
      setTaskSlotIndex(task, slotIndex);
      tableLength = tl + 1;
      usedBits |= freeBit;
      hostLast ^= freeBit;
      return a_store(hostBits, 0, hostLast);
    }
    for (let at = 0; at + 1 < tl; at++) {
      const cur = sai[at];
      const curStart = cur & START_MASK;
      const curEnd = curStart + (sz[cur & SLOT_MASK] >>> 0) >>> 0;
      const nextStart = sai[at + 1] & START_MASK;
      if (nextStart - curEnd >>> 0 < size >>> 0) {
        continue;
      }
      saiCopyWithin(at + 2, at + 1, tl);
      sai[at + 1] = (curEnd | slotIndex) >>> 0;
      sz[slotIndex] = size;
      task[3 /* Start */] = curEnd;
      setTaskSlotIndex(task, slotIndex);
      tableLength = tl + 1;
      usedBits |= freeBit;
      hostLast ^= freeBit;
      return a_store(hostBits, 0, hostLast);
    }
    if (tl < 32 /* slots */) {
      const last = sai[tl - 1];
      const lastStart = last & START_MASK;
      const newStart = lastStart + (sz[last & SLOT_MASK] >>> 0) >>> 0;
      sai[tl] = (newStart | slotIndex) >>> 0;
      sz[slotIndex] = size;
      task[3 /* Start */] = newStart;
      setTaskSlotIndex(task, slotIndex);
      tableLength = tl + 1;
      usedBits |= freeBit;
      hostLast ^= freeBit;
      return a_store(hostBits, 0, hostLast);
    }
    return -1;
  };
  const setSlotLength = (slotIndex, payloadLen) => {
    slotIndex = slotIndex & TASK_SLOT_INDEX_MASK;
    const bit = 1 << slotIndex;
    if ((usedBits & bit) === 0) {
      return false;
    }
    const current = size64bit[slotIndex] >>> 0;
    const aligned = (payloadLen | 0) + 63 & ~63;
    if (aligned < 0) {
      return false;
    }
    if (aligned >>> 0 > current) {
      return false;
    }
    size64bit[slotIndex] = aligned >>> 0;
    return true;
  };
  const free = (index) => {
    index = index & TASK_SLOT_INDEX_MASK;
    workerLast ^= 1 << index;
    a_store(workerBits, 0, workerLast);
  };
  return {
    allocTask,
    setSlotLength,
    lockSAB,
    free,
    hostBits,
    workerBits,
    updateTable,
    startAndIndexToArray,
  };
};

// src/memory/createSharedBufferIO.ts
import { Buffer as NodeBuffer } from "node:buffer";

// src/common/runtime.ts
var globals = globalThis;
var IS_DENO = typeof globals.Deno?.version?.deno === "string";
var IS_BUN = typeof globals.Bun?.version === "string";
var IS_NODE = typeof process !== "undefined" &&
  typeof process.versions?.node === "string";
var RUNTIME = IS_DENO ? "deno" : IS_BUN ? "bun" : IS_NODE ? "node" : "unknown";
var SET_IMMEDIATE = typeof globals.setImmediate === "function"
  ? globals.setImmediate
  : undefined;
var HAS_SAB_GROW = typeof SharedArrayBuffer === "function" &&
  typeof SharedArrayBuffer.prototype.grow === "function";
var createSharedArrayBuffer = (byteLength, maxByteLength) => {
  if (HAS_SAB_GROW && typeof maxByteLength === "number") {
    return new SharedArrayBuffer(byteLength, { maxByteLength });
  }
  return new SharedArrayBuffer(byteLength);
};

// src/memory/createSharedBufferIO.ts
var page = 1024 * 4;
var textEncode = new TextEncoder();
var SignalEnumOptions;
((SignalEnumOptions2) => {
  SignalEnumOptions2[SignalEnumOptions2["header"] = 64] = "header";
  SignalEnumOptions2[SignalEnumOptions2["maxByteLength"] = page * page] =
    "maxByteLength";
  SignalEnumOptions2[SignalEnumOptions2["defaultSize"] = page] = "defaultSize";
  SignalEnumOptions2[SignalEnumOptions2["safePadding"] = page] = "safePadding";
})(SignalEnumOptions ||= {});
var alignUpto64 = (n) => n + (64 - 1) & ~(64 - 1);
var createSharedDynamicBufferIO = ({
  sab,
}) => {
  const maxBytes = 64 * 1024 * 1024;
  const initialBytes = HAS_SAB_GROW ? 4 * 1024 * 1024 : maxBytes;
  const lockSAB = sab ?? createSharedArrayBuffer(initialBytes, maxBytes);
  let u8 = new Uint8Array(lockSAB, 64 /* header */);
  const requireBufferView = (buffer) => {
    const view = NodeBuffer.from(buffer, 64 /* header */);
    if (view.buffer !== buffer) {
      throw new Error("Buffer view does not alias SharedArrayBuffer");
    }
    return view;
  };
  let buf = requireBufferView(lockSAB);
  let f64 = new Float64Array(lockSAB, 64 /* header */);
  const capacityBytes = () => lockSAB.byteLength - 64 /* header */;
  const ensureCapacity = (neededBytes) => {
    if (capacityBytes() >= neededBytes) {
      return true;
    }
    if (!HAS_SAB_GROW || typeof lockSAB.grow !== "function") {
      return false;
    }
    try {
      lockSAB.grow(
        alignUpto64(
          64 /* header */ + neededBytes + SignalEnumOptions.safePadding,
        ),
      );
    } catch {
      return false;
    }
    u8 = new Uint8Array(
      lockSAB,
      64, /* header */
      lockSAB.byteLength - 64, /* header */
    );
    buf = requireBufferView(lockSAB);
    f64 = new Float64Array(
      lockSAB,
      64, /* header */
      lockSAB.byteLength - 64 /* header */ >>> 3,
    );
    return true;
  };
  const readUtf8 = (start, end) => {
    return buf.toString("utf8", start, end);
  };
  const writeBinary = (src, start = 0) => {
    if (!ensureCapacity(start + src.byteLength)) {
      throw new RangeError("Shared buffer capacity exceeded");
    }
    u8.set(src, start);
    return src.byteLength;
  };
  const write8Binary = (src, start = 0) => {
    const bytes = src.byteLength;
    if (!ensureCapacity(start + bytes)) {
      throw new RangeError("Shared buffer capacity exceeded");
    }
    f64.set(src, start >>> 3);
    return bytes;
  };
  const readBytesCopy = (start, end) => u8.slice(start, end);
  const readBytesView = (start, end) => u8.subarray(start, end);
  const readBytesBufferCopy = (start, end) => {
    const length = Math.max(0, end - start | 0);
    const out = NodeBuffer.allocUnsafe(length);
    if (length === 0) {
      return out;
    }
    buf.copy(out, 0, start, end);
    return out;
  };
  const readBytesArrayBufferCopy = (start, end) => {
    const length = Math.max(0, end - start | 0);
    const out = new Uint8Array(length);
    if (length === 0) {
      return out.buffer;
    }
    buf.copy(out, 0, start, end);
    return out.buffer;
  };
  const read8BytesFloatCopy = (start, end) => f64.slice(start >>> 3, end >>> 3);
  const read8BytesFloatView = (start, end) =>
    f64.subarray(start >>> 3, end >>> 3);
  const writeUtf8 = (str, start, reservedBytes = str.length * 3) => {
    if (!ensureCapacity(start + reservedBytes)) {
      throw new RangeError("Shared buffer capacity exceeded");
    }
    const { read, written } = textEncode.encodeInto(
      str,
      u8.subarray(start, start + reservedBytes),
    );
    if (read !== str.length) {
      throw new RangeError("Shared buffer capacity exceeded");
    }
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
    writeUtf8,
  };
};
var createSharedStaticBufferIO = ({
  headersBuffer,
}) => {
  const u32Bytes = Uint32Array.BYTES_PER_ELEMENT;
  const slotStride = 0 /* header */ + 128 /* TotalBuff */;
  const writableBytes = (128 /* TotalBuff */ - 8 /* Size */) * u32Bytes;
  const slotOffset = (at) => at * slotStride + 0 /* header */;
  const slotStartBytes = (at) => (slotOffset(at) + 8 /* Size */) * u32Bytes;
  const arrU8Sec = Array.from({
    length: 32, /* slots */
  }, (_, i) => new Uint8Array(headersBuffer, slotStartBytes(i), writableBytes));
  const arrBuffSec = Array.from(
    { length: 32 /* slots */ },
    (_, i) => NodeBuffer.from(headersBuffer, slotStartBytes(i), writableBytes),
  );
  const arrF64Sec = Array.from(
    {
      length: 32, /* slots */
    },
    (_, i) =>
      new Float64Array(headersBuffer, slotStartBytes(i), writableBytes >>> 3),
  );
  const canWrite = (start, length) =>
    (start | 0) >= 0 && start + length <= writableBytes;
  const writeUtf8 = (str, at) => {
    const { read, written } = textEncode.encodeInto(str, arrU8Sec[at]);
    if (read !== str.length) {
      return -1;
    }
    return written;
  };
  const readUtf8 = (start, end, at) => {
    return arrBuffSec[at].toString("utf8", start, end);
  };
  const writeBinary = (src, at, start = 0) => {
    if (!canWrite(start, src.byteLength)) {
      return -1;
    }
    arrU8Sec[at].set(src, start);
    return src.byteLength;
  };
  const write8Binary = (src, at, start = 0) => {
    const bytes = src.byteLength;
    if (!canWrite(start, bytes)) {
      return -1;
    }
    arrF64Sec[at].set(src, start >>> 3);
    return bytes;
  };
  const readBytesCopy = (start, end, at) => arrU8Sec[at].slice(start, end);
  const readBytesView = (start, end, at) => arrU8Sec[at].subarray(start, end);
  const readBytesBufferCopy = (start, end, at) => {
    const length = Math.max(0, end - start | 0);
    const out = NodeBuffer.allocUnsafe(length);
    if (length === 0) {
      return out;
    }
    arrBuffSec[at].copy(out, 0, start, end);
    return out;
  };
  const readBytesArrayBufferCopy = (start, end, at) => {
    const length = Math.max(0, end - start | 0);
    const out = new Uint8Array(length);
    if (length === 0) {
      return out.buffer;
    }
    arrBuffSec[at].copy(out, 0, start, end);
    return out.buffer;
  };
  const read8BytesFloatCopy = (start, end, at) =>
    arrF64Sec[at].slice(start >>> 3, end >>> 3);
  const read8BytesFloatView = (start, end, at) =>
    arrF64Sec[at].subarray(start >>> 3, end >>> 3);
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
    maxBytes: writableBytes,
  };
};

// src/memory/payloadCodec.ts
import { Buffer as NodeBuffer2 } from "node:buffer";

// src/ipc/protocol/parsers/NumericBuffer.ts
var kBrand = Symbol("NumericArray");

class NumericBuffer {
  arr;
  arrFloat;
  isFloat = false;
  [kBrand] = true;
  constructor(data) {
    if (data instanceof Float64Array) {
      this.arrFloat = data;
      this.isFloat = true;
    } else {
      this.arr = data;
      this.isFloat = false;
    }
  }
  static FloatToArray(srcF64) {
    const len = srcF64.length;
    const arr = new Array(len);
    const rem = len & 3;
    let i = 0;
    for (; i < len - rem; i += 4) {
      arr[i] = srcF64[i];
      arr[i + 1] = srcF64[i + 1];
      arr[i + 2] = srcF64[i + 2];
      arr[i + 3] = srcF64[i + 3];
    }
    for (; i < len; i++) {
      arr[i] = srcF64[i];
    }
    return arr;
  }
  static isNumericArray(v) {
    return !!(v && v[kBrand]);
  }
  static fromFloat64(srcF64) {
    return new NumericBuffer(srcF64.slice());
  }
  static fromArrayCopy(arr) {
    return new NumericBuffer([...arr]);
  }
  toArray() {
    if (this.isFloat) {
      this.isFloat = true;
      return this.arr = NumericBuffer.FloatToArray(this.arrFloat);
    }
    return this.arr;
  }
  toFloat64() {
    if (this.isFloat) {
      return this.arrFloat;
    }
    return Float64Array.from(this.arr);
  }
}

// src/error.ts
import { isMainThread } from "node:worker_threads";
var promisePayloadMarker = Symbol.for("knitting.promise.payload");
var reasonFrom = (task, type, detail) => {
  switch (type) {
    case 0 /* Function */: {
      const name = typeof task.value === "function"
        ? task.value.name || "<anonymous>"
        : "<unknown>";
      return `KNT_ERROR_0: Function is not a valid type; name: ${name}`;
    }
    case 1 /* Symbol */:
      return "KNT_ERROR_1: Symbol must use Symbol.for(...) keys";
    case 2 /* Json */:
      return detail == null || detail.length === 0
        ? "KNT_ERROR_2: JSON stringify failed; payload must be JSON-safe"
        : `KNT_ERROR_2: JSON stringify failed; ${detail}`;
    case 3 /* Serializable */:
      return detail == null || detail.length === 0
        ? "KNT_ERROR_3: Unsupported payload type; serialize it yourself"
        : `KNT_ERROR_3: Unsupported payload type; ${detail}`;
  }
};
var encoderError = ({
  task,
  type,
  onPromise,
  detail,
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
  if (markedTask[promisePayloadMarker] === true) {
    return false;
  }
  markedTask[promisePayloadMarker] = true;
  queueMicrotask(() => {
    markedTask[promisePayloadMarker] = false;
    task.value = reason;
    onPromise(task, { status: "rejected", reason });
  });
  return false;
};

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
var arrayBufferIsView = ArrayBuffer.isView;
var objectPrototype = Object.prototype;
var int32ArrayPrototype = Int32Array.prototype;
var float64ArrayPrototype = Float64Array.prototype;
var bigInt64ArrayPrototype = BigInt64Array.prototype;
var bigUint64ArrayPrototype = BigUint64Array.prototype;
var dataViewPrototype = DataView.prototype;
var UNSUPPORTED_OBJECT_DETAIL =
  "Unsupported object type. Allowed: plain object, array, Error, Date, Buffer, ArrayBuffer, DataView, and typed arrays. Serialize it yourself.";
var VIEW_KIND_UNKNOWN = 0;
var VIEW_KIND_INT32_ARRAY = 1;
var VIEW_KIND_FLOAT64_ARRAY = 2;
var VIEW_KIND_BIGINT64_ARRAY = 3;
var VIEW_KIND_BIGUINT64_ARRAY = 4;
var VIEW_KIND_DATA_VIEW = 5;
var getArrayBufferViewKind = (value) => {
  const proto = objectGetPrototypeOf(value);
  if (proto === int32ArrayPrototype) {
    return VIEW_KIND_INT32_ARRAY;
  }
  if (proto === float64ArrayPrototype) {
    return VIEW_KIND_FLOAT64_ARRAY;
  }
  if (proto === bigInt64ArrayPrototype) {
    return VIEW_KIND_BIGINT64_ARRAY;
  }
  if (proto === bigUint64ArrayPrototype) {
    return VIEW_KIND_BIGUINT64_ARRAY;
  }
  if (proto === dataViewPrototype) {
    return VIEW_KIND_DATA_VIEW;
  }
  if (value instanceof Int32Array) {
    return VIEW_KIND_INT32_ARRAY;
  }
  if (value instanceof Float64Array) {
    return VIEW_KIND_FLOAT64_ARRAY;
  }
  if (value instanceof BigInt64Array) {
    return VIEW_KIND_BIGINT64_ARRAY;
  }
  if (value instanceof BigUint64Array) {
    return VIEW_KIND_BIGUINT64_ARRAY;
  }
  if (value instanceof DataView) {
    return VIEW_KIND_DATA_VIEW;
  }
  return VIEW_KIND_UNKNOWN;
};
var isPlainJsonObject = (value) => {
  const proto = objectGetPrototypeOf(value);
  return proto === objectPrototype || proto === null;
};
var toErrorCause = (cause) => {
  if (cause === null || cause === undefined) {
    return cause;
  }
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
      message: cause.message,
    };
    if (typeof cause.stack === "string") {
      nested.stack = cause.stack;
    }
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
    message: error.message,
  };
  if (typeof error.stack === "string") {
    payload.stack = error.stack;
  }
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
  const err = new Error(
    typeof payload.message === "string" ? payload.message : "",
  );
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
  for (let i = bytes.length - 1; i >= 1; i--) {
    value = value << 8n | BigInt(bytes[i]);
  }
  return sign === 1 ? -value : value;
};
var initStaticIO = (headersBuffer) => {
  const u32Bytes = Uint32Array.BYTES_PER_ELEMENT;
  const slotStride = 0 /* header */ + 128 /* TotalBuff */;
  const slotOffset = (at) => at * slotStride + 0 /* header */;
  const slotStartBytes = (at) => (slotOffset(at) + 8 /* Size */) * u32Bytes;
  const writableBytes = (128 /* TotalBuff */ - 8 /* Size */) * u32Bytes;
  const requiredBytes = slotStartBytes(32 /* slots */ - 1) + writableBytes;
  if (headersBuffer.byteLength < requiredBytes) {
    return null;
  }
  return createSharedStaticBufferIO({
    headersBuffer: headersBuffer.buffer,
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
  sab,
  headersBuffer,
  onPromise,
}) => {
  const { allocTask, setSlotLength, free } = register({
    lockSector,
  });
  const {
    writeBinary: writeDynamicBinary,
    write8Binary: writeDynamic8Binary,
    writeUtf8: writeDynamicUtf8,
  } = createSharedDynamicBufferIO({
    sab,
  });
  const {
    maxBytes: staticMaxBytes,
    writeBinary: writeStaticBinary,
    write8Binary: writeStatic8Binary,
    writeUtf8: writeStaticUtf8,
  } = requireStaticIO(headersBuffer);
  const slotOf = (task) => getTaskSlotIndex(task);
  const reserveDynamic = (task, bytes) => {
    task[5 /* PayloadLen */] = bytes;
    if (allocTask(task) === -1) {
      return false;
    }
    return true;
  };
  let objectDynamicSlot = -1;
  const reserveDynamicObject = (task, bytes) => {
    task[5 /* PayloadLen */] = bytes;
    if (allocTask(task) === -1) {
      return false;
    }
    objectDynamicSlot = slotOf(task);
    return true;
  };
  const rollbackObjectDynamic = () => {
    if (objectDynamicSlot !== -1) {
      free(objectDynamicSlot);
      objectDynamicSlot = -1;
    }
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
      const detail = encodeErrorReason instanceof Error
        ? encodeErrorReason.message
        : String(encodeErrorReason);
      return encoderError({
        task,
        type: 3, /* Serializable */
        onPromise,
        detail,
      });
    }
    const estimatedBytes = text.length * 3;
    task[2 /* Type */] = 24 /* Error */;
    if (!reserveDynamicObject(task, estimatedBytes)) {
      return false;
    }
    const written = writeDynamicUtf8(text, task[3 /* Start */]);
    task[5 /* PayloadLen */] = written;
    setSlotLength(slotOf(task), written);
    task.value = null;
    return true;
  };
  const encodeObjectBinary = (
    task,
    slotIndex,
    bytesView,
    dynamicType,
    staticType,
  ) => {
    const bytes = bytesView.byteLength;
    if (bytes <= staticMaxBytes) {
      const written = writeStaticBinary(bytesView, slotIndex);
      if (written !== -1) {
        task[2 /* Type */] = staticType;
        task[5 /* PayloadLen */] = written;
        task.value = null;
        return true;
      }
    }
    task[2 /* Type */] = dynamicType;
    if (!reserveDynamicObject(task, bytes)) {
      return false;
    }
    writeDynamicBinary(bytesView, task[3 /* Start */]);
    task.value = null;
    return true;
  };
  const encodeObjectFloat64Array = (task, slotIndex, float64) => {
    const bytes = float64.byteLength;
    if (bytes <= staticMaxBytes) {
      const written = writeStatic8Binary(float64, slotIndex);
      if (written !== -1) {
        task[2 /* Type */] = 32 /* StaticFloat64Array */;
        task[5 /* PayloadLen */] = written;
        task.value = null;
        return true;
      }
    }
    task[2 /* Type */] = 20 /* Float64Array */;
    if (!reserveDynamicObject(task, bytes)) {
      return false;
    }
    writeDynamic8Binary(float64, task[3 /* Start */]);
    task.value = null;
    return true;
  };
  const toUint8View = (value) =>
    new Uint8Array(value.buffer, value.byteOffset, value.byteLength);
  return (task, slotIndex) => {
    const args = task.value;
    switch (typeof args) {
      case "bigint":
        if (args < BIGINT64_MIN || args > BIGINT64_MAX) {
          const binaryBytes = encodeBigIntIntoScratch(args);
          const binary = bigintScratch.subarray(0, binaryBytes);
          if (binaryBytes <= staticMaxBytes) {
            const written = writeStaticBinary(binary, slotIndex);
            if (written !== -1) {
              task[2 /* Type */] = 29 /* StaticBigInt */;
              task[5 /* PayloadLen */] = written;
              clearBigIntScratch(binaryBytes);
              return true;
            }
          }
          task[2 /* Type */] = 28 /* BigInt */;
          if (!reserveDynamic(task, binaryBytes)) {
            clearBigIntScratch(binaryBytes);
            return false;
          }
          writeDynamicBinary(binary, task[3 /* Start */]);
          clearBigIntScratch(binaryBytes);
          return true;
        }
        BigInt64View[0] = args;
        task[2 /* Type */] = 2 /* BigInt */;
        task[3 /* Start */] = Uint32View[0];
        task[4 /* End */] = Uint32View[1];
        return true;
      case "boolean":
        task[2 /* Type */] = task.value === true ? 3 /* True */ : 4 /* False */;
        return true;
      case "function":
        return encoderError({
          task,
          type: 0, /* Function */
          onPromise,
        });
      case "number":
        if (args !== args) {
          task[2 /* Type */] = 6 /* NaN */;
          return true;
        }
        switch (args) {
          case Infinity:
            task[2 /* Type */] = 7 /* Infinity */;
            return true;
          case -Infinity:
            task[2 /* Type */] = 8 /* NegativeInfinity */;
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
              const detail = error instanceof Error
                ? error.message
                : String(error);
              return encoderError({
                task,
                type: 2, /* Json */
                onPromise,
                detail,
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
            if (!reserveDynamicObject(task, text.length * 3)) {
              return false;
            }
            const written = writeDynamicUtf8(text, task[3 /* Start */]);
            task[5 /* PayloadLen */] = written;
            setSlotLength(slotOf(task), written);
            task.value = null;
            return true;
          }
          if (NodeBuffer2.isBuffer(objectValue)) {
            return encodeObjectBinary(
              task,
              slotIndex,
              objectValue,
              38, /* Buffer */
              39, /* StaticBuffer */
            );
          }
          if (objectValue instanceof Uint8Array) {
            return encodeObjectBinary(
              task,
              slotIndex,
              objectValue,
              17, /* Binary */
              18, /* StaticBinary */
            );
          }
          if (objectValue instanceof ArrayBuffer) {
            return encodeObjectBinary(
              task,
              slotIndex,
              new Uint8Array(objectValue),
              36, /* ArrayBuffer */
              37, /* StaticArrayBuffer */
            );
          }
          if (objectValue instanceof NumericBuffer) {
            const float64 = objectValue.toFloat64();
            task[2 /* Type */] = 14 /* NumericBuffer */;
            if (!reserveDynamicObject(task, float64.byteLength)) {
              return false;
            }
            writeDynamic8Binary(float64, task[3 /* Start */]);
            task.value = null;
            return true;
          }
          if (arrayBufferIsView(objectValue)) {
            switch (getArrayBufferViewKind(objectValue)) {
              case VIEW_KIND_INT32_ARRAY:
                return encodeObjectBinary(
                  task,
                  slotIndex,
                  toUint8View(objectValue),
                  19, /* Int32Array */
                  31, /* StaticInt32Array */
                );
              case VIEW_KIND_FLOAT64_ARRAY:
                return encodeObjectFloat64Array(task, slotIndex, objectValue);
              case VIEW_KIND_BIGINT64_ARRAY:
                return encodeObjectBinary(
                  task,
                  slotIndex,
                  toUint8View(objectValue),
                  21, /* BigInt64Array */
                  33, /* StaticBigInt64Array */
                );
              case VIEW_KIND_BIGUINT64_ARRAY:
                return encodeObjectBinary(
                  task,
                  slotIndex,
                  toUint8View(objectValue),
                  22, /* BigUint64Array */
                  34, /* StaticBigUint64Array */
                );
              case VIEW_KIND_DATA_VIEW:
                return encodeObjectBinary(
                  task,
                  slotIndex,
                  toUint8View(objectValue),
                  23, /* DataView */
                  35, /* StaticDataView */
                );
            }
          }
          if (objectValue instanceof Date) {
            Float64View[0] = objectValue.getTime();
            task[2 /* Type */] = 25 /* Date */;
            task[3 /* Start */] = Uint32View[0];
            task[4 /* End */] = Uint32View[1];
            task.value = null;
            return true;
          }
          if (objectValue instanceof Promise) {
            const markedTask = task;
            if (markedTask[PromisePayloadMarker] !== true) {
              markedTask[PromisePayloadMarker] = true;
              objectValue.then((value) => {
                markedTask[PromisePayloadMarker] = false;
                task.value = value;
                onPromise?.(task, { status: "fulfilled", value });
              }, (reason) => {
                markedTask[PromisePayloadMarker] = false;
                task.value = reason;
                onPromise?.(task, { status: "rejected", reason });
              });
            }
            return false;
          }
          if (objectValue instanceof Error) {
            return encodeErrorObject(task, objectValue);
          }
          return encoderError({
            task,
            type: 3, /* Serializable */
            onPromise,
            detail: UNSUPPORTED_OBJECT_DETAIL,
          });
        } catch (error) {
          rollbackObjectDynamic();
          const detail = error instanceof Error ? error.message : String(error);
          return encoderError({
            task,
            type: 3, /* Serializable */
            onPromise,
            detail,
          });
        }
      case "string": {
        const text = args;
        const estimatedBytes = text.length * 3;
        if (text.length <= staticMaxBytes) {
          const written2 = writeStaticUtf8(text, slotIndex);
          if (written2 !== -1) {
            task[2 /* Type */] = 15 /* StaticString */;
            task[5 /* PayloadLen */] = written2;
            return true;
          }
        }
        task[2 /* Type */] = 11 /* String */;
        if (!reserveDynamic(task, estimatedBytes)) {
          return false;
        }
        const written = writeDynamicUtf8(
          text,
          task[3 /* Start */],
          estimatedBytes,
        );
        task[5 /* PayloadLen */] = written;
        setSlotLength(slotOf(task), written);
        return true;
      }
      case "symbol": {
        const key = symbolKeyFor(args);
        if (key === undefined) {
          return encoderError({
            task,
            type: 1, /* Symbol */
            onPromise,
          });
        }
        const estimatedBytes = key.length * 3;
        if (estimatedBytes <= staticMaxBytes) {
          const written2 = writeStaticUtf8(key, slotIndex);
          if (written2 !== -1) {
            task[2 /* Type */] = 27 /* StaticSymbol */;
            task[5 /* PayloadLen */] = written2;
            return true;
          }
        }
        task[2 /* Type */] = 26 /* Symbol */;
        if (!reserveDynamic(task, estimatedBytes)) {
          return false;
        }
        const written = writeDynamicUtf8(key, task[3 /* Start */]);
        task[5 /* PayloadLen */] = written;
        setSlotLength(slotOf(task), written);
        return true;
      }
      case "undefined":
        task[2 /* Type */] = 5 /* Undefined */;
        return true;
    }
  };
};
var decodePayload = ({
  lockSector,
  sab,
  headersBuffer,
  host,
}) => {
  const { free } = register({
    lockSector,
  });
  const freeTaskSlot = (task) => free(getTaskSlotIndex(task));
  const {
    readUtf8: readDynamicUtf8,
    readBytesCopy: readDynamicBytesCopy,
    readBytesBufferCopy: readDynamicBufferCopy,
    readBytesArrayBufferCopy: readDynamicArrayBufferCopy,
    read8BytesFloatCopy: readDynamic8BytesFloatCopy,
    read8BytesFloatView: readDynamic8BytesFloatView,
  } = createSharedDynamicBufferIO({
    sab,
  });
  const {
    readUtf8: readStaticUtf8,
    readBytesCopy: readStaticBytesCopy,
    readBytesBufferCopy: readStaticBufferCopy,
    readBytesArrayBufferCopy: readStaticArrayBufferCopy,
    read8BytesFloatCopy: readStatic8BytesFloatCopy,
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
      case 7 /* Infinity */:
        task.value = Infinity;
        return;
      case 6 /* NaN */:
        task.value = NaN;
        return;
      case 8 /* NegativeInfinity */:
        task.value = -Infinity;
        return;
      case 10 /* Null */:
        task.value = null;
        return;
      case 5 /* Undefined */:
        task.value = undefined;
        return;
      case 11 /* String */:
        task.value = readDynamicUtf8(
          task[3 /* Start */],
          task[3 /* Start */] + task[5 /* PayloadLen */],
        );
        freeTaskSlot(task);
        return;
      case 15 /* StaticString */:
        task.value = readStaticUtf8(0, task[5 /* PayloadLen */], slotIndex);
        return;
      case 12 /* Json */:
        task.value = parseJSON(
          readDynamicUtf8(
            task[3 /* Start */],
            task[3 /* Start */] + task[5 /* PayloadLen */],
          ),
        );
        freeTaskSlot(task);
        return;
      case 16 /* StaticJson */:
        task.value = parseJSON(
          readStaticUtf8(0, task[5 /* PayloadLen */], slotIndex),
        );
        return;
      case 28 /* BigInt */:
        task.value = decodeBigIntBinary(
          readDynamicBytesCopy(
            task[3 /* Start */],
            task[3 /* Start */] + task[5 /* PayloadLen */],
          ),
        );
        freeTaskSlot(task);
        return;
      case 29 /* StaticBigInt */:
        task.value = decodeBigIntBinary(
          readStaticBytesCopy(0, task[5 /* PayloadLen */], slotIndex),
        );
        return;
      case 26 /* Symbol */:
        task.value = symbolFor(
          readDynamicUtf8(
            task[3 /* Start */],
            task[3 /* Start */] + task[5 /* PayloadLen */],
          ),
        );
        freeTaskSlot(task);
        return;
      case 27 /* StaticSymbol */:
        task.value = symbolFor(
          readStaticUtf8(0, task[5 /* PayloadLen */], slotIndex),
        );
        return;
      case 19 /* Int32Array */: {
        const bytes = readDynamicBytesCopy(
          task[3 /* Start */],
          task[3 /* Start */] + task[5 /* PayloadLen */],
        );
        task.value = new Int32Array(
          bytes.buffer,
          bytes.byteOffset,
          bytes.byteLength >>> 2,
        );
        freeTaskSlot(task);
        return;
      }
      case 31 /* StaticInt32Array */: {
        const bytes = readStaticBytesCopy(
          0,
          task[5 /* PayloadLen */],
          slotIndex,
        );
        task.value = new Int32Array(
          bytes.buffer,
          bytes.byteOffset,
          bytes.byteLength >>> 2,
        );
        return;
      }
      case 20 /* Float64Array */: {
        task.value = readDynamic8BytesFloatCopy(
          task[3 /* Start */],
          task[3 /* Start */] + task[5 /* PayloadLen */],
        );
        freeTaskSlot(task);
        return;
      }
      case 32 /* StaticFloat64Array */:
        task.value = readStatic8BytesFloatCopy(
          0,
          task[5 /* PayloadLen */],
          slotIndex,
        );
        return;
      case 21 /* BigInt64Array */: {
        const bytes = readDynamicBytesCopy(
          task[3 /* Start */],
          task[3 /* Start */] + task[5 /* PayloadLen */],
        );
        task.value = new BigInt64Array(
          bytes.buffer,
          bytes.byteOffset,
          bytes.byteLength >>> 3,
        );
        freeTaskSlot(task);
        return;
      }
      case 33 /* StaticBigInt64Array */: {
        const bytes = readStaticBytesCopy(
          0,
          task[5 /* PayloadLen */],
          slotIndex,
        );
        task.value = new BigInt64Array(
          bytes.buffer,
          bytes.byteOffset,
          bytes.byteLength >>> 3,
        );
        return;
      }
      case 22 /* BigUint64Array */: {
        const bytes = readDynamicBytesCopy(
          task[3 /* Start */],
          task[3 /* Start */] + task[5 /* PayloadLen */],
        );
        task.value = new BigUint64Array(
          bytes.buffer,
          bytes.byteOffset,
          bytes.byteLength >>> 3,
        );
        freeTaskSlot(task);
        return;
      }
      case 34 /* StaticBigUint64Array */: {
        const bytes = readStaticBytesCopy(
          0,
          task[5 /* PayloadLen */],
          slotIndex,
        );
        task.value = new BigUint64Array(
          bytes.buffer,
          bytes.byteOffset,
          bytes.byteLength >>> 3,
        );
        return;
      }
      case 23 /* DataView */: {
        const bytes = readDynamicBytesCopy(
          task[3 /* Start */],
          task[3 /* Start */] + task[5 /* PayloadLen */],
        );
        task.value = new DataView(
          bytes.buffer,
          bytes.byteOffset,
          bytes.byteLength,
        );
        freeTaskSlot(task);
        return;
      }
      case 35 /* StaticDataView */: {
        const bytes = readStaticBytesCopy(
          0,
          task[5 /* PayloadLen */],
          slotIndex,
        );
        task.value = new DataView(
          bytes.buffer,
          bytes.byteOffset,
          bytes.byteLength,
        );
        return;
      }
      case 25 /* Date */:
        Uint32View[0] = task[3 /* Start */];
        Uint32View[1] = task[4 /* End */];
        task.value = new Date(Float64View[0]);
        return;
      case 24 /* Error */:
        task.value = parseErrorPayload(
          readDynamicUtf8(
            task[3 /* Start */],
            task[3 /* Start */] + task[5 /* PayloadLen */],
          ),
        );
        freeTaskSlot(task);
        return;
      case 17 /* Binary */:
        {
          const buffer = readDynamicBufferCopy(
            task[3 /* Start */],
            task[3 /* Start */] + task[5 /* PayloadLen */],
          );
          task.value = new Uint8Array(
            buffer.buffer,
            buffer.byteOffset,
            buffer.byteLength,
          );
        }
        freeTaskSlot(task);
        return;
      case 18 /* StaticBinary */:
        task.value = readStaticBytesCopy(
          0,
          task[5 /* PayloadLen */],
          slotIndex,
        );
        return;
      case 36 /* ArrayBuffer */:
        task.value = readDynamicArrayBufferCopy(
          task[3 /* Start */],
          task[3 /* Start */] + task[5 /* PayloadLen */],
        );
        freeTaskSlot(task);
        return;
      case 37 /* StaticArrayBuffer */:
        task.value = readStaticArrayBufferCopy(
          0,
          task[5 /* PayloadLen */],
          slotIndex,
        );
        return;
      case 38 /* Buffer */:
        task.value = readDynamicBufferCopy(
          task[3 /* Start */],
          task[3 /* Start */] + task[5 /* PayloadLen */],
        );
        freeTaskSlot(task);
        return;
      case 39 /* StaticBuffer */:
        task.value = readStaticBufferCopy(
          0,
          task[5 /* PayloadLen */],
          slotIndex,
        );
        return;
      case 14 /* NumericBuffer */:
        task.value = NumericBuffer.fromFloat64(
          readDynamic8BytesFloatView(
            task[3 /* Start */],
            task[3 /* Start */] + task[5 /* PayloadLen */],
          ),
        );
        freeTaskSlot(task);
        return;
    }
  };
};

// src/memory/lock.ts
var PromisePayloadMarker = Symbol.for("knitting.promise.payload");
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
var getTaskFunctionMeta = (task) =>
  task[0 /* FunctionID */] >>> TASK_FUNCTION_ID_BITS &
  TASK_FUNCTION_META_VALUE_MASK;
var getTaskSlotIndex = (task) =>
  task[6 /* slotBuffer */] & TASK_SLOT_INDEX_MASK;
var setTaskSlotIndex = (task, slotIndex) => {
  task[6 /* slotBuffer */] =
    (task[6 /* slotBuffer */] & TASK_SLOT_META_PACKED_MASK |
      slotIndex & TASK_SLOT_INDEX_MASK) >>> 0;
};
var getTaskSlotMeta = (task) =>
  task[6 /* slotBuffer */] >>> TASK_SLOT_INDEX_BITS & TASK_SLOT_META_VALUE_MASK;
var LOCK_WORD_BYTES = Int32Array.BYTES_PER_ELEMENT;
var LOCK_HOST_BITS_OFFSET_BYTES = 64 /* padding */;
var LOCK_WORKER_BITS_OFFSET_BYTES = 64 /* padding */ * 2;
var LOCK_SECTOR_BYTE_LENGTH = LOCK_WORKER_BITS_OFFSET_BYTES + LOCK_WORD_BYTES;
var HEADER_SLOT_STRIDE_U32 = 0 /* header */ + 128 /* TotalBuff */;
var HEADER_U32_LENGTH = 0 /* header */ +
  HEADER_SLOT_STRIDE_U32 * 32 /* slots */;
var HEADER_BYTE_LENGTH = HEADER_U32_LENGTH * Uint32Array.BYTES_PER_ELEMENT;
var INDEX_ID = 0;
var def = (_) => {};
var createTaskShell = () => {
  const task = new Uint32Array(8 /* Size */);
  task.value = null;
  task.resolve = def;
  task.reject = def;
  task[PromisePayloadMarker] = false;
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
var takeTask = ({ queue }) => (array, at) => {
  const slotOffset = at * HEADER_SLOT_STRIDE_U32 + 0 /* header */;
  const task = queue[array[slotOffset + 1 /* ID */]];
  fillTaskFrom(task, array, slotOffset);
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
  payloadSector,
  resultList,
  toSentList,
  recycleList,
}) => {
  const LockBoundSAB = LockBoundSector ??
    new SharedArrayBuffer(LOCK_SECTOR_BYTE_LENGTH);
  const hostBits = new Int32Array(LockBoundSAB, LOCK_HOST_BITS_OFFSET_BYTES, 1);
  const workerBits = new Int32Array(
    LockBoundSAB,
    LOCK_WORKER_BITS_OFFSET_BYTES,
    1,
  );
  const bufferHeadersBuffer = headers ??
    new SharedArrayBuffer(HEADER_BYTE_LENGTH);
  const headersBuffer = new Uint32Array(bufferHeadersBuffer);
  const payloadMaxBytes = 64 * 1024 * 1024;
  const payloadInitialBytes = HAS_SAB_GROW ? 4 * 1024 * 1024 : payloadMaxBytes;
  const payloadSAB = payload ??
    createSharedArrayBuffer(payloadInitialBytes, payloadMaxBytes);
  const payloadLockSAB = payloadSector ??
    new SharedArrayBuffer(LOCK_SECTOR_BYTE_LENGTH);
  let promiseHandler;
  const encodeTask = encodePayload({
    sab: payloadSAB,
    headersBuffer,
    lockSector: payloadLockSAB,
    onPromise: (task, result) => promiseHandler?.(task, result),
  });
  const decodeTask = decodePayload({
    sab: payloadSAB,
    headersBuffer,
    lockSector: payloadLockSAB,
  });
  let LastLocal = 0 | 0;
  let LastWorker = 0 | 0;
  let lastTake = 32 | 0;
  const toBeSent = toSentList ?? new RingQueue();
  const recyclecList = recycleList ?? new RingQueue();
  const resolved = resultList ?? new RingQueue();
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
  const enlist = (task) => toBeSentPush(task);
  const encodeWithState = (task, state) => {
    const free = ~state;
    if (free === 0) {
      return 0;
    }
    if (!encodeTask(task, selectedSlotIndex = 31 - clz32(free))) {
      return 0;
    }
    encodeAt(task, selectedSlotIndex, selectedSlotBit = 1 << selectedSlotIndex);
    return selectedSlotBit;
  };
  const encodeManyFrom = (list) => {
    let state = LastLocal ^ a_load(workerBits, 0) | 0;
    let encoded = 0 | 0;
    if (list === toBeSent) {
      while (true) {
        const task = toBeSentShift();
        if (!task) {
          break;
        }
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
        if (!task) {
          break;
        }
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
    if (toBeSent.isEmpty) {
      return true;
    }
    encodeManyFrom(toBeSent);
    return toBeSent.isEmpty;
  };
  let selectedSlotIndex = 0 | 0, selectedSlotBit = 0 >>> 0;
  const storeHost = (bit) =>
    a_store(hostBits, 0, LastLocal = LastLocal ^ bit | 0);
  const storeWorker = (bit) =>
    a_store(workerBits, 0, LastWorker = LastWorker ^ bit | 0);
  const encode = (task, state = LastLocal ^ a_load(workerBits, 0) | 0) => {
    const free = ~state;
    if (free === 0) {
      return false;
    }
    if (!encodeTask(task, selectedSlotIndex = 31 - clz32(free))) {
      return false;
    }
    return encodeAt(
      task,
      selectedSlotIndex,
      selectedSlotBit = 1 << selectedSlotIndex,
    );
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
    storeHost(bit);
    return true;
  };
  const hasSpace = () => (hostBits[0] ^ LastWorker) !== 0;
  const decode = () => {
    let diff = a_load(hostBits, 0) ^ LastWorker;
    if (diff === 0) {
      return false;
    }
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
        if (pick === 0) {
          pick = diff;
        }
        decodeAt(selectedSlotIndex = 31 - clz32(pick));
        selectedSlotBit = 1 << (last = selectedSlotIndex);
        diff ^= selectedSlotBit;
        consumedBits = consumedBits ^ selectedSlotBit | 0;
      }
    } finally {
      if (consumedBits !== 0) {
        storeWorker(consumedBits);
      }
    }
    lastTake = last;
    return true;
  };
  const resolveHost = ({
    queue,
    onResolved,
  }) => {
    const getTask = takeTask({
      queue,
    });
    const HAS_RESOLVE = onResolved ? true : false;
    let lastResolved = 32;
    return () => {
      let diff = a_load(hostBits, 0) ^ LastWorker | 0;
      if (diff === 0) {
        return 0;
      }
      let modified = 0;
      let consumedBits = 0 | 0;
      let last = lastResolved;
      if (last === 32) {
        const idx = 31 - clz32(diff);
        const selectedBit = 1 << idx;
        const task = getTask(headersBuffer, idx);
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
        if (pick === 0) {
          pick = diff;
        }
        const idx = 31 - clz32(pick);
        const selectedBit = 1 << idx;
        const task = getTask(headersBuffer, idx);
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
    const recycled = recycleShift();
    let task;
    if (recycled) {
      fillTaskFrom(recycled, headersBuffer, slotOffset(at));
      recycled.value = null;
      recycled.resolve = def;
      recycled.reject = def;
      task = recycled;
    } else {
      task = makeTaskFrom(headersBuffer, slotOffset(at));
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
    },
  };
};

// src/worker/composable-runners.ts
var ABORT_SIGNAL_META_OFFSET = 1;
var TIMEOUT_KIND_RESOLVE = 1;
var p_now = performance.now.bind(performance);
var raceTimeout = (promise, ms, resolveOnTimeout, timeoutValue) =>
  new Promise((resolve, reject) => {
    let done = false;
    const timer = setTimeout(() => {
      if (done) {
        return;
      }
      done = true;
      if (resolveOnTimeout) {
        resolve(timeoutValue);
      } else {
        reject(timeoutValue);
      }
    }, ms);
    promise.then((value) => {
      if (done) {
        return;
      }
      done = true;
      clearTimeout(timer);
      resolve(value);
    }, (err) => {
      if (done) {
        return;
      }
      done = true;
      clearTimeout(timer);
      reject(err);
    });
  });
var nowStamp = (now) => (Math.floor(now()) & TASK_SLOT_META_VALUE_MASK) >>> 0;
var applyTimeoutBudget = (promise, slot, spec, now) => {
  const elapsed = nowStamp(now) - getTaskSlotMeta(slot) &
    TASK_SLOT_META_VALUE_MASK;
  const remaining = spec.ms - elapsed;
  if (!(remaining > 0)) {
    promise.then(() => {}, () => {});
    return spec.kind === TIMEOUT_KIND_RESOLVE
      ? Promise.resolve(spec.value)
      : Promise.reject(spec.value);
  }
  const timeoutMs = Math.max(1, Math.floor(remaining));
  return raceTimeout(
    promise,
    timeoutMs,
    spec.kind === TIMEOUT_KIND_RESOLVE,
    spec.value,
  );
};
var NO_ABORT_SIGNAL = -1;
var readSignal = (slot) => {
  const encodedSignal = getTaskFunctionMeta(slot);
  if (encodedSignal === 0) {
    return NO_ABORT_SIGNAL;
  }
  const signal = encodedSignal - ABORT_SIGNAL_META_OFFSET | 0;
  return signal >= 0 ? signal : NO_ABORT_SIGNAL;
};
var throwIfAborted = (signal, hasAborted) => {
  if (signal === NO_ABORT_SIGNAL) {
    return;
  }
  if (hasAborted(signal)) {
    throw new Error("Task aborted");
  }
};
var makeToolkitCache = (hasAborted) => {
  const bySignal = [];
  return (signal) => {
    let toolkit = bySignal[signal];
    if (toolkit) {
      return toolkit;
    }
    const hasAbortedMethod = () => hasAborted(signal);
    toolkit = {
      hasAborted: hasAbortedMethod,
    };
    bySignal[signal] = toolkit;
    return toolkit;
  };
};
var composeWorkerRunner = ({
  job,
  timeout,
  hasAborted,
  now,
}) => {
  const nowTime = now ?? p_now;
  if (!hasAborted) {
    if (!timeout) {
      return (slot) => job(slot.value);
    }
    return (slot) => {
      const result = job(slot.value);
      if (!(result instanceof Promise)) {
        return result;
      }
      return applyTimeoutBudget(result, slot, timeout, nowTime);
    };
  }
  const getToolkit = makeToolkitCache(hasAborted);
  if (!timeout) {
    return (slot) => {
      const signal = readSignal(slot);
      throwIfAborted(signal, hasAborted);
      if (signal === NO_ABORT_SIGNAL) {
        return job(slot.value);
      }
      return job(slot.value, getToolkit(signal));
    };
  }
  return (slot) => {
    const signal = readSignal(slot);
    throwIfAborted(signal, hasAborted);
    const result = signal === NO_ABORT_SIGNAL
      ? job(slot.value)
      : job(slot.value, getToolkit(signal));
    if (!(result instanceof Promise)) {
      return result;
    }
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
  now,
}) => {
  const PLACE_HOLDER = (_) => {
    throw "UNREACHABLE FROM PLACE HOLDER (thread)";
  };
  let hasAnythingFinished = 0;
  let awaiting = 0;
  const jobs = listOfFunctions.reduce(
    (acc, fixed) => (acc.push(fixed.run), acc),
    [],
  );
  const toWork = new RingQueue();
  const pendingFrames = new RingQueue();
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
      now,
    }));
    return acc;
  }, []);
  const hasCompleted = workerOptions?.resolveAfterFinishingAll === true
    ? () => hasAnythingFinished !== 0 && toWork.size === 0
    : () => hasAnythingFinished !== 0;
  const { decode, resolved } = lock;
  const resolvedShift = resolved.shiftNoClear.bind(resolved);
  const enqueueLock = () => {
    if (!decode()) {
      return false;
    }
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
    if (!returnLock.encode(slot)) {
      return false;
    }
    return true;
  };
  const sendReturn = (slot, shouldReject) => {
    slot[IDX_FLAGS] = shouldReject ? FLAG_REJECT : 0;
    if (!encodeReturnSafe(slot)) {
      return false;
    }
    hasAnythingFinished--;
    recyclePush(slot);
    return true;
  };
  const settleNow = (slot, isError, value, wasAwaited) => {
    slot.value = value;
    hasAnythingFinished++;
    if (wasAwaited && awaiting > 0) {
      awaiting--;
    }
    const shouldReject = isError || slot[IDX_FLAGS] === FLAG_REJECT;
    if (!sendReturn(slot, shouldReject)) {
      pendingPush(slot);
    }
  };
  const writeOne = () => {
    const slot = pendingShift();
    if (!slot) {
      return false;
    }
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
        if (!writeOne()) {
          break;
        }
        wrote++;
      }
      return wrote;
    },
    serviceBatchImmediate: () => {
      let processed = 0;
      while (processed < 3) {
        const slot = toWorkShift();
        if (!slot) {
          break;
        }
        try {
          const fnIndex = slot[0 /* FunctionID */] & FUNCTION_ID_MASK;
          const result = runByIndex[fnIndex](slot);
          slot[IDX_FLAGS] = 0;
          if (result instanceof Promise) {
            awaiting++;
            result.then(
              (value) => settleNow(slot, false, value, true),
              (err) => settleNow(slot, true, err, true),
            );
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
    getAwaiting: () => awaiting,
  };
};

// src/ipc/transport/shared-memory.ts
import { isMainThread as isMainThread2 } from "node:worker_threads";

// src/common/module-url.ts
import { pathToFileURL } from "node:url";
var WINDOWS_DRIVE_PATH = /^[A-Za-z]:[\\/]/;
var WINDOWS_UNC_PATH = /^\\\\[^\\/?]+\\[^\\/?]+/;
var encodeFilePath = (path) =>
  encodeURI(path).replace(/\?/g, "%3F").replace(/#/g, "%23");
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

// src/common/others.ts
import { hrtime } from "node:process";
import { createWriteStream, existsSync, mkdirSync } from "node:fs";
import { join } from "node:path";
var genTaskID = ((counter) => () => counter++)(0);
var getCallerFilePathForBun = (offset) => {
  const originalStackTrace = Error.prepareStackTrace;
  Error.prepareStackTrace = (_, stack2) => stack2;
  const err = new Error();
  const stack = err.stack;
  Error.prepareStackTrace = originalStackTrace;
  const caller = stack[offset]?.getFileName();
  if (!caller) {
    throw new Error("Unable to determine caller file.");
  }
  return toModuleUrl(caller);
};
var linkingMap = new Map();
var getCallerFilePath = () => {
  const stackOffset = 3;
  const href = getCallerFilePathForBun(stackOffset);
  const at = linkingMap.get(href) ?? 0;
  linkingMap.set(href, at + 1);
  return [href, at];
};
var beat = () => Number(hrtime.bigint()) / 1e4;
var signalDebuggerV2 = ({
  thread,
  isMain,
  op,
  startAt,
}) => {
  const orange = "\x1B[38;5;214m";
  const purple = "\x1B[38;5;129m";
  const reset = "\x1B[0m";
  const tab = "\t";
  const color = isMain ? orange : purple;
  const stripAnsi = (s) => s.replace(/\x1b\[[0-9;]*m/g, "");
  const logDir = join(process.cwd(), "log");
  if (!existsSync(logDir)) {
    mkdirSync(logDir, { recursive: true });
  }
  const born = startAt;
  const logFile = join(logDir, `${isMain ? "M" : "T"}_${thread}_${born}.log`);
  const stream = createWriteStream(logFile, { flags: "a" });
  let last = op[0];
  let lastBeat = born;
  let hitsTotal = 0;
  const hitsPerValue = { [last]: 0 };
  const header =
    `${color}Thread${tab}Tag${tab}Value${tab}SinceBorn${tab}SinceLast${tab}HitsPrev${tab}TotalHits${reset}`;
  stream.write(
    stripAnsi(header) + `
`,
  );
  function maybeLog(value, tag) {
    hitsTotal++;
    hitsPerValue[value] = (hitsPerValue[value] ?? 0) + 1;
    if (value !== last) {
      const now = isMain ? beat() : beat() + born;
      const hits = hitsPerValue[last];
      const line =
        `${color}${isMain ? "M" : "T"}${thread}${reset}${tab}${tab}` +
        `${tag}${String(last).padStart(1, " ")}${reset}${tab}` +
        `${(now - born).toFixed(2).padStart(9)}${tab}` +
        `${(now - lastBeat).toFixed(2).padStart(9)}${tab}` +
        `${hits.toString().padStart(8)}${tab}` +
        `${hitsTotal.toString().padStart(9)}`;
      stream.write(
        stripAnsi(line) + `
`,
      );
      last = value;
      lastBeat = now;
    }
  }
  const proxied = new Proxy(op, {
    get(target, prop, receiver) {
      if (prop === "0") {
        const value = Atomics.load(target, 0);
        maybeLog(value, "GET ");
        return value;
      }
      return Reflect.get(target, prop, receiver);
    },
    set(target, prop, value, receiver) {
      const ok = Reflect.set(target, prop, value, receiver);
      if (ok && prop === "0") {
        maybeLog(value, "PUT ");
      }
      return ok;
    },
  });
  return proxied;
};

// src/ipc/transport/shared-memory.ts
var page2 = 1024 * 4;
var CACHE_LINE_BYTES = 64;
var SIGNAL_OFFSETS = {
  op: 0,
  rxStatus: CACHE_LINE_BYTES,
  txStatus: CACHE_LINE_BYTES * 2,
};
var a_store = Atomics.store;
var createSharedMemoryTransport = (
  { sabObject, isMain, thread, debug, startTime },
) => {
  const toGrow = sabObject?.size ?? page2;
  const sab = sabObject?.sharedSab
    ? sabObject.sharedSab
    : createSharedArrayBuffer(toGrow + toGrow % page2, page2 * page2);
  const startAt = beat();
  const isReflected = typeof debug !== "undefined" &&
    (debug?.logMain === isMain && isMain === true ||
      debug?.logThreads === true && isMain === false);
  const op = isReflected
    ? signalDebuggerV2({
      thread,
      isMain,
      startAt: startTime ?? startAt,
      op: new Int32Array(sab, SIGNAL_OFFSETS.op, 1),
    })
    : new Int32Array(sab, SIGNAL_OFFSETS.op, 1);
  if (isMainThread2) {
    a_store(new Int32Array(sab, SIGNAL_OFFSETS.op, 1), 0, 0);
  }
  const rxStatus = new Int32Array(sab, SIGNAL_OFFSETS.rxStatus, 1);
  a_store(rxStatus, 0, 1);
  return {
    sab,
    op,
    startAt,
    isReflected,
    opView: new Int32Array(sab, SIGNAL_OFFSETS.op, 1),
    rxStatus,
    txStatus: new Int32Array(sab, SIGNAL_OFFSETS.txStatus, 1),
  };
};
var mainSignal = ({ op, opView, startAt, rxStatus, txStatus }) => {
  return {
    op,
    opView,
    startAt,
    rxStatus,
    txStatus,
  };
};

// src/common/task-symbol.ts
var endpointSymbol = Symbol.for("task");

// src/worker/safety/strict-import.ts
var BLOCKED_BINDING_GETTER = Symbol.for("knitting.strict.blockedBindingGetter");
var ROOT_GLOBAL = globalThis;
var OVERLAY_BINDINGS = ["require", "module", "globalThis", "self"];
var isSelfReferenceBinding = (name) => name === "globalThis" || name === "self";
var STRICT_DYNAMIC_IMPORT_ERROR =
  "[Knitting Strict] Dynamic import() is blocked in sandboxed code. All modules must be declared statically in the task definition.";
var toBlockedBindingMessage = (binding) =>
  `[Knitting Strict] ${binding} is blocked. Use static imports in your task module.`;
var createBlockedGetter = (binding) => {
  const getter = () => {
    throw new Error(toBlockedBindingMessage(binding));
  };
  getter[BLOCKED_BINDING_GETTER] = true;
  return getter;
};
var isBlockedBindingDescriptor = (descriptor) =>
  typeof descriptor?.get === "function" &&
  descriptor.get[BLOCKED_BINDING_GETTER] === true;
var createBlockedBindingDescriptor = (binding) => ({
  get: createBlockedGetter(binding),
  enumerable: false,
  configurable: false,
});
var createEphemeralBlockedBindingDescriptor = (binding) => ({
  get: createBlockedGetter(binding),
  enumerable: false,
  configurable: true,
});
var ignoreError = (action) => {
  try {
    action();
  } catch {}
};
var tryDefineProperty = (target, key, descriptor) =>
  ignoreError(() => {
    Object.defineProperty(target, key, descriptor);
  });
var mirrorCallableMetadata = ({
  target,
  source,
  name,
}) => {
  for (
    const [key, value] of [
      ["name", name],
      ["length", source.length],
      ["toString", () => Function.prototype.toString.call(source)],
    ]
  ) {
    tryDefineProperty(target, key, { value, configurable: true });
  }
};
var assertBindingHidden = (sandboxGlobal, binding) => {
  let proto = sandboxGlobal;
  while (proto !== null) {
    const isRoot = proto === sandboxGlobal;
    const descriptor = Object.getOwnPropertyDescriptor(proto, binding);
    if (!descriptor) {
      proto = Object.getPrototypeOf(proto);
      continue;
    }
    if (isRoot && isBlockedBindingDescriptor(descriptor)) {
      proto = Object.getPrototypeOf(proto);
      continue;
    }
    const location = isRoot ? "on membrane global" : "on prototype chain";
    const message = binding === "require"
      ? `FATAL: require found ${location}`
      : `FATAL: module object found ${location}`;
    throw new Error(message);
  }
};
var verifyNoRequire = (sandboxGlobal) => {
  assertBindingHidden(sandboxGlobal, "require");
  assertBindingHidden(sandboxGlobal, "module");
};
var createBlockedDynamicImportHook = () => (_specifier) => {
  throw new Error(STRICT_DYNAMIC_IMPORT_ERROR);
};
var createNodeVmDynamicImportOptions = () => ({
  importModuleDynamically: createBlockedDynamicImportHook(),
});
var createInjectedStrictCallable = (target) => {
  const callable = target;
  const wrapped = function (...args) {
    const g = ROOT_GLOBAL;
    const saved = new Map();
    const shadow = Object.create(g);
    Object.defineProperty(
      shadow,
      "require",
      createEphemeralBlockedBindingDescriptor("require"),
    );
    Object.defineProperty(
      shadow,
      "module",
      createEphemeralBlockedBindingDescriptor("module"),
    );
    for (const name of ["globalThis", "self"]) {
      Object.defineProperty(shadow, name, {
        value: shadow,
        configurable: true,
        writable: true,
        enumerable: true,
      });
    }
    for (const name of OVERLAY_BINDINGS) {
      const current = Object.getOwnPropertyDescriptor(g, name);
      saved.set(name, current);
      if (isSelfReferenceBinding(name)) {
        if (!current || current.configurable === true) {
          tryDefineProperty(g, name, {
            value: shadow,
            configurable: true,
            writable: true,
            enumerable: current?.enumerable ?? name === "self",
          });
        } else if ("value" in current && current.writable === true) {
          ignoreError(() => {
            g[name] = shadow;
          });
        }
        continue;
      }
      if (current && current.configurable !== true) {
        continue;
      }
      tryDefineProperty(g, name, createEphemeralBlockedBindingDescriptor(name));
    }
    try {
      return Reflect.apply(callable, this, args);
    } finally {
      for (const name of OVERLAY_BINDINGS) {
        const previous = saved.get(name);
        if (previous) {
          tryDefineProperty(g, name, previous);
          continue;
        }
        ignoreError(() => {
          Reflect.deleteProperty(g, name);
        });
      }
    }
  };
  mirrorCallableMetadata({
    target: wrapped,
    source: target,
    name: target.name || "strictInjectedCallable",
  });
  return wrapped;
};

// src/worker/safety/strict-sandbox.ts
import { createRequire as createRequire2 } from "node:module";
import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath, pathToFileURL as pathToFileURL2 } from "node:url";

// src/permison/strict-scan.ts
import { createRequire } from "node:module";
var MIN_MAX_EVAL_DEPTH = 1;
var MAX_MAX_EVAL_DEPTH = 64;
var DEFAULT_MAX_EVAL_DEPTH = 16;
var NON_EXCLUDABLE_PATTERN_IDS = new Set([
  "FFI-01",
  "FFI-02",
  "FFI-03",
  "FFI-04",
  "FFI-05",
  "FFI-06",
]);
var createBlockPattern = (id, regex, category, flags) => ({
  id,
  regex,
  category,
  severity: "block",
  ...flags,
});
var PATTERN_REGISTRY = [
  createBlockPattern("FFI-01", /\bbun\s*:\s*ffi\b/g, "ffi"),
  createBlockPattern("FFI-02", /\bBun\s*\.\s*dlopen\b/g, "ffi"),
  createBlockPattern("FFI-03", /\bBun\s*\.\s*linkSymbols\b/g, "ffi"),
  createBlockPattern("FFI-04", /\bprocess\s*\.\s*dlopen\b/g, "ffi"),
  createBlockPattern("FFI-05", /\bprocess\s*\.\s*binding\b/g, "ffi"),
  createBlockPattern("FFI-06", /\bprocess\s*\.\s*_linkedBinding\b/g, "ffi"),
  createBlockPattern("FS-01", /\bnode\s*:\s*fs\b/g, "fs"),
  createBlockPattern("FS-02", /['"]fs['"]/g, "fs"),
  createBlockPattern("FS-03", /['"]fs\/promises['"]/g, "fs"),
  createBlockPattern("THR-01", /\bnode\s*:\s*worker_threads\b/g, "thread"),
  createBlockPattern("THR-02", /\bnode\s*:\s*child_process\b/g, "thread"),
  createBlockPattern("THR-03", /\bnode\s*:\s*cluster\b/g, "thread"),
  createBlockPattern("EVAL-01", /\beval\s*\(/g, "eval", {
    preflightOnly: true,
  }),
  createBlockPattern("EVAL-02", /\bnew\s+Function\s*\(/g, "eval", {
    preflightOnly: true,
  }),
  createBlockPattern("EVAL-03", /\bFunction\s*\(/g, "eval", {
    preflightOnly: true,
  }),
  createBlockPattern("EVAL-04", /\bsetTimeout\s*\(\s*['"`]/g, "eval"),
  createBlockPattern("EVAL-05", /\bsetInterval\s*\(\s*['"`]/g, "eval"),
  createBlockPattern("IMP-01", /\bimport\s*\(/g, "import"),
  createBlockPattern("IMP-02", /\brequire\s*\(/g, "import"),
  createBlockPattern("IMP-03", /\brequire\s*\.\s*resolve\s*\(/g, "import"),
  createBlockPattern("IMP-04", /\bimport\s*\.\s*meta\b/g, "import"),
  createBlockPattern("IMP-06", /\bmodule\s*\.\s*createRequire\b/g, "import"),
  createBlockPattern(
    "GLOB-01",
    /\bFunction\s*\(\s*['"]return\s+this['"]\s*\)/g,
    "global",
  ),
  createBlockPattern(
    "GLOB-02",
    /\bconstructor\s*\.\s*constructor\s*\(/g,
    "global",
  ),
];
var clampMaxDepth = (value) => {
  if (!Number.isFinite(value)) {
    return DEFAULT_MAX_EVAL_DEPTH;
  }
  const int = Math.floor(value);
  if (int < MIN_MAX_EVAL_DEPTH) {
    return MIN_MAX_EVAL_DEPTH;
  }
  if (int > MAX_MAX_EVAL_DEPTH) {
    return MAX_MAX_EVAL_DEPTH;
  }
  return int;
};
var toFrozenScanResult = (result) => ({
  passed: result.passed,
  violations: Object.freeze(
    result.violations.map((v) => Object.freeze({ ...v })),
  ),
});
var AST_CACHE_LIMIT = 256;
var astViolationCache = new Map();
var FUNCTION_CONSTRUCTOR_ORIGINS = new Set([
  "Function",
  "GeneratorFunction",
  "AsyncFunction",
  "AsyncGeneratorFunction",
]);
var isFunctionConstructorOrigin = (origin) =>
  FUNCTION_CONSTRUCTOR_ORIGINS.has(origin);
var toAstCacheKey = ({
  source,
  context,
}) => `${isFunctionConstructorOrigin(context.origin) ? "fn" : "src"}:${source}`;
var getCachedAstViolations = (key) => {
  const cached = astViolationCache.get(key);
  if (!cached) {
    return;
  }
  astViolationCache.delete(key);
  astViolationCache.set(key, cached);
  return cached.map((entry) => ({ ...entry }));
};
var storeAstViolations = (key, violations) => {
  setCachedAstViolations(key, violations);
  return violations;
};
var setCachedAstViolations = (key, violations) => {
  astViolationCache.delete(key);
  astViolationCache.set(
    key,
    Object.freeze(violations.map((entry) => Object.freeze({ ...entry }))),
  );
  if (astViolationCache.size <= AST_CACHE_LIMIT) {
    return;
  }
  const oldest = astViolationCache.keys().next().value;
  if (typeof oldest === "string") {
    astViolationCache.delete(oldest);
  }
};
var require2 = createRequire(import.meta.url);
var tsApi = (() => {
  try {
    return require2("typescript");
  } catch {
    return;
  }
})();
var toAstViolation = ({
  pattern,
  match,
  line,
  column,
}) => ({
  pattern,
  match,
  line: Math.max(1, line),
  column: Math.max(1, column),
  category: "import",
  severity: "block",
});
var toLineColumnFromIndex = (source, index) => {
  const bounded = Math.max(0, Math.min(index, source.length));
  let line = 1;
  let column = 1;
  for (let i = 0; i < bounded; i++) {
    const ch = source.charCodeAt(i);
    if (ch === 10) {
      line++;
      column = 1;
      continue;
    }
    column++;
  }
  return { line, column };
};
var forEachRegexMatch = (source, regex, cb) => {
  regex.lastIndex = 0;
  for (const found of source.matchAll(regex)) {
    cb(found);
  }
};
var scanAstHeuristic = ({
  source,
  context,
}) => {
  const out = [];
  for (
    const [regex, pattern, match] of [
      [/\bimport\s*\(/g, "AST-ImportExpression", "import(...)"],
      [/\bimport\s*\.\s*meta\b/g, "AST-MetaProperty", "import.meta"],
      [/\brequire\s*\(/g, "AST-CallExpression:require", "require(...)"],
    ]
  ) {
    forEachRegexMatch(source, regex, (found) => {
      const { line, column } = toLineColumnFromIndex(source, found.index ?? 0);
      out.push(toAstViolation({ pattern, match, line, column }));
    });
  }
  if (out.length === 0 && context.depth > 0) {
    try {
      new Function(source);
    } catch (error) {
      out.push(toAstViolation({
        pattern: "AST-PARSE",
        match: String(error?.message ?? error).slice(0, 120),
        line: 1,
        column: 1,
      }));
    }
  }
  return out;
};
var parseSourceWithTs = ({
  source,
  context,
}) => {
  const ts = tsApi;
  if (!ts) {
    return {
      lineOffset: 0,
    };
  }
  const fileName = context.source ?? "strict-scan-input.ts";
  const wrapAsFunctionBody = isFunctionConstructorOrigin(context.origin);
  const wrappedSource = wrapAsFunctionBody
    ? `function __knitting_scan_wrapper__(){
${source}
}`
    : source;
  const lineOffset = wrapAsFunctionBody ? -1 : 0;
  const sourceFile = ts.createSourceFile(
    fileName,
    wrappedSource,
    ts.ScriptTarget.Latest,
    true,
    ts.ScriptKind.TS,
  );
  const diagnostics = sourceFile.parseDiagnostics ?? [];
  if (diagnostics.length === 0) {
    return {
      sourceFile,
      lineOffset,
    };
  }
  const first = diagnostics[0];
  const start = typeof first?.start === "number" ? first.start : 0;
  const position = sourceFile.getLineAndCharacterOfPosition(start);
  const rawMessage = first?.messageText;
  const message = typeof rawMessage === "string"
    ? rawMessage
    : rawMessage?.messageText ?? "syntax parse failure";
  return {
    sourceFile,
    lineOffset,
    parseError: toAstViolation({
      pattern: "AST-PARSE",
      match: String(message).slice(0, 120),
      line: position.line + 1 + lineOffset,
      column: position.character + 1,
    }),
  };
};
var scanAst = ({
  source,
  context,
}) => {
  const cacheKey = toAstCacheKey({ source, context });
  const cached = getCachedAstViolations(cacheKey);
  if (cached) {
    return cached;
  }
  if (!tsApi) {
    return storeAstViolations(cacheKey, scanAstHeuristic({ source, context }));
  }
  const parsed = parseSourceWithTs({ source, context });
  const sourceFile = parsed.sourceFile;
  if (!sourceFile) {
    return storeAstViolations(cacheKey, scanAstHeuristic({ source, context }));
  }
  if (parsed.parseError) {
    return storeAstViolations(cacheKey, [parsed.parseError]);
  }
  const out = [];
  const syntaxKind = tsApi.SyntaxKind;
  const toLineColumn = (node) => {
    const nodeAny = node;
    const start = typeof nodeAny.getStart === "function"
      ? nodeAny.getStart(sourceFile)
      : typeof nodeAny.pos === "number"
      ? nodeAny.pos
      : 0;
    const pos = sourceFile.getLineAndCharacterOfPosition(start);
    return {
      line: pos.line + 1 + parsed.lineOffset,
      column: pos.character + 1,
    };
  };
  const pushNodeViolation = (node, pattern, match) => {
    const { line, column } = toLineColumn(node);
    out.push(toAstViolation({ pattern, match, line, column }));
  };
  const visit = (node) => {
    const n = node;
    if (
      n.kind === syntaxKind.CallExpression &&
      n.expression?.kind === syntaxKind.ImportKeyword
    ) {
      pushNodeViolation(node, "AST-ImportExpression", "import(...)");
    }
    if (
      n.kind === syntaxKind.MetaProperty &&
      n.keywordToken === syntaxKind.ImportKeyword &&
      n.name?.escapedText === "meta"
    ) {
      pushNodeViolation(node, "AST-MetaProperty", "import.meta");
    }
    if (
      n.kind === syntaxKind.CallExpression &&
      n.expression?.kind === syntaxKind.Identifier &&
      n.expression.escapedText === "require"
    ) {
      pushNodeViolation(node, "AST-CallExpression:require", "require(...)");
    }
    tsApi.forEachChild(node, visit);
  };
  visit(sourceFile);
  return storeAstViolations(cacheKey, out);
};
var validatePatternRegistry = (patterns) => {
  const seen = new Set();
  const out = [];
  for (const pattern of patterns) {
    if (seen.has(pattern.id)) {
      throw new Error(`duplicate strict pattern id: ${pattern.id}`);
    }
    seen.add(pattern.id);
    if (pattern.regex.global !== true) {
      throw new Error(`strict pattern ${pattern.id} must include /g flag`);
    }
    out.push(pattern);
  }
  return out;
};
var resolvePatternRegistry = (options) => {
  const exclude = new Set(options?.excludePatterns ?? []);
  for (const id of exclude) {
    if (NON_EXCLUDABLE_PATTERN_IDS.has(id)) {
      throw new Error(`strict pattern ${id} cannot be excluded`);
    }
  }
  return validatePatternRegistry([
    ...PATTERN_REGISTRY,
    ...options?.additionalPatterns ?? [],
  ]).filter((pattern) => !exclude.has(pattern.id));
};

class StrictModeViolationError extends Error {
  name = "StrictModeViolationError";
  violations;
  origin;
  depth;
  source;
  scannedCode;
  constructor({
    origin,
    depth,
    source,
    violations,
    scannedCode,
  }) {
    const first = violations[0];
    const details = first
      ? `${first.pattern} at ${first.line}:${first.column} (${first.match})`
      : "unknown violation";
    super(
      `KNT_ERROR_PERMISSION_DENIED: strict mode blocked ${origin} at depth ${depth}: ${details}`,
    );
    this.violations = violations;
    this.origin = origin;
    this.depth = depth;
    this.source = source;
    this.scannedCode = typeof scannedCode === "string"
      ? scannedCode.slice(0, 200)
      : undefined;
  }
}

class StrictModeDepthError extends Error {
  name = "StrictModeDepthError";
  currentDepth;
  maxDepth;
  origin;
  constructor({
    currentDepth,
    maxDepth,
    origin,
  }) {
    super(
      `KNT_ERROR_PERMISSION_DENIED: strict mode depth limit reached in ${origin} (${currentDepth}/${maxDepth})`,
    );
    this.currentDepth = currentDepth;
    this.maxDepth = maxDepth;
    this.origin = origin;
  }
}
var scanCode = (code, context, options) => {
  if (code == null) {
    throw new TypeError("scanCode: input must not be null or undefined");
  }
  const source = String(code);
  if (source.length === 0) {
    const out2 = { passed: true, violations: [] };
    options?.onScan?.(context, toFrozenScanResult(out2));
    return out2;
  }
  const registry = resolvePatternRegistry(options);
  const isPreflight = context.depth === 0;
  const patterns = registry.filter((pattern) =>
    isPreflight ? pattern.runtimeOnly !== true : pattern.preflightOnly !== true
  );
  const violations = [];
  for (const pattern of patterns) {
    forEachRegexMatch(source, pattern.regex, (match) => {
      const violation = {
        pattern: pattern.id,
        match: match[0],
        ...toLineColumnFromIndex(source, match.index ?? 0),
        category: pattern.category,
        severity: pattern.severity,
      };
      violations.push(violation);
      if (violation.severity === "warn") {
        options?.onWarning?.(violation);
      }
    });
  }
  violations.push(...scanAst({ source, context }));
  const out = {
    passed: violations.every((violation) => violation.severity !== "block"),
    violations,
  };
  options?.onScan?.(context, toFrozenScanResult(out));
  return out;
};
var resolveStrictModeOptions = (input) => ({
  recursiveScan: input?.recursiveScan !== false,
  maxEvalDepth: clampMaxDepth(input?.maxEvalDepth),
  additionalPatterns: input?.additionalPatterns ?? [],
  excludePatterns: input?.excludePatterns ?? [],
  onWarning: input?.onWarning,
  onScan: input?.onScan,
});

// src/worker/safety/strict-membrane.ts
var SAFE_CORE_GLOBAL_NAMES = [
  "Object",
  "Array",
  "String",
  "Number",
  "Boolean",
  "BigInt",
  "Date",
  "Error",
  "TypeError",
  "RangeError",
  "ReferenceError",
  "SyntaxError",
  "URIError",
  "EvalError",
  "AggregateError",
  "Promise",
  "Map",
  "Set",
  "WeakMap",
  "WeakSet",
  "Symbol",
  "RegExp",
  "Int8Array",
  "Uint8Array",
  "Int16Array",
  "Uint16Array",
  "Int32Array",
  "Uint32Array",
  "Float32Array",
  "Float64Array",
  "BigInt64Array",
  "BigUint64Array",
  "DataView",
  "ArrayBuffer",
  "SharedArrayBuffer",
  "TextEncoder",
  "TextDecoder",
  "URL",
  "URLSearchParams",
  "AbortController",
  "AbortSignal",
];
var SAFE_FUNCTION_GLOBAL_NAMES = [
  "parseInt",
  "parseFloat",
  "isNaN",
  "isFinite",
  "encodeURI",
  "decodeURI",
  "encodeURIComponent",
  "decodeURIComponent",
  "atob",
  "btoa",
  "structuredClone",
  "queueMicrotask",
  "clearTimeout",
  "clearInterval",
];
var SAFE_LITERAL_GLOBAL_NAMES = [
  "Infinity",
  "NaN",
  "undefined",
];
var SAFE_CONSOLE_METHODS = [
  "log",
  "warn",
  "error",
  "info",
  "debug",
  "trace",
];
var SAFE_REFLECT_METHODS = [
  "apply",
  "defineProperty",
  "deleteProperty",
  "get",
  "getOwnPropertyDescriptor",
  "getPrototypeOf",
  "has",
  "isExtensible",
  "ownKeys",
  "preventExtensions",
  "set",
];
var BLOCKED_ADDITIONAL_GLOBAL_NAMES = new Set([
  "Bun",
  "Deno",
  "process",
  "require",
  "module",
  "WebAssembly",
  "fetch",
  "Worker",
  "SharedWorker",
  "XMLHttpRequest",
  "WebSocket",
  "EventSource",
  "Proxy",
]);
var BLOCKED_ADDITIONAL_GLOBAL_PREFIXES = [
  "Bun.",
  "Deno.",
  "process.",
  "globalThis.",
];
var CONSTRUCTOR_ROUTE_ENTRIES = [
  ["originalFunction", "secureFunction"],
  ["originalGeneratorFunction", "secureGeneratorFunction"],
  ["originalAsyncFunction", "secureAsyncFunction"],
  ["originalAsyncGeneratorFunction", "secureAsyncGeneratorFunction"],
];
var hasOwn = (target, key) => Object.prototype.hasOwnProperty.call(target, key);
var defineLockedValue = (target, key, value) => {
  if (hasOwn(target, key)) {
    throw new Error(
      `KNT_ERROR_PERMISSION_DENIED: strict membrane attempted to overwrite ${
        String(key)
      }`,
    );
  }
  Object.defineProperty(target, key, {
    value,
    writable: false,
    configurable: false,
    enumerable: true,
  });
};
var getHostGlobalValue = (name) => globalThis[name];
var bindGlobalFunction = (name) => {
  const candidate = getHostGlobalValue(name);
  if (typeof candidate !== "function") {
    return;
  }
  return candidate.bind(globalThis);
};
var createFrozenNamespace = (namespace) => {
  const out = Object.create(null);
  for (const key of Reflect.ownKeys(namespace)) {
    const descriptor = Object.getOwnPropertyDescriptor(namespace, key);
    if (!descriptor) {
      continue;
    }
    const nextDescriptor = {
      enumerable: descriptor.enumerable ?? false,
      configurable: false,
    };
    if ("value" in descriptor) {
      const value = typeof descriptor.value === "function"
        ? descriptor.value.bind(namespace)
        : descriptor.value;
      nextDescriptor.value = value;
      nextDescriptor.writable = false;
    } else {
      nextDescriptor.get = descriptor.get;
      nextDescriptor.set = undefined;
    }
    Object.defineProperty(out, key, nextDescriptor);
  }
  return Object.freeze(out);
};
var createSafeConsole = () => {
  const hostConsole = globalThis.console;
  const out = Object.create(null);
  for (const method of SAFE_CONSOLE_METHODS) {
    const target = hostConsole?.[method];
    const wrapped = typeof target === "function"
      ? (...args) => Reflect.apply(target, hostConsole, args)
      : () => {
        return;
      };
    defineLockedValue(out, method, wrapped);
  }
  return Object.freeze(out);
};
var defineAppliedMethod = (target, source, methodName) => {
  const method = source[methodName];
  if (typeof method !== "function") {
    return;
  }
  defineLockedValue(
    target,
    methodName,
    (...args) => Reflect.apply(method, source, args),
  );
};
var createSafeCrypto = () => {
  const hostCrypto = globalThis.crypto;
  if (!hostCrypto || typeof hostCrypto !== "object") {
    return;
  }
  const out = Object.create(null);
  defineAppliedMethod(out, hostCrypto, "getRandomValues");
  defineAppliedMethod(out, hostCrypto, "randomUUID");
  return Object.freeze(out);
};
var createSafePerformance = () => {
  const hostPerformance = globalThis.performance;
  if (!hostPerformance || typeof hostPerformance !== "object") {
    return;
  }
  const out = Object.create(null);
  defineAppliedMethod(out, hostPerformance, "now");
  if (out.now === undefined) {
    return;
  }
  return Object.freeze(out);
};
var blockedReferences = () => {
  const g = globalThis;
  return [
    globalThis,
    g.process,
    g.Bun,
    g.Deno,
    g.require,
    g.module,
    g.WebAssembly,
    g.fetch,
    g.Worker,
    g.SharedWorker,
    g.XMLHttpRequest,
    g.WebSocket,
    g.EventSource,
    g.Proxy,
  ].filter((entry) => entry != null);
};
var assertAdditionalGlobalName = (name) => {
  if (name.length === 0) {
    throw new Error(
      "KNT_ERROR_PERMISSION_DENIED: strict membrane additional global name must not be empty",
    );
  }
  if (BLOCKED_ADDITIONAL_GLOBAL_NAMES.has(name)) {
    throw new Error(
      `KNT_ERROR_PERMISSION_DENIED: strict membrane additional global "${name}" maps to runtime-native API`,
    );
  }
  for (const prefix of BLOCKED_ADDITIONAL_GLOBAL_PREFIXES) {
    if (name.startsWith(prefix)) {
      throw new Error(
        `KNT_ERROR_PERMISSION_DENIED: strict membrane additional global "${name}" maps to runtime-native API`,
      );
    }
  }
};
var assertAdditionalGlobalValue = (name, value) => {
  for (const blocked of blockedReferences()) {
    if (value === blocked) {
      throw new Error(
        `KNT_ERROR_PERMISSION_DENIED: strict membrane additional global "${name}" references runtime-native API`,
      );
    }
  }
};
var freezeDeep = (value, seen = new WeakSet()) => {
  if (!value || typeof value !== "object" && typeof value !== "function") {
    return value;
  }
  const objectValue = value;
  if (seen.has(objectValue)) {
    return value;
  }
  seen.add(objectValue);
  for (const key of Reflect.ownKeys(objectValue)) {
    const descriptor = Object.getOwnPropertyDescriptor(objectValue, key);
    if (!descriptor) {
      continue;
    }
    if ("value" in descriptor) {
      freezeDeep(descriptor.value, seen);
    }
    if (typeof descriptor.get === "function") {
      freezeDeep(descriptor.get, seen);
    }
    if (typeof descriptor.set === "function") {
      freezeDeep(descriptor.set, seen);
    }
  }
  try {
    Object.freeze(objectValue);
  } catch (error) {
    throw new Error(
      `KNT_ERROR_PERMISSION_DENIED: strict membrane additional global is not freezable (${
        String(error)
      })`,
    );
  }
  return value;
};
var routeConstructor = (candidate, constructors) => {
  if (!constructors || typeof candidate !== "function") {
    return;
  }
  for (const [originalKey, secureKey] of CONSTRUCTOR_ROUTE_ENTRIES) {
    const original = constructors[originalKey];
    const secure = constructors[secureKey];
    if (original && secure && candidate === original) {
      return secure;
    }
  }
  return;
};
var toConstructor = (candidate, constructors) => {
  const routed = routeConstructor(candidate, constructors);
  if (routed) {
    return routed;
  }
  if (typeof candidate !== "function") {
    throw new TypeError("Reflect.construct target must be a constructor");
  }
  return candidate;
};
var createSafeReflect = (constructors) => {
  const out = Object.create(null);
  for (const method of SAFE_REFLECT_METHODS) {
    const reflectMethod = Reflect[method];
    if (typeof reflectMethod !== "function") {
      continue;
    }
    defineLockedValue(out, method, reflectMethod.bind(Reflect));
  }
  defineLockedValue(out, "construct", (target, argArray, newTarget) => {
    const targetCtor = toConstructor(target, constructors);
    const newTargetCtor = newTarget == null
      ? targetCtor
      : toConstructor(newTarget, constructors);
    return Reflect.construct(targetCtor, Array.from(argArray), newTargetCtor);
  });
  return Object.freeze(out);
};
var createMembraneGlobal = (config = {}) => {
  const allowConsole = config.allowConsole === true;
  const allowCrypto = config.allowCrypto !== false;
  const allowPerformance = config.allowPerformance !== false;
  const membraneGlobal = Object.create(null);
  for (const name of SAFE_CORE_GLOBAL_NAMES) {
    const value = getHostGlobalValue(name);
    if (value === undefined) {
      continue;
    }
    defineLockedValue(membraneGlobal, name, value);
  }
  for (const name of SAFE_LITERAL_GLOBAL_NAMES) {
    defineLockedValue(membraneGlobal, name, getHostGlobalValue(name));
  }
  for (const name of SAFE_FUNCTION_GLOBAL_NAMES) {
    const bound = bindGlobalFunction(name);
    if (!bound) {
      continue;
    }
    defineLockedValue(membraneGlobal, name, bound);
  }
  defineLockedValue(membraneGlobal, "Math", createFrozenNamespace(Math));
  defineLockedValue(
    membraneGlobal,
    "JSON",
    Object.freeze(Object.create(null, {
      parse: {
        value: JSON.parse.bind(JSON),
        writable: false,
        configurable: false,
        enumerable: true,
      },
      stringify: {
        value: JSON.stringify.bind(JSON),
        writable: false,
        configurable: false,
        enumerable: true,
      },
    })),
  );
  defineLockedValue(
    membraneGlobal,
    "Reflect",
    createSafeReflect(config.reflectConstructors),
  );
  if (allowConsole) {
    defineLockedValue(membraneGlobal, "console", createSafeConsole());
  }
  if (allowCrypto) {
    const safeCrypto = createSafeCrypto();
    if (safeCrypto) {
      defineLockedValue(membraneGlobal, "crypto", safeCrypto);
    }
  }
  if (allowPerformance) {
    const safePerformance = createSafePerformance();
    if (safePerformance) {
      defineLockedValue(membraneGlobal, "performance", safePerformance);
    }
  }
  const additionalGlobals = config.additionalGlobals ?? {};
  const wrappers = config.customWrappers ?? {};
  for (const [name, originalValue] of Object.entries(additionalGlobals)) {
    assertAdditionalGlobalName(name);
    const wrapped = typeof wrappers[name] === "function"
      ? wrappers[name](originalValue)
      : originalValue;
    assertAdditionalGlobalValue(name, wrapped);
    freezeDeep(wrapped);
    defineLockedValue(membraneGlobal, name, wrapped);
  }
  defineLockedValue(membraneGlobal, "globalThis", membraneGlobal);
  defineLockedValue(membraneGlobal, "self", membraneGlobal);
  verifyNoRequire(membraneGlobal);
  return Object.freeze(membraneGlobal);
};

// src/worker/safety/strict-sandbox.ts
var ROOT_GLOBAL_RECORD = globalThis;
var STRICT_SECURE_CONSTRUCTOR = Symbol.for("knitting.strict.secureConstructor");
var STRICT_BLOCKED_GLOBALS = [
  "Bun",
  "Deno",
  "process",
  "WebAssembly",
  "fetch",
  "Worker",
  "SharedWorker",
  "XMLHttpRequest",
  "WebSocket",
  "EventSource",
  "Proxy",
  "require",
  "module",
];
var STRICT_IMPORT_OVERLAY_GLOBALS = [
  "Bun",
  "Deno",
  "process",
  "require",
  "module",
];
var STRICT_VM_BLOCKED_GLOBALS = STRICT_BLOCKED_GLOBALS.filter((name) =>
  name !== "require" && name !== "module"
);
var BLOCKED_REQUIRE_MODULE_MESSAGE = (binding) =>
  `[Knitting Strict] ${binding} is blocked. Use static imports in your task module.`;
var toFrozenIssue = (error) => String(error?.message ?? error).slice(0, 160);
var ignoreError2 = (action) => {
  try {
    action();
  } catch {}
};
var tryDefineProperty2 = (target, key, descriptor) => {
  ignoreError2(() => {
    Object.defineProperty(target, key, descriptor);
  });
};
var tryMirrorCallableMetadata = ({
  target,
  source,
  name,
}) => {
  tryDefineProperty2(target, "name", {
    value: name,
    configurable: true,
  });
  tryDefineProperty2(target, "length", {
    value: source.length,
    configurable: true,
  });
  tryDefineProperty2(target, "toString", {
    value: () => Function.prototype.toString.call(source),
    configurable: true,
  });
};
var require3 = createRequire2(import.meta.url);
var tsTranspiler = (() => {
  try {
    return require3("typescript");
  } catch {
    return;
  }
})();
var nodeVm = (() => {
  try {
    return require3("node:vm");
  } catch {
    return;
  }
})();
var shouldUseStrictSandbox = (protocol) =>
  protocol?.enabled === true && protocol.unsafe !== true &&
  protocol.mode === "strict" && protocol.strict.recursiveScan !== false &&
  protocol.strict.sandbox === true;
var toMutableMembraneGlobal = (frozenMembrane) => {
  const mutable = Object.create(null);
  for (const key of Reflect.ownKeys(frozenMembrane)) {
    const descriptor = Object.getOwnPropertyDescriptor(frozenMembrane, key);
    if (!descriptor) {
      continue;
    }
    if ("value" in descriptor) {
      Object.defineProperty(mutable, key, {
        value: descriptor.value,
        writable: true,
        configurable: true,
        enumerable: descriptor.enumerable ?? true,
      });
      continue;
    }
    Object.defineProperty(mutable, key, {
      get: descriptor.get,
      set: descriptor.set,
      configurable: true,
      enumerable: descriptor.enumerable ?? false,
    });
  }
  Object.defineProperty(mutable, "globalThis", {
    value: mutable,
    writable: true,
    configurable: true,
    enumerable: true,
  });
  Object.defineProperty(mutable, "self", {
    value: mutable,
    writable: true,
    configurable: true,
    enumerable: true,
  });
  return mutable;
};
var lockMembraneGlobal = (membraneGlobal) => {
  const ownKeys = Reflect.ownKeys(membraneGlobal);
  for (const key of ownKeys) {
    const descriptor = Object.getOwnPropertyDescriptor(membraneGlobal, key);
    if (!descriptor) {
      continue;
    }
    if ("value" in descriptor) {
      Object.defineProperty(membraneGlobal, key, {
        value: descriptor.value,
        writable: false,
        configurable: false,
        enumerable: descriptor.enumerable ?? true,
      });
      continue;
    }
    Object.defineProperty(membraneGlobal, key, {
      get: descriptor.get,
      set: undefined,
      configurable: false,
      enumerable: descriptor.enumerable ?? false,
    });
  }
  Object.freeze(membraneGlobal);
};
var defineMembraneValue = (membraneGlobal, key, value) => {
  Object.defineProperty(membraneGlobal, key, {
    value,
    writable: true,
    configurable: true,
    enumerable: true,
  });
};
var installVmBlockedGlobals = (membraneGlobal) => {
  for (const key of STRICT_VM_BLOCKED_GLOBALS) {
    if (Object.prototype.hasOwnProperty.call(membraneGlobal, key)) {
      continue;
    }
    defineMembraneValue(membraneGlobal, key, undefined);
  }
};
var wrapMembraneConstructor = ({
  originalCtor,
  origin,
  runScan,
  enter,
  begin,
  end,
}) => {
  if (originalCtor[STRICT_SECURE_CONSTRUCTOR] === true) {
    return originalCtor;
  }
  const secure = function (...args) {
    const nextDepth = enter(origin);
    runScan(
      args.map((value) => String(value)).join(`
`),
      origin,
      nextDepth,
    );
    begin();
    try {
      return Reflect.construct(
        originalCtor,
        args,
        new.target ? new.target : originalCtor,
      );
    } finally {
      end();
    }
  };
  tryMirrorCallableMetadata({
    target: secure,
    source: originalCtor,
    name: origin,
  });
  tryDefineProperty2(secure, STRICT_SECURE_CONSTRUCTOR, {
    value: true,
    configurable: true,
  });
  ignoreError2(() => {
    Object.setPrototypeOf(secure, originalCtor);
  });
  ignoreError2(() => {
    secure.prototype = originalCtor.prototype;
  });
  return secure;
};
var installInterceptorsOnMembrane = (membraneGlobal, strictOptions) => {
  const maxEvalDepth = strictOptions.maxEvalDepth;
  let evalDepth = 0;
  const runScan = (code, origin, depth) => {
    const source = `${origin}@depth-${depth}`;
    const result = scanCode(code, { depth, origin, source }, strictOptions);
    if (result.passed === true) {
      return;
    }
    throw new StrictModeViolationError({
      origin,
      depth,
      source,
      violations: result.violations,
      scannedCode: code,
    });
  };
  const enter = (origin) => {
    const nextDepth = evalDepth + 1;
    if (nextDepth >= maxEvalDepth) {
      throw new StrictModeDepthError({
        currentDepth: nextDepth,
        maxDepth: maxEvalDepth,
        origin,
      });
    }
    return nextDepth;
  };
  const begin = () => {
    evalDepth++;
  };
  const end = () => {
    evalDepth--;
  };
  const OriginalFunction = membraneGlobal.Function ?? Function;
  const GeneratorFunction = Object.getPrototypeOf(function* () {}).constructor;
  const AsyncFunction = Object.getPrototypeOf(async function () {}).constructor;
  const AsyncGeneratorFunction =
    Object.getPrototypeOf(async function* () {}).constructor;
  const wrapConstructor = (originalCtor, origin) =>
    wrapMembraneConstructor({
      originalCtor,
      origin,
      runScan,
      enter,
      begin,
      end,
    });
  const SecureFunction = wrapConstructor(OriginalFunction, "Function");
  const SecureGeneratorFunction = wrapConstructor(
    GeneratorFunction,
    "GeneratorFunction",
  );
  const SecureAsyncFunction = wrapConstructor(AsyncFunction, "AsyncFunction");
  const SecureAsyncGeneratorFunction = wrapConstructor(
    AsyncGeneratorFunction,
    "AsyncGeneratorFunction",
  );
  const originalEval = membraneGlobal.eval ?? globalThis.eval;
  const secureEval = (code) => {
    if (typeof code !== "string") {
      return code;
    }
    const nextDepth = enter("eval");
    runScan(code, "eval", nextDepth);
    begin();
    try {
      return Reflect.apply(originalEval, membraneGlobal, [code]);
    } finally {
      end();
    }
  };
  defineMembraneValue(membraneGlobal, "eval", secureEval);
  defineMembraneValue(membraneGlobal, "Function", SecureFunction);
  defineMembraneValue(
    membraneGlobal,
    "Reflect",
    createSafeReflect({
      originalFunction: OriginalFunction,
      secureFunction: SecureFunction,
      originalGeneratorFunction: GeneratorFunction,
      secureGeneratorFunction: SecureGeneratorFunction,
      originalAsyncFunction: AsyncFunction,
      secureAsyncFunction: SecureAsyncFunction,
      originalAsyncGeneratorFunction: AsyncGeneratorFunction,
      secureAsyncGeneratorFunction: SecureAsyncGeneratorFunction,
    }),
  );
  const wrapTimer = (originalTimer, origin) => (handler, ...rest) => {
    if (typeof handler === "string") {
      const nextDepth = enter(origin);
      runScan(handler, origin, nextDepth);
    }
    return Reflect.apply(originalTimer, globalThis, [handler, ...rest]);
  };
  for (
    const [name, origin] of [
      ["setTimeout", "setTimeout"],
      ["setInterval", "setInterval"],
    ]
  ) {
    const timer = globalThis[name];
    if (typeof timer !== "function") {
      continue;
    }
    defineMembraneValue(membraneGlobal, name, wrapTimer(timer, origin));
  }
  for (const name of ["clearTimeout", "clearInterval"]) {
    const clear = globalThis[name];
    if (typeof clear !== "function") {
      continue;
    }
    defineMembraneValue(membraneGlobal, name, clear.bind(globalThis));
  }
  return {
    OriginalFunction,
    GeneratorFunction,
    AsyncFunction,
    AsyncGeneratorFunction,
    SecureFunction,
    SecureGeneratorFunction,
    SecureAsyncFunction,
    SecureAsyncGeneratorFunction,
  };
};
var freezePrototypeChains = (bundle) => {
  for (
    const [prototype, constructorValue] of [
      [bundle.OriginalFunction.prototype, bundle.SecureFunction],
      [bundle.GeneratorFunction.prototype, bundle.SecureGeneratorFunction],
      [bundle.AsyncFunction.prototype, bundle.SecureAsyncFunction],
      [
        bundle.AsyncGeneratorFunction.prototype,
        bundle.SecureAsyncGeneratorFunction,
      ],
    ]
  ) {
    if (!prototype) {
      continue;
    }
    tryDefineProperty2(prototype, "constructor", {
      value: constructorValue,
      writable: false,
      configurable: false,
      enumerable: false,
    });
  }
};
var createBlockedRequireOrModuleDescriptor = (name) => ({
  get: () => {
    throw new Error(BLOCKED_REQUIRE_MODULE_MESSAGE(name));
  },
  configurable: true,
  enumerable: false,
});
var applyGlobalOverlay = (targetName, overlayDescriptor, state) => {
  const g = ROOT_GLOBAL_RECORD;
  const existing = Object.getOwnPropertyDescriptor(g, targetName);
  if (!existing || existing.configurable === true) {
    let defined = false;
    ignoreError2(() => {
      Object.defineProperty(g, targetName, overlayDescriptor);
      defined = true;
    });
    state.set(
      targetName,
      defined
        ? {
          mode: "defined",
          descriptor: existing,
        }
        : { mode: "skipped" },
    );
    return;
  }
  if ("value" in existing && existing.writable === true) {
    const previousValue = existing.value;
    const nextValue = "value" in overlayDescriptor
      ? overlayDescriptor.value
      : undefined;
    let assigned = false;
    ignoreError2(() => {
      g[targetName] = nextValue;
      assigned = true;
    });
    state.set(
      targetName,
      assigned
        ? {
          mode: "assigned",
          previousValue,
        }
        : { mode: "skipped" },
    );
    return;
  }
  state.set(targetName, { mode: "skipped" });
};
var restoreGlobalOverlay = (state) => {
  const g = globalThis;
  for (const [name, item] of state.entries()) {
    if (item.mode === "defined") {
      if (item.descriptor) {
        tryDefineProperty2(g, name, item.descriptor);
        continue;
      }
      ignoreError2(() => {
        Reflect.deleteProperty(g, name);
      });
      continue;
    }
    if (item.mode === "assigned") {
      ignoreError2(() => {
        g[name] = item.previousValue;
      });
    }
  }
};
var applyMembraneOverlay = (membraneGlobal, explicitNames) => {
  const globalNames = explicitNames ? new Set(explicitNames) : new Set([
    ...STRICT_BLOCKED_GLOBALS,
    ...Reflect.ownKeys(membraneGlobal).filter((key) => typeof key === "string"),
  ]);
  const overlayState = new Map();
  for (const name of globalNames) {
    const isMembraneValue = Object.prototype.hasOwnProperty.call(
      membraneGlobal,
      name,
    );
    const descriptor = isMembraneValue
      ? {
        value: membraneGlobal[name],
        writable: true,
        configurable: true,
        enumerable: true,
      }
      : name === "require" || name === "module"
      ? createBlockedRequireOrModuleDescriptor(name)
      : {
        value: undefined,
        writable: true,
        configurable: true,
        enumerable: true,
      };
    applyGlobalOverlay(name, descriptor, overlayState);
  }
  return overlayState;
};
var withMembraneOverlayAsync = async (membraneGlobal, action, names) => {
  const state = applyMembraneOverlay(membraneGlobal, names);
  try {
    return await action();
  } finally {
    restoreGlobalOverlay(state);
  }
};
var withOverlayQueue = async (runtime, work) => {
  const previous = runtime.overlayQueue;
  let release;
  runtime.overlayQueue = new Promise((resolve) => {
    release = resolve;
  });
  await previous;
  try {
    return await work();
  } finally {
    release?.();
  }
};
var createMembraneInjectedCallable = (target, membraneGlobal) => {
  const callable = target;
  const wrapped = function (...args) {
    const overlayState = applyMembraneOverlay(membraneGlobal);
    try {
      return Reflect.apply(callable, this, args);
    } finally {
      restoreGlobalOverlay(overlayState);
    }
  };
  tryMirrorCallableMetadata({
    target: wrapped,
    source: target,
    name: target.name || "strictSandboxInjectedCallable",
  });
  return wrapped;
};
var tryCreateVmContext = (membraneGlobal) => {
  if (!nodeVm) {
    return;
  }
  try {
    return nodeVm.createContext(
      membraneGlobal,
      createNodeVmDynamicImportOptions(),
    );
  } catch {
    return;
  }
};
var lockVmContextGlobalPrototype = (context, issues) => {
  if (!nodeVm) {
    return;
  }
  try {
    const script = new nodeVm.Script(
      "Object.setPrototypeOf(globalThis, null);",
    );
    script.runInContext(context);
  } catch (error) {
    issues.push(
      `[strict-sandbox] failed to lock vm global prototype: ${
        toFrozenIssue(error)
      }`,
    );
  }
};
var isTypeScriptFilePath = (filePath) =>
  filePath.endsWith(".ts") || filePath.endsWith(".mts") ||
  filePath.endsWith(".cts") || filePath.endsWith(".tsx");
var toModuleIdentifier = (specifier, parentIdentifier) => {
  if (specifier.startsWith("node:")) {
    return specifier;
  }
  if (path.isAbsolute(specifier)) {
    return pathToFileURL2(specifier).href;
  }
  if (parentIdentifier) {
    try {
      return new URL(specifier, parentIdentifier).href;
    } catch {}
  }
  try {
    return new URL(specifier).href;
  } catch {}
  return specifier;
};
var toModuleFilePath = (identifier) => {
  try {
    const parsed = new URL(identifier);
    if (parsed.protocol !== "file:") {
      return;
    }
    return fileURLToPath(parsed);
  } catch {
    return;
  }
};
var transpileModuleSource = ({
  source,
  filePath,
  runtime,
}) => {
  if (!isTypeScriptFilePath(filePath)) {
    return source;
  }
  if (!tsTranspiler) {
    runtime.issues.push(
      `[strict-sandbox] typescript transpiler unavailable for ${filePath}; using raw source`,
    );
    return source;
  }
  try {
    const out = tsTranspiler.transpileModule(source, {
      fileName: filePath,
      compilerOptions: {
        module: tsTranspiler.ModuleKind.ESNext,
        target: tsTranspiler.ScriptTarget.ES2022,
        sourceMap: false,
        inlineSources: false,
        inlineSourceMap: false,
      },
    });
    return out.outputText;
  } catch (error) {
    runtime.issues.push(
      `[strict-sandbox] transpile failed for ${filePath}: ${
        toFrozenIssue(error)
      }`,
    );
    return source;
  }
};
var createHostSyntheticModule = async ({
  identifier,
  runtime,
}) => {
  const SyntheticModule = nodeVm?.SyntheticModule;
  if (!SyntheticModule || !runtime.context) {
    throw new Error("SyntheticModule unavailable");
  }
  const hostModule = await import(identifier);
  const exportNames = Reflect.ownKeys(hostModule).filter((key) =>
    typeof key === "string"
  );
  const uniqueExports = [...new Set(exportNames)];
  const synthetic = new SyntheticModule(uniqueExports, function () {
    for (const name of uniqueExports) {
      this.setExport(name, hostModule[name]);
    }
  }, {
    context: runtime.context,
    identifier,
    ...createNodeVmDynamicImportOptions(),
  });
  return synthetic;
};
var createSourceTextModule = async ({
  identifier,
  runtime,
  loadModuleById,
}) => {
  const filePath = toModuleFilePath(identifier);
  const SourceTextModule = nodeVm?.SourceTextModule;
  if (!filePath || !SourceTextModule || !runtime.context) {
    throw new Error(`source module unavailable for ${identifier}`);
  }
  const source = readFileSync(filePath, "utf8");
  const preflight = scanCode(source, {
    depth: 0,
    origin: "preflight",
    source: filePath,
  }, runtime.strictOptions);
  if (preflight.passed !== true) {
    throw new StrictModeViolationError({
      origin: "preflight",
      depth: 0,
      source: filePath,
      violations: preflight.violations,
      scannedCode: source,
    });
  }
  const jsSource = transpileModuleSource({
    source,
    filePath,
    runtime,
  });
  const module = new SourceTextModule(jsSource, {
    context: runtime.context,
    identifier,
    initializeImportMeta: (meta) => {
      meta.url = identifier;
    },
    ...createNodeVmDynamicImportOptions(),
  });
  await module.link((specifier, referencingModule) => {
    const parent = referencingModule.identifier ?? identifier;
    const nextIdentifier = toModuleIdentifier(specifier, parent);
    return loadModuleById(nextIdentifier, parent);
  });
  return module;
};
var loadVmModuleByIdentifier = (identifier, runtime) => {
  const cached = runtime.vmModuleCache.get(identifier);
  if (cached) {
    return cached;
  }
  const pending = (async () => {
    const loadModuleById = (moduleIdentifier, _parentIdentifier) =>
      loadVmModuleByIdentifier(moduleIdentifier, runtime);
    try {
      return await createSourceTextModule({
        identifier,
        runtime,
        loadModuleById,
      });
    } catch (error) {
      runtime.issues.push(
        `[strict-sandbox] source module fallback for ${identifier}: ${
          toFrozenIssue(error)
        }`,
      );
      return await createHostSyntheticModule({
        identifier,
        runtime,
      });
    }
  })();
  runtime.vmModuleCache.set(identifier, pending);
  return pending;
};
var loadModuleInSandbox = async (moduleSpecifier, runtime) => {
  const fallbackHostImport = async () => {
    if (!runtime) {
      return {
        namespace: await import(moduleSpecifier),
        loadedInSandbox: false,
      };
    }
    const namespace = await withOverlayQueue(
      runtime,
      () =>
        withMembraneOverlayAsync(
          runtime.membraneGlobal,
          async () => await import(moduleSpecifier),
          STRICT_IMPORT_OVERLAY_GLOBALS,
        ),
    );
    return {
      namespace,
      loadedInSandbox: false,
    };
  };
  if (
    !runtime || !runtime.context || !runtime.vmEnabled ||
    !nodeVm?.SourceTextModule || !nodeVm?.SyntheticModule
  ) {
    return await fallbackHostImport();
  }
  const identifier = toModuleIdentifier(moduleSpecifier);
  const cachedNamespace = runtime.moduleNamespaceCache.get(identifier);
  if (cachedNamespace) {
    return {
      namespace: cachedNamespace,
      loadedInSandbox: true,
    };
  }
  try {
    const entryModule = await loadVmModuleByIdentifier(identifier, runtime);
    await entryModule.evaluate();
    const namespace = entryModule.namespace;
    runtime.moduleNamespaceCache.set(identifier, namespace);
    return {
      namespace,
      loadedInSandbox: true,
    };
  } catch (error) {
    runtime.issues.push(
      `[strict-sandbox] module load failed for ${identifier}: ${
        toFrozenIssue(error)
      }`,
    );
    return await fallbackHostImport();
  }
};
var tryCompileVmCallable = (runtime, target) => {
  if (!runtime.context || !nodeVm) {
    return;
  }
  const source = Function.prototype.toString.call(target);
  const filename = `strict-sandbox-task-${target.name || "anonymous"}.mjs`;
  try {
    const script = new nodeVm.Script(`(${source})`, {
      filename,
      ...createNodeVmDynamicImportOptions(),
    });
    const evaluated = script.runInContext(runtime.context, {
      displayErrors: true,
    });
    if (typeof evaluated === "function") {
      return evaluated;
    }
    runtime.issues.push(
      `[strict-sandbox] vm compile result for ${
        target.name || "anonymous"
      } was not callable`,
    );
    return;
  } catch (error) {
    runtime.issues.push(
      `[strict-sandbox] vm compile failed for ${target.name || "anonymous"}: ${
        toFrozenIssue(error)
      }`,
    );
    return;
  }
};
var isUnresolvedSandboxReference = (error) => {
  const message = String(error?.message ?? error);
  return message.includes("is not defined") ||
    message.includes("Cannot access") ||
    message.includes("before initialization");
};
var loadInSandbox = (target, runtime) => {
  if (!runtime) {
    return createInjectedStrictCallable(target);
  }
  const injectedFallback = createMembraneInjectedCallable(
    target,
    runtime.membraneGlobal,
  );
  const vmCallable = tryCompileVmCallable(runtime, target);
  if (!vmCallable) {
    return injectedFallback;
  }
  const wrapped = function (...args) {
    try {
      return Reflect.apply(vmCallable, this, args);
    } catch (error) {
      if (!isUnresolvedSandboxReference(error)) {
        throw error;
      }
      runtime.issues.push(
        `[strict-sandbox] unresolved reference fallback for ${
          target.name || "anonymous"
        }: ${toFrozenIssue(error)}`,
      );
      return Reflect.apply(injectedFallback, this, args);
    }
  };
  tryMirrorCallableMetadata({
    target: wrapped,
    source: target,
    name: target.name || "strictSandboxCallable",
  });
  return wrapped;
};
var bindContextSelfReferences = (membraneGlobal, context) => {
  const contextGlobal = context;
  defineMembraneValue(membraneGlobal, "globalThis", contextGlobal);
  defineMembraneValue(membraneGlobal, "self", contextGlobal);
};
var createStrictSandboxRuntime = (protocol) => {
  const strictOptions = resolveStrictModeOptions(protocol.strict);
  const issues = [];
  const frozenMembrane = createMembraneGlobal({
    allowConsole: protocol.allowConsole === true,
    allowCrypto: true,
    allowPerformance: true,
  });
  const membraneGlobal = toMutableMembraneGlobal(frozenMembrane);
  installVmBlockedGlobals(membraneGlobal);
  verifyNoRequire(membraneGlobal);
  const interceptors = installInterceptorsOnMembrane(
    membraneGlobal,
    strictOptions,
  );
  freezePrototypeChains(interceptors);
  const context = tryCreateVmContext(membraneGlobal);
  if (context) {
    lockVmContextGlobalPrototype(context, issues);
  }
  if (context) {
    bindContextSelfReferences(membraneGlobal, context);
  }
  lockMembraneGlobal(membraneGlobal);
  if (!context) {
    issues.push(
      "[strict-sandbox] node:vm unavailable; using membrane injected call fallback",
    );
  } else if (!nodeVm?.SourceTextModule || !nodeVm?.SyntheticModule) {
    issues.push(
      "[strict-sandbox] vm modules unavailable (missing --experimental-vm-modules); module-level sandbox loader disabled",
    );
  }
  return {
    membraneGlobal,
    strictOptions,
    context,
    vmEnabled: Boolean(
      context && nodeVm?.SourceTextModule && nodeVm?.SyntheticModule,
    ),
    issues,
    vmModuleCache: new Map(),
    moduleNamespaceCache: new Map(),
    overlayQueue: Promise.resolve(),
  };
};
var ensureStrictSandboxRuntime = (protocol) => {
  if (!protocol || !shouldUseStrictSandbox(protocol)) {
    return;
  }
  const g = globalThis;
  if (g.__knittingStrictSandboxRuntime) {
    return g.__knittingStrictSandboxRuntime;
  }
  const runtime = createStrictSandboxRuntime(protocol);
  g.__knittingStrictSandboxRuntime = runtime;
  return runtime;
};

// src/worker/get-functions.ts
var normalizeTimeout = (timeout) => {
  if (timeout == null) {
    return;
  }
  if (typeof timeout === "number") {
    const ms2 = Math.floor(timeout);
    return ms2 >= 0
      ? { ms: ms2, kind: 0, /* Reject */ value: new Error("Task timeout") }
      : undefined;
  }
  const ms = Math.floor(timeout.time);
  if (!(ms >= 0)) {
    return;
  }
  if ("default" in timeout) {
    return { ms, kind: 1, /* Resolve */ value: timeout.default };
  }
  if (timeout.maybe === true) {
    return { ms, kind: 1, /* Resolve */ value: undefined };
  }
  if ("error" in timeout) {
    return { ms, kind: 0, /* Reject */ value: timeout.error };
  }
  return { ms, kind: 0, /* Reject */ value: new Error("Task timeout") };
};
var toValueTag = Object.prototype.toString;
var isPromiseAcrossRealms = (value) =>
  value instanceof Promise ||
  typeof value === "object" && value !== null &&
    toValueTag.call(value) === "[object Promise]";
var cloneToHostRealm = (value) => {
  const clone = globalThis.structuredClone;
  if (typeof clone !== "function") {
    return value;
  }
  try {
    return clone(value);
  } catch {
    return value;
  }
};
var wrapSandboxLoadedCallable = (fn) => {
  const wrapped = (args, abortToolkit) => {
    const out = fn(args, abortToolkit);
    if (!isPromiseAcrossRealms(out)) {
      return cloneToHostRealm(out);
    }
    return Promise.resolve(out).then(
      (value) => cloneToHostRealm(value),
      (error) => Promise.reject(cloneToHostRealm(error)),
    );
  };
  try {
    Object.defineProperty(wrapped, "name", {
      value: fn.name || "strictSandboxLoadedCallable",
      configurable: true,
    });
  } catch {}
  try {
    Object.defineProperty(wrapped, "length", {
      value: fn.length,
      configurable: true,
    });
  } catch {}
  try {
    Object.defineProperty(wrapped, "toString", {
      value: () => Function.prototype.toString.call(fn),
      configurable: true,
    });
  } catch {}
  return wrapped;
};
var composeWorkerCallable = (fixed, permission, loadedInSandbox) => {
  const fn = fixed.f;
  if (loadedInSandbox === true) {
    return wrapSandboxLoadedCallable(fn);
  }
  const shouldInjectStrictCaller = permission?.enabled === true &&
    permission.unsafe !== true && permission.mode === "strict" &&
    permission.strict.recursiveScan !== false;
  if (!shouldInjectStrictCaller) {
    return fn;
  }
  const shouldUseStrictSandbox2 = permission?.strict.sandbox === true;
  if (!shouldUseStrictSandbox2) {
    return createInjectedStrictCallable(fn);
  }
  const sandboxRuntime = ensureStrictSandboxRuntime(permission);
  if (!sandboxRuntime) {
    return createInjectedStrictCallable(fn);
  }
  return loadInSandbox(fn, sandboxRuntime);
};
var getFunctions = async ({ list, ids, at, permission }) => {
  const modules = list.map((specifier) => toModuleUrl(specifier));
  const shouldUseStrictSandbox2 = permission?.enabled === true &&
    permission.unsafe !== true && permission.mode === "strict" &&
    permission.strict.recursiveScan !== false &&
    permission.strict.sandbox === true;
  const sandboxRuntime = shouldUseStrictSandbox2
    ? ensureStrictSandboxRuntime(permission)
    : undefined;
  const results = await Promise.all(modules.map(async (imports) => {
    const loadedModule = sandboxRuntime
      ? await loadModuleInSandbox(imports, sandboxRuntime)
      : {
        namespace: await import(imports),
        loadedInSandbox: false,
      };
    const module = loadedModule.namespace;
    return Object.entries(module).filter(([_, value]) =>
      value != null && typeof value === "object" &&
      value?.[endpointSymbol] === true
    ).map(([name, value]) => ({
      ...value,
      name,
      __knittingLoadedInSandbox: loadedModule.loadedInSandbox,
    }));
  }));
  const flattened = results.flat();
  const useAtFilter = modules.length === 1 && at.length > 0;
  const atSet = useAtFilter ? new Set(at) : null;
  const targetModule = useAtFilter ? modules[0] : null;
  const flattenedResults = flattened.filter((obj) =>
    useAtFilter
      ? obj.importedFrom === targetModule && atSet.has(obj.at)
      : ids.includes(obj.id)
  ).sort((a, b) => a.name.localeCompare(b.name));
  return flattenedResults.map((fixed) => ({
    ...fixed,
    run: composeWorkerCallable(
      fixed,
      permission,
      fixed.__knittingLoadedInSandbox === true,
    ),
    timeout: normalizeTimeout(fixed.timeout),
  }));
};

// src/worker/timers.ts
var maybeGc = (() => {
  const host = globalThis;
  const gc = typeof host.gc === "function"
    ? host.gc.bind(globalThis)
    : undefined;
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
  if (!a_pause || forNanoseconds <= 0) {
    return () => {};
  }
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
}) => {
  const pause = pauseInNanoseconds !== undefined
    ? whilePausing({ pauseInNanoseconds })
    : pauseGeneric;
  const tryProgress = () => {
    let progressed = false;
    if (enqueueLock()) {
      progressed = true;
    }
    if (write) {
      const wrote = write();
      if (typeof wrote === "number") {
        if (wrote > 0) {
          progressed = true;
        }
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
      if (a_load(opView, at) !== value || txStatus[0 /* thisIsAHint */] === 1) {
        return;
      }
      if (tryProgress()) {
        return;
      }
      pause();
      if ((spinChecks++ & 63) === 0 && p_now2() >= until) {
        break;
      }
    }
    if (tryProgress()) {
      return;
    }
    a_store2(rxStatus, 0, 0);
    a_wait(opView, at, value, parkMs ?? 60);
    a_store2(rxStatus, 0, 1);
  };
};

// src/worker/safety/process.ts
var installTerminationGuard = () => {
  if (typeof process === "undefined") {
    return;
  }
  const proc = process;
  if (proc.__knittingTerminationGuard === true) {
    return;
  }
  proc.__knittingTerminationGuard = true;
  const blocked = (name) => {
    throw new Error(
      `KNT_ERROR_PROCESS_GUARD: ${name} is disabled in worker tasks`,
    );
  };
  const guardMethod = (name) => {
    try {
      Object.defineProperty(proc, name, {
        configurable: false,
        writable: false,
        value: (..._args) => blocked(`process.${name}`),
      });
    } catch {}
  };
  guardMethod("exit");
  guardMethod("kill");
  guardMethod("abort");
  guardMethod("reallyExit");
  const globalScope = globalThis;
  if (globalScope.Bun && typeof globalScope.Bun.exit === "function") {
    try {
      Object.defineProperty(globalScope.Bun, "exit", {
        configurable: false,
        writable: false,
        value: (_code) => blocked("Bun.exit"),
      });
    } catch {}
  }
  if (globalScope.Deno && typeof globalScope.Deno.exit === "function") {
    try {
      Object.defineProperty(globalScope.Deno, "exit", {
        configurable: false,
        writable: false,
        value: (_code) => blocked("Deno.exit"),
      });
    } catch {}
  }
};
var installUnhandledRejectionSilencer = () => {
  if (typeof process === "undefined" || typeof process.on !== "function") {
    return;
  }
  const proc = process;
  if (proc.__knittingUnhandledRejectionSilencer === true) {
    return;
  }
  proc.__knittingUnhandledRejectionSilencer = true;
  process.on("unhandledRejection", () => {});
};
// src/worker/safety/performance.ts
var installPerformanceNowGuard = () => {
  const g = globalThis;
  if (g.__knittingPerformanceNowGuardInstalled === true) {
    return;
  }
  g.__knittingPerformanceNowGuardInstalled = true;
  const perf = globalThis.performance;
  if (!perf || typeof perf.now !== "function") {
    return;
  }
  try {
    perf.now();
  } catch {}
};
// src/worker/safety/permission.ts
import path2 from "node:path";
import { createRequire as createRequire3 } from "node:module";
import { fileURLToPath as fileURLToPath2 } from "node:url";
var WRAPPED = Symbol.for("knitting.permission.wrapped");
var require4 = createRequire3(import.meta.url);
var fsApi = (() => {
  try {
    return require4("node:fs");
  } catch {
    return;
  }
})();
var rawExistsSync = typeof fsApi?.existsSync === "function"
  ? fsApi.existsSync
  : undefined;
var rawRealpathSync = (() => {
  const maybe = fsApi?.realpathSync?.native ?? fsApi?.realpathSync;
  return typeof maybe === "function" ? maybe : undefined;
})();
var maybeSyncBuiltinESMExports = (() => {
  try {
    const moduleApi = require4("node:module");
    return moduleApi.syncBuiltinESMExports;
  } catch {
    return;
  }
})();
var isPathWithin = (base, candidate) => {
  const relative = path2.relative(base, candidate);
  return relative === "" ||
    !relative.startsWith("..") && !path2.isAbsolute(relative);
};
var toStringPath = (value) => {
  if (typeof value === "string") {
    return value;
  }
  if (value instanceof URL) {
    if (value.protocol === "file:") {
      return fileURLToPath2(value);
    }
    return;
  }
  if (
    typeof value === "object" && value !== null && "toString" in value &&
    typeof value.toString === "function"
  ) {
    const out = String(value.toString());
    return out.length > 0 ? out : undefined;
  }
  return;
};
var toAbsolutePath = (value, cwd) => {
  const raw = toStringPath(value);
  if (!raw) {
    return;
  }
  if (path2.isAbsolute(raw)) {
    return path2.resolve(raw);
  }
  try {
    const parsed = new URL(raw);
    if (parsed.protocol !== "file:") {
      return;
    }
    return path2.resolve(fileURLToPath2(parsed));
  } catch {
    return path2.resolve(cwd, raw);
  }
};
var shouldDenyPath = (value, cwd, denied) => {
  const resolveCanonical = (candidate) => {
    const realpath = rawRealpathSync;
    const direct = (() => {
      if (!realpath) {
        return;
      }
      try {
        return realpath(candidate);
      } catch {
        return;
      }
    })();
    if (direct) {
      return path2.resolve(direct);
    }
    if (!rawExistsSync || !realpath) {
      return path2.resolve(candidate);
    }
    const missingSegments = [];
    let cursor = path2.resolve(candidate);
    while (!rawExistsSync(cursor)) {
      const parent = path2.dirname(cursor);
      if (parent === cursor) {
        return path2.resolve(candidate);
      }
      missingSegments.push(path2.basename(cursor));
      cursor = parent;
    }
    let base = cursor;
    try {
      base = realpath(cursor);
    } catch {}
    let rebuilt = base;
    for (let i = missingSegments.length - 1; i >= 0; i--) {
      rebuilt = path2.join(rebuilt, missingSegments[i]);
    }
    return path2.resolve(rebuilt);
  };
  const absolute = toAbsolutePath(value, cwd);
  if (!absolute) {
    return false;
  }
  const resolved = resolveCanonical(absolute);
  return denied.some((deny) => isPathWithin(deny, resolved));
};
var isNodeOpenForWrite = (flag) => {
  if (typeof flag === "string") {
    return /[wa+]/.test(flag);
  }
  if (typeof flag === "number") {
    return true;
  }
  if (typeof flag === "object" && flag !== null && "flags" in flag) {
    return isNodeOpenForWrite(flag.flags);
  }
  return false;
};
var isNodeOpenForRead = (flag) => {
  if (typeof flag === "string") {
    return /r/.test(flag);
  }
  if (typeof flag === "number") {
    return true;
  }
  if (typeof flag === "object" && flag !== null && "flags" in flag) {
    return isNodeOpenForRead(flag.flags);
  }
  return true;
};
var isDenoOpenForWrite = (options) => {
  if (!options || typeof options !== "object") {
    return false;
  }
  const o = options;
  return o.write === true || o.append === true || o.create === true ||
    o.truncate === true;
};
var throwDeniedAccess = (target, mode) => {
  throw new Error(
    `KNT_ERROR_PERMISSION_DENIED: ${mode} access denied for ${String(target)}`,
  );
};
var safeWrap = (target, method, check) => {
  try {
    const original = target[method];
    if (typeof original !== "function") {
      return;
    }
    if (original[WRAPPED] === true) {
      return;
    }
    const wrapped = function (...args) {
      const denied = check(args);
      if (denied) {
        return throwDeniedAccess(denied.target, denied.mode);
      }
      return Reflect.apply(original, this, args);
    };
    wrapped[WRAPPED] = true;
    target[method] = wrapped;
  } catch {}
};
var wrapMethods = (target, methods, check) => {
  for (const method of methods) {
    safeWrap(target, method, check);
  }
};
var wrapMethodsAndSync = (target, methods, check) => {
  for (const method of methods) {
    safeWrap(target, method, check);
    safeWrap(target, `${method}Sync`, check);
  }
};
var createAccessChecks = ({
  cwd,
  denyRead,
  denyWrite,
}) => {
  const readAt = (index) => (args) =>
    shouldDenyPath(args[index], cwd, denyRead)
      ? { target: args[index], mode: "read" }
      : undefined;
  const writeAt = (index) => (args) =>
    shouldDenyPath(args[index], cwd, denyWrite)
      ? { target: args[index], mode: "write" }
      : undefined;
  const readWriteAt = (readIndex, writeIndex) => (args) =>
    readAt(readIndex)(args) ?? writeAt(writeIndex)(args);
  const nodeOpen = (args) => {
    if (isNodeOpenForWrite(args[1])) {
      return writeAt(0)(args);
    }
    if (isNodeOpenForRead(args[1])) {
      return readAt(0)(args);
    }
    return;
  };
  const denoOpen = (args) =>
    isDenoOpenForWrite(args[1]) ? writeAt(0)(args) : readAt(0)(args);
  return {
    readAt,
    writeAt,
    readWriteAt,
    nodeOpen,
    denoOpen,
  };
};
var installConsoleGuard = () => {
  const g = globalThis;
  if (g.__knittingConsoleGuardInstalled === true) {
    return;
  }
  g.__knittingConsoleGuardInstalled = true;
  if (!g.console || typeof g.console !== "object") {
    return;
  }
  const noop = () => {};
  for (
    const method of [
      "log",
      "info",
      "warn",
      "error",
      "debug",
      "trace",
      "dir",
      "dirxml",
      "table",
    ]
  ) {
    try {
      Object.defineProperty(g.console, method, {
        configurable: false,
        writable: false,
        value: noop,
      });
    } catch {
      try {
        g.console[method] = noop;
      } catch {}
    }
  }
};
var installNodeFsGuard = ({
  cwd,
  denyRead,
  denyWrite,
}) => {
  try {
    const fsModule = require4("node:fs");
    const checks = createAccessChecks({ cwd, denyRead, denyWrite });
    wrapMethods(fsModule, [
      "writeFile",
      "writeFileSync",
      "appendFile",
      "appendFileSync",
      "truncate",
      "truncateSync",
      "unlink",
      "unlinkSync",
      "rm",
      "rmSync",
      "rmdir",
      "rmdirSync",
      "mkdir",
      "mkdirSync",
      "chmod",
      "chmodSync",
      "chown",
      "chownSync",
      "utimes",
      "utimesSync",
      "createWriteStream",
    ], checks.writeAt(0));
    wrapMethods(fsModule, [
      "readFile",
      "readFileSync",
      "readdir",
      "readdirSync",
      "stat",
      "statSync",
      "lstat",
      "lstatSync",
      "readlink",
      "readlinkSync",
      "realpath",
      "realpathSync",
      "opendir",
      "opendirSync",
      "access",
      "accessSync",
      "createReadStream",
      "watch",
      "watchFile",
    ], checks.readAt(0));
    wrapMethods(
      fsModule,
      ["rename", "renameSync", "copyFile", "copyFileSync"],
      checks.readWriteAt(0, 1),
    );
    safeWrap(fsModule, "open", checks.nodeOpen);
    safeWrap(fsModule, "openSync", checks.nodeOpen);
    const promises = fsModule.promises;
    if (!promises) {
      return;
    }
    wrapMethods(promises, [
      "writeFile",
      "appendFile",
      "truncate",
      "unlink",
      "rm",
      "rmdir",
      "mkdir",
      "chmod",
      "chown",
      "utimes",
    ], checks.writeAt(0));
    wrapMethods(promises, [
      "readFile",
      "readdir",
      "stat",
      "lstat",
      "readlink",
      "realpath",
      "opendir",
      "access",
      "watch",
    ], checks.readAt(0));
    wrapMethods(promises, ["rename", "copyFile"], checks.readWriteAt(0, 1));
    safeWrap(promises, "open", checks.nodeOpen);
    maybeSyncBuiltinESMExports?.();
  } catch {}
};
var installNodeProcessGuard = () => {
  try {
    const childProcess = require4("node:child_process");
    const runAt = (index, fallback) => (args) => ({
      target: args[index] ?? fallback,
      mode: "run",
    });
    wrapMethods(childProcess, [
      "spawn",
      "spawnSync",
      "exec",
      "execSync",
      "execFile",
      "execFileSync",
      "fork",
    ], runAt(0, "node:child_process"));
    maybeSyncBuiltinESMExports?.();
  } catch {}
};
var installNodeInternalsGuard = () => {
  if (typeof process === "undefined") {
    return;
  }
  const proc = process;
  const block = (name) => {
    throw new Error(
      `KNT_ERROR_PERMISSION_DENIED: run access denied for ${name}`,
    );
  };
  const dangerousBindingNames = new Set(["spawn_sync", "spawn_wrap"]);
  const wrapBinding = (method) => {
    const original = proc[method];
    if (typeof original !== "function") {
      return;
    }
    if (original[WRAPPED] === true) {
      return;
    }
    const wrapped = (name, ...rest) => {
      if (dangerousBindingNames.has(name)) {
        return block(`process.${method}(${name})`);
      }
      return Reflect.apply(original, proc, [name, ...rest]);
    };
    wrapped[WRAPPED] = true;
    try {
      Object.defineProperty(proc, method, {
        configurable: false,
        writable: false,
        value: wrapped,
      });
    } catch {
      try {
        proc[method] = wrapped;
      } catch {}
    }
  };
  wrapBinding("binding");
  wrapBinding("_linkedBinding");
  const originalDlopen = proc.dlopen;
  if (
    typeof originalDlopen === "function" && originalDlopen[WRAPPED] !== true
  ) {
    const wrappedDlopen = (..._args) => block("process.dlopen");
    wrappedDlopen[WRAPPED] = true;
    try {
      Object.defineProperty(proc, "dlopen", {
        configurable: false,
        writable: false,
        value: wrappedDlopen,
      });
    } catch {
      try {
        proc.dlopen = wrappedDlopen;
      } catch {}
    }
  }
};
var installWorkerSpawnGuard = () => {
  const g = globalThis;
  if (g.__knittingWorkerSpawnGuardInstalled === true) {
    return;
  }
  g.__knittingWorkerSpawnGuardInstalled = true;
  const blockWorker = (name) => {
    throw new Error(
      `KNT_ERROR_PERMISSION_DENIED: run access denied for ${name}`,
    );
  };
  try {
    const workerThreads = require4("node:worker_threads");
    if (
      typeof workerThreads.Worker === "function" &&
      workerThreads.Worker[WRAPPED] !== true
    ) {
      const original = workerThreads.Worker;
      const wrapped = new Proxy(original, {
        apply() {
          return blockWorker("node:worker_threads.Worker");
        },
        construct() {
          return blockWorker("node:worker_threads.Worker");
        },
      });
      wrapped[WRAPPED] = true;
      workerThreads.Worker = wrapped;
      maybeSyncBuiltinESMExports?.();
    }
  } catch {}
  const globalWorker = g.Worker;
  if (typeof globalWorker === "function" && globalWorker[WRAPPED] !== true) {
    try {
      const wrapped = new Proxy(globalWorker, {
        construct() {
          return blockWorker("Worker");
        },
      });
      wrapped[WRAPPED] = true;
      g.Worker = wrapped;
    } catch {}
  }
};
var installDenoGuard = ({
  cwd,
  denyRead,
  denyWrite,
  allowRun,
}) => {
  const g = globalThis;
  const deno = g.Deno;
  if (!deno) {
    return;
  }
  const checks = createAccessChecks({ cwd, denyRead, denyWrite });
  wrapMethodsAndSync(deno, [
    "writeFile",
    "writeTextFile",
    "remove",
    "truncate",
    "mkdir",
    "chmod",
    "chown",
    "create",
  ], checks.writeAt(0));
  wrapMethodsAndSync(deno, [
    "readFile",
    "readTextFile",
    "readDir",
    "readLink",
    "stat",
    "lstat",
    "realPath",
    "watchFs",
  ], checks.readAt(0));
  safeWrap(deno, "open", checks.denoOpen);
  safeWrap(deno, "openSync", checks.denoOpen);
  wrapMethodsAndSync(
    deno,
    ["rename", "copyFile", "link", "symlink"],
    checks.readWriteAt(0, 1),
  );
  if (allowRun !== true) {
    const runAt = (index, fallback) => (args) => ({
      target: args[index] ?? fallback,
      mode: "run",
    });
    wrapMethods(
      deno,
      ["run", "spawn", "spawnSync", "spawnChild"],
      runAt(0, "Deno.Command"),
    );
    try {
      const command = deno.Command;
      if (typeof command === "function" && command[WRAPPED] !== true) {
        const wrapped = new Proxy(command, {
          construct(_target, args) {
            return throwDeniedAccess(args[0] ?? "Deno.Command", "run");
          },
        });
        wrapped[WRAPPED] = true;
        deno.Command = wrapped;
      }
    } catch {}
  }
};
var installBunGuard = ({
  cwd,
  denyRead,
  denyWrite,
  allowRun,
}) => {
  const g = globalThis;
  const bun = g.Bun;
  if (!bun) {
    return;
  }
  const checks = createAccessChecks({ cwd, denyRead, denyWrite });
  safeWrap(bun, "write", checks.writeAt(0));
  safeWrap(bun, "file", checks.readAt(0));
  safeWrap(bun, "dlopen", (_args) => ({
    target: "Bun.dlopen",
    mode: "run",
  }));
  safeWrap(bun, "linkSymbols", (_args) => ({
    target: "Bun.linkSymbols",
    mode: "run",
  }));
  if (allowRun !== true) {
    const runAt = (index, fallback) => (args) => ({
      target: args[index] ?? fallback,
      mode: "run",
    });
    wrapMethods(bun, ["spawn", "spawnSync", "$"], runAt(0, "Bun.spawn"));
  }
};
var installWritePermissionGuard = (protocol) => {
  if (!protocol || protocol.enabled !== true) {
    return;
  }
  if (protocol.allowConsole !== true) {
    installConsoleGuard();
  }
  if (protocol.unsafe === true) {
    return;
  }
  const g = globalThis;
  if (g.__knittingPermissionGuardInstalled === true) {
    return;
  }
  g.__knittingPermissionGuardInstalled = true;
  if (protocol.node.allowChildProcess !== true) {
    installNodeProcessGuard();
    installNodeInternalsGuard();
    installWorkerSpawnGuard();
  }
  const { cwd, denyRead, denyWrite } = protocol;
  if (
    (!Array.isArray(denyRead) || denyRead.length === 0) &&
    (!Array.isArray(denyWrite) || denyWrite.length === 0)
  ) {
    return;
  }
  installNodeFsGuard({ cwd, denyRead, denyWrite });
  installDenoGuard({
    cwd,
    denyRead,
    denyWrite,
    allowRun: protocol.deno.allowRun,
  });
  installBunGuard({
    cwd,
    denyRead,
    denyWrite,
    allowRun: protocol.bun.allowRun,
  });
};
// src/worker/safety/strict-mode.ts
var STRICT_SECURE_CONSTRUCTOR2 = Symbol.for(
  "knitting.strict.secureConstructor",
);
var ignoreError3 = (action) => {
  try {
    action();
  } catch {}
};
var tryDefineProperty3 = (defineProperty, target, property, descriptor) => {
  ignoreError3(() => {
    defineProperty(target, property, descriptor);
  });
};
var markProtectedProperty = (state, target, property) => {
  const set = state.get(target) ?? new Set();
  set.add(property);
  state.set(target, set);
};
var isProtectedProperty = (state, target, property) =>
  state.get(target)?.has(property) === true;
var defineLockedProperty = (
  defineProperty,
  protectedState,
  target,
  property,
  value,
) =>
  defineLockedDescriptor(defineProperty, protectedState, target, property, {
    value,
    writable: false,
    enumerable: true,
  });
var defineLockedDescriptor = (
  defineProperty,
  protectedState,
  target,
  property,
  descriptor,
) => {
  defineProperty(target, property, {
    ...descriptor,
    configurable: false,
    enumerable: descriptor.enumerable ?? false,
  });
  markProtectedProperty(protectedState, target, property);
};
var shouldInstallStrictRuntimeGuard = (protocol) =>
  protocol?.enabled === true && protocol.unsafe !== true &&
  protocol.mode === "strict";
var installStrictModeRuntimeGuard = (protocol) => {
  if (!shouldInstallStrictRuntimeGuard(protocol)) {
    return;
  }
  const strictOptions = resolveStrictModeOptions(protocol?.strict);
  if (strictOptions.recursiveScan === false) {
    return;
  }
  const g = globalThis;
  if (g.__knittingStrictRuntimeGuardInstalled === true) {
    return;
  }
  try {
    const maxEvalDepth = strictOptions.maxEvalDepth;
    const protectedState = new WeakMap();
    const originalDefineProperty = Object.defineProperty;
    let evalDepth = 0;
    const lockValue = (target, property, value) => {
      defineLockedProperty(
        originalDefineProperty,
        protectedState,
        target,
        property,
        value,
      );
    };
    const withScannedExecution = (origin, source, run) => {
      const nextDepth = enter(origin);
      runScan(source, origin, nextDepth);
      evalDepth++;
      try {
        return run();
      } finally {
        evalDepth--;
      }
    };
    if (RUNTIME === "bun") {
      for (const binding of ["require", "module"]) {
        const existing = Object.getOwnPropertyDescriptor(globalThis, binding);
        if (
          existing?.configurable === false &&
          isBlockedBindingDescriptor(existing) !== true
        ) {
          throw new Error(
            `KNT_ERROR_PERMISSION_DENIED: strict mode cannot lock global ${binding}`,
          );
        }
        defineLockedDescriptor(
          originalDefineProperty,
          protectedState,
          globalThis,
          binding,
          createBlockedBindingDescriptor(binding),
        );
      }
      verifyNoRequire(globalThis);
    }
    const runScan = (code, origin, depth) => {
      const source = `${origin}@depth-${depth}`;
      const result = scanCode(code, { depth, origin, source }, strictOptions);
      if (result.passed === true) {
        return;
      }
      throw new StrictModeViolationError({
        origin,
        depth,
        source,
        violations: result.violations,
        scannedCode: code,
      });
    };
    const enter = (origin) => {
      const nextDepth = evalDepth + 1;
      if (nextDepth >= maxEvalDepth) {
        throw new StrictModeDepthError({
          currentDepth: nextDepth,
          maxDepth: maxEvalDepth,
          origin,
        });
      }
      return nextDepth;
    };
    const wrapConstructor = (originalCtor, origin) => {
      if (originalCtor[STRICT_SECURE_CONSTRUCTOR2] === true) {
        return originalCtor;
      }
      const secure = function (...args) {
        return withScannedExecution(
          origin,
          args.map((value) => String(value)).join(`
`),
          () =>
            Reflect.construct(
              originalCtor,
              args,
              new.target ? new.target : originalCtor,
            ),
        );
      };
      tryDefineProperty3(originalDefineProperty, secure, "name", {
        value: origin,
      });
      tryDefineProperty3(
        originalDefineProperty,
        secure,
        STRICT_SECURE_CONSTRUCTOR2,
        { value: true },
      );
      return secure;
    };
    const originalEval = globalThis.eval;
    const secureEval = function (code) {
      if (typeof code !== "string") {
        return code;
      }
      return withScannedExecution(
        "eval",
        code,
        () => Reflect.apply(originalEval, globalThis, [code]),
      );
    };
    const OriginalFunction = Function;
    const GeneratorFunction =
      Object.getPrototypeOf(function* () {}).constructor;
    const AsyncFunction =
      Object.getPrototypeOf(async function () {}).constructor;
    const AsyncGeneratorFunction =
      Object.getPrototypeOf(async function* () {}).constructor;
    const SecureFunction = wrapConstructor(OriginalFunction, "Function");
    const SecureGeneratorFunction = wrapConstructor(
      GeneratorFunction,
      "GeneratorFunction",
    );
    const SecureAsyncFunction = wrapConstructor(AsyncFunction, "AsyncFunction");
    const SecureAsyncGeneratorFunction = wrapConstructor(
      AsyncGeneratorFunction,
      "AsyncGeneratorFunction",
    );
    lockValue(globalThis, "eval", secureEval);
    lockValue(globalThis, "Function", SecureFunction);
    for (
      const [prototype, ctor] of [
        [OriginalFunction.prototype, SecureFunction],
        [GeneratorFunction.prototype, SecureGeneratorFunction],
        [AsyncFunction.prototype, SecureAsyncFunction],
        [AsyncGeneratorFunction.prototype, SecureAsyncGeneratorFunction],
      ]
    ) {
      lockValue(prototype, "constructor", ctor);
    }
    const wrapTimer = (originalTimer, origin) => (handler, ...rest) => {
      if (typeof handler === "string") {
        const nextDepth = enter(origin);
        runScan(handler, origin, nextDepth);
      }
      return Reflect.apply(originalTimer, globalThis, [handler, ...rest]);
    };
    for (
      const [name, origin] of [
        ["setTimeout", "setTimeout"],
        ["setInterval", "setInterval"],
      ]
    ) {
      const timer = globalThis[name];
      if (typeof timer !== "function") {
        continue;
      }
      lockValue(globalThis, name, wrapTimer(timer, origin));
    }
    const secureDefineProperty = (target, property, descriptor) => {
      if (isProtectedProperty(protectedState, target, property)) {
        throw new Error(
          `KNT_ERROR_PERMISSION_DENIED: strict mode lock for ${
            String(property)
          }`,
        );
      }
      return Reflect.apply(originalDefineProperty, Object, [
        target,
        property,
        descriptor,
      ]);
    };
    lockValue(Object, "defineProperty", secureDefineProperty);
    g.__knittingStrictRuntimeGuardInstalled = true;
  } catch (error) {
    g.__knittingStrictRuntimeGuardInstalled = false;
    throw error;
  }
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
var hasLockBuffers = (value) =>
  !!value?.headers && !!value?.lockSector && !!value?.payload &&
  !!value?.payloadSector;
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
  if (listOfFunctions.length > 0) {
    return;
  }
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
  maxSignals,
}) => {
  const atomicView = new Uint32Array(sab);
  const size = atomicView.length;
  const inUse = new Uint32Array(size);
  const physicalMax = size * SLOT_BITS;
  const max = (() => {
    if (!Number.isFinite(maxSignals)) {
      return physicalMax;
    }
    const parsed = Math.floor(maxSignals);
    if (parsed <= 0) {
      return physicalMax;
    }
    return Math.min(parsed, physicalMax);
  })();
  const closeNow = max + 1;
  let current = 0;
  let cursor = 0;
  const getSignal = () => {
    if (current >= max) {
      return closeNow;
    }
    for (let step = 0; step < size; step++) {
      const word = (cursor + step) % size;
      const wordBase = word << 5;
      const remaining = max - wordBase;
      if (remaining <= 0) {
        continue;
      }
      const allowedMask = remaining >= SLOT_BITS
        ? 4294967295
        : (1 << remaining) - 1 >>> 0;
      const freeBits = (~inUse[word] & allowedMask) >>> 0;
      if (freeBits === 0) {
        continue;
      }
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
    if (signal === closeNow) {
      return 0;
    }
    if (!Number.isInteger(signal)) {
      return -1;
    }
    if (signal < 0 || signal >= max) {
      return -1;
    }
    const word = signal >>> 5;
    const bit = 1 << (signal & SLOT_MASK);
    Atomics.or(atomicView, word, bit);
    return 1;
  };
  const abortAll = () => {
    for (let word = 0; word < size; word++) {
      Atomics.store(atomicView, word, inUse[word]);
    }
    return current;
  };
  const hasAborted = (signal) => {
    if (signal === closeNow) {
      return true;
    }
    if (!Number.isInteger(signal)) {
      return false;
    }
    if (signal < 0 || signal >= max) {
      return false;
    }
    const word = signal >>> 5;
    const bit = 1 << (signal & SLOT_MASK);
    return (Atomics.load(atomicView, word) & bit) !== 0;
  };
  const resetSignal = (signal) => {
    if (signal === closeNow) {
      return false;
    }
    if (!Number.isInteger(signal)) {
      return false;
    }
    if (signal < 0 || signal >= max) {
      return false;
    }
    const word = signal >>> 5;
    const bit = 1 << (signal & SLOT_MASK);
    const used = (inUse[word] & bit) !== 0;
    if (!used) {
      return false;
    }
    inUse[word] = (inUse[word] & ~bit) >>> 0;
    if (current > 0) {
      current = current - 1 | 0;
    }
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
    inUseCount: () => current,
  };
};

class OneShotDeferred {
  #triggered = false;
  constructor(deferred, onSettle) {
    const settleOnce = (fn) => (...args) => {
      if (this.#triggered) {
        return;
      }
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
    permission,
    totalNumberOfThread,
    list,
    ids,
    at,
  } = startupData;
  scrubWorkerDataSensitiveBuffers(startupData);
  installWritePermissionGuard(permission);
  installStrictModeRuntimeGuard(permission);
  assertWorkerSharedMemoryBootData({ sab, lock, returnLock });
  var Comment;
  ((Comment2) => {
    Comment2[Comment2["thisIsAHint"] = 0] = "thisIsAHint";
  })(Comment ||= {});
  const signals = createSharedMemoryTransport({
    sabObject: {
      sharedSab: sab,
    },
    isMain: false,
    thread,
    debug,
    startTime: startAt,
  });
  const lockState = lock2({
    headers: lock.headers,
    LockBoundSector: lock.lockSector,
    payload: lock.payload,
    payloadSector: lock.payloadSector,
  });
  const returnLockState = lock2({
    headers: returnLock.headers,
    LockBoundSector: returnLock.lockSector,
    payload: returnLock.payload,
    payloadSector: returnLock.payloadSector,
  });
  const timers = workerOptions?.timers;
  const spinMicroseconds = timers?.spinMicroseconds ??
    Math.max(1, totalNumberOfThread) * 50;
  const parkMs = timers?.parkMs ?? Math.max(1, totalNumberOfThread) * 50;
  const pauseSpin = (() => {
    const fn = typeof timers?.pauseNanoseconds === "number"
      ? whilePausing({ pauseInNanoseconds: timers.pauseNanoseconds })
      : pauseGeneric;
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
    permission,
  });
  assertWorkerImportsResolved({ debug, list, ids, listOfFunctions });
  const abortSignals = abortSignalSAB
    ? signalAbortFactory({
      sab: abortSignalSAB,
      maxSignals: abortSignalMax,
    })
    : undefined;
  const {
    enqueueLock,
    serviceBatchImmediate,
    hasCompleted,
    writeBatch,
    hasPending,
    getAwaiting,
  } = createWorkerRxQueue({
    listOfFunctions,
    workerOptions,
    lock: lockState,
    returnLock: returnLockState,
    hasAborted: abortSignals?.hasAborted,
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
    write: () => hasCompleted() ? writeBatch(WRITE_MAX) : 0,
  });
  const channel = new MessageChannel();
  const port1 = channel.port1;
  const port2 = channel.port2;
  const post2 = port2.postMessage.bind(port2);
  let isInMacro = false;
  let awaitingSpins = 0;
  let lastAwaiting = 0;
  const MAX_AWAITING_MS = 10;
  let wakeSeq = a_load2(opView, 0);
  const scheduleMacro = () => {
    if (isInMacro) {
      return;
    }
    isInMacro = true;
    post2(null);
  };
  const scheduleTimer = (delayMs) => {
    if (isInMacro) {
      return;
    }
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
        if (_writeBatch(WRITE_MAX) > 0) {
          progressed = true;
        }
      }
      if (_hasPending()) {
        if (_serviceBatchImmediate() > 0) {
          progressed = true;
        }
      }
      if ((awaiting = _getAwaiting()) > 0) {
        if (awaiting !== lastAwaiting) {
          awaitingSpins = 0;
        }
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
  if (typeof scopeCtor !== "function") {
    return false;
  }
  try {
    return globalThis instanceof scopeCtor;
  } catch {
    return false;
  }
};
var isLockBuffers = (value) => {
  if (!value || typeof value !== "object") {
    return false;
  }
  const candidate = value;
  return candidate.headers instanceof SharedArrayBuffer &&
    candidate.lockSector instanceof SharedArrayBuffer &&
    candidate.payload instanceof SharedArrayBuffer &&
    candidate.payloadSector instanceof SharedArrayBuffer;
};
var isWorkerBootPayload = (value) => {
  if (!value || typeof value !== "object") {
    return false;
  }
  const candidate = value;
  return candidate.sab instanceof SharedArrayBuffer &&
    Array.isArray(candidate.list) && Array.isArray(candidate.ids) &&
    Array.isArray(candidate.at) && typeof candidate.thread === "number" &&
    typeof candidate.totalNumberOfThread === "number" &&
    typeof candidate.startAt === "number" && isLockBuffers(candidate.lock) &&
    isLockBuffers(candidate.returnLock);
};
var installWebWorkerBootstrap = () => {
  const g = globalThis;
  const start = (data) => {
    if (!isWorkerBootPayload(data)) {
      return;
    }
    workerMainLoop(data);
  };
  if (
    typeof g.addEventListener === "function" &&
    typeof g.removeEventListener === "function"
  ) {
    const onMessage = (event) => {
      const data = event?.data;
      if (!isWorkerBootPayload(data)) {
        return;
      }
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
    if (!isWorkerBootPayload(data)) {
      return;
    }
    g.onmessage = null;
    start(data);
  };
};
if (isMainThread3 === false && isWorkerBootPayload(workerData)) {
  workerMainLoop(workerData);
} else if (isWebWorkerScope()) {
  installWebWorkerBootstrap();
}

// src/common/with-resolvers.ts
var withResolvers = () => {
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
  now,
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
  const queue = Array.from(
    { length: initialSize },
    (_, index) => newSlot(index),
  );
  const freeSockets = Array.from({ length: initialSize }, (_, i) => i);
  const toBeSent = new RingQueue();
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
    },
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
    for (let index = 0; index < queue.length; index++) {
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
    if (toBeSentCount === 0) {
      return false;
    }
    const encoded = encodeManyFrom(toBeSent) | 0;
    if (encoded === 0) {
      return false;
    }
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
      const USE_SIGNAL = abortSignal !== undefined &&
        abortSignals !== undefined;
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
          const encodedSignalMeta =
            (maybeSignal + ABORT_SIGNAL_META_OFFSET2 & FUNCTION_META_MASK) >>>
            0;
          slot[0 /* FunctionID */] =
            (encodedSignalMeta << FUNCTION_META_SHIFT | functionIDMasked) >>> 0;
        }
        slot.value = rawArgs;
        slot[1 /* ID */] = index;
        slot.resolve = deferred.resolve;
        slot.reject = deferred.reject;
        if (HAS_TIMER) {
          slot[6 /* slotBuffer */] =
            (slot[6 /* slotBuffer */] & SLOT_INDEX_MASK |
              (nowTime() >>> 0 & SLOT_META_MASK) << SLOT_META_SHIFT >>> 0) >>>
            0;
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
    settlePromisePayload: (task, result) => {
      if (task.reject === PLACE_HOLDER) {
        return false;
      }
      if (pendingPromises > 0) {
        pendingPromises = pendingPromises - 1 | 0;
      }
      if (result.status === "rejected") {
        try {
          task.reject(result.reason);
        } catch {}
        inUsed = inUsed - 1 | 0;
        freePush(task[1 /* ID */]);
        return false;
      }
      task.value = result.value;
      return enqueueKnown(task);
    },
  };
}

// src/runtime/dispatcher.ts
import { MessageChannel as MessageChannel2 } from "node:worker_threads";
var hostDispatcherLoop = ({
  signalBox: {
    opView,
    txStatus,
    rxStatus,
  },
  queue: {
    completeFrame,
    hasPendingFrames,
    flushToWorker,
    txIdle,
  },
  channelHandler,
  dispatcherOptions,
}) => {
  const a_load2 = Atomics.load;
  const a_store3 = Atomics.store;
  const a_notify = Atomics.notify;
  const notify = channelHandler.notify.bind(channelHandler);
  let stallCount = 0 | 0;
  const STALL_FREE_LOOPS = Math.max(
    0,
    (dispatcherOptions?.stallFreeLoops ?? 128) | 0,
  );
  const MAX_BACKOFF_MS = Math.max(
    0,
    (dispatcherOptions?.maxBackoffMs ?? 10) | 0,
  );
  let progressed = false;
  let anyProgressed = false;
  const check = () => {
    txStatus[0 /* thisIsAHint */] = 1;
    if (a_load2(rxStatus, 0) === 0) {
      a_store3(opView, 0, 1);
      a_notify(opView, 0, 1);
      do {
        progressed = false;
        if (completeFrame() > 0) {
          progressed = true;
          anyProgressed = true;
        }
        while (hasPendingFrames()) {
          if (!flushToWorker()) {
            break;
          }
          progressed = true;
          anyProgressed = true;
        }
      } while (progressed);
    }
    do {
      progressed = false;
      if (completeFrame() > 0) {
        anyProgressed = progressed = true;
      }
      while (hasPendingFrames()) {
        if (!flushToWorker()) {
          break;
        }
        anyProgressed = progressed = true;
      }
    } while (progressed);
    txStatus[0 /* thisIsAHint */] = 0;
    if (!txIdle()) {
      if (anyProgressed || hasPendingFrames()) {
        stallCount = 0 | 0;
      } else {
        stallCount = stallCount + 1 | 0;
      }
      scheduleNotify();
      return;
    }
    txStatus[0 /* thisIsAHint */] = 0;
    check.isRunning = false;
    stallCount = 0 | 0;
  };
  check.isRunning = false;
  const scheduleNotify = () => {
    if (stallCount <= STALL_FREE_LOOPS) {
      notify();
      return;
    }
    let delay = stallCount - STALL_FREE_LOOPS - 1 | 0;
    if (delay < 0) {
      delay = 0;
    } else if (delay > MAX_BACKOFF_MS) {
      delay = MAX_BACKOFF_MS;
    }
    setTimeout(check, delay);
  };
  const fastCheck = () => {
    txStatus[0 /* thisIsAHint */] = 0;
    completeFrame();
    flushToWorker();
    fastCheck.isRunning = false;
  };
  fastCheck.isRunning = false;
  return {
    check,
    fastCheck,
  };
};

class ChannelHandler {
  channel;
  port1;
  port2;
  #post2;
  constructor() {
    this.channel = new MessageChannel2();
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
var isNodeWorkerSafeExecFlag = (flag) => {
  const key = flag.split("=", 1)[0];
  return key === "--experimental-vm-modules" ||
    key === "--experimental-transform-types" || key === "--expose-gc" ||
    key === "--no-warnings" || key === "--permission" ||
    key === "--experimental-permission" || key === "--allow-fs-read" ||
    key === "--allow-fs-write" || key === "--allow-worker" ||
    key === "--allow-child-process" || key === "--allow-addons" ||
    key === "--allow-wasi";
};
var isNodePermissionExecFlag = (flag) => {
  const key = flag.split("=", 1)[0];
  return key === "--permission" || key === "--experimental-permission" ||
    key === "--allow-fs-read" || key === "--allow-fs-write" ||
    key === "--allow-worker" || key === "--allow-child-process" ||
    key === "--allow-addons" || key === "--allow-wasi";
};
var toWorkerSafeExecArgv = (flags) => {
  if (!flags || flags.length === 0) {
    return;
  }
  const filtered = flags.filter(isNodeWorkerSafeExecFlag);
  if (filtered.length === 0) {
    return;
  }
  const seen = new Set();
  const deduped = [];
  for (const flag of filtered) {
    if (seen.has(flag)) {
      continue;
    }
    seen.add(flag);
    deduped.push(flag);
  }
  return deduped;
};
var toWorkerCompatExecArgv = (flags) => {
  const safe = toWorkerSafeExecArgv(flags);
  if (!safe || safe.length === 0) {
    return;
  }
  const compat = safe.filter((flag) => !isNodePermissionExecFlag(flag));
  return compat.length > 0 ? compat : undefined;
};
var toDenoWorkerPermissions = (protocol) => {
  if (!protocol || protocol.enabled !== true || protocol.unsafe === true) {
    return;
  }
  return {
    env: "inherit",
    ffi: "inherit",
    import: "inherit",
    net: "inherit",
    read: protocol.read.length > 0 ? protocol.read : false,
    run: protocol.deno.allowRun === true ? "inherit" : false,
    sys: "inherit",
    write: protocol.write.length > 0 ? protocol.write : false,
  };
};
var isUnstableDenoWorkerOptionsError = (error) => {
  const message = String(error?.message ?? error);
  return message.includes("unstable-worker-options") ||
    message.includes("Worker.deno.permissions");
};
var toDenoWorkerScript = (source, fallback) => {
  if (source instanceof URL) {
    return source.href;
  }
  try {
    return new URL(source, fallback).href;
  } catch {
    return source;
  }
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
  payloadInitialBytes,
  payloadMaxBytes,
  abortSignalCapacity,
  usesAbortSignal,
}) => {
  const tsFileUrl = new URL(import.meta.url);
  if (debug?.logHref === true) {
    console.log(tsFileUrl);
    jsrIsGreatAndWorkWithoutBugs();
  }
  const defaultPayloadMaxBytes = 64 * 1024 * 1024;
  const sanitizeBytes = (value) => {
    if (!Number.isFinite(value)) {
      return;
    }
    const bytes = Math.floor(value);
    return bytes > 0 ? bytes : undefined;
  };
  const maxBytes = sanitizeBytes(payloadMaxBytes) ?? defaultPayloadMaxBytes;
  const requestedInitial = sanitizeBytes(payloadInitialBytes);
  const initialBytes = HAS_SAB_GROW
    ? Math.min(requestedInitial ?? 4 * 1024 * 1024, maxBytes)
    : maxBytes;
  const defaultAbortSignalCapacity = 258;
  const requestedAbortSignalCapacity = sanitizeBytes(abortSignalCapacity);
  const resolvedAbortSignalCapacity = requestedAbortSignalCapacity ??
    defaultAbortSignalCapacity;
  const lockBuffers = {
    lockSector: new SharedArrayBuffer(LOCK_SECTOR_BYTE_LENGTH),
    payloadSector: new SharedArrayBuffer(LOCK_SECTOR_BYTE_LENGTH),
    headers: new SharedArrayBuffer(HEADER_BYTE_LENGTH),
    payload: createSharedArrayBuffer(initialBytes, maxBytes),
  };
  const returnLockBuffers = {
    lockSector: new SharedArrayBuffer(LOCK_SECTOR_BYTE_LENGTH),
    payloadSector: new SharedArrayBuffer(LOCK_SECTOR_BYTE_LENGTH),
    headers: new SharedArrayBuffer(HEADER_BYTE_LENGTH),
    payload: createSharedArrayBuffer(initialBytes, maxBytes),
  };
  const lock = lock2({
    headers: lockBuffers.headers,
    LockBoundSector: lockBuffers.lockSector,
    payload: lockBuffers.payload,
    payloadSector: lockBuffers.payloadSector,
  });
  const returnLock = lock2({
    headers: returnLockBuffers.headers,
    LockBoundSector: returnLockBuffers.lockSector,
    payload: returnLockBuffers.payload,
    payloadSector: returnLockBuffers.payloadSector,
  });
  const abortSignalWords = Math.max(
    1,
    Math.ceil(resolvedAbortSignalCapacity / 32),
  );
  const abortSignalSAB = usesAbortSignal === true
    ? new SharedArrayBuffer(Uint32Array.BYTES_PER_ELEMENT * abortSignalWords)
    : undefined;
  const abortSignals = abortSignalSAB
    ? signalAbortFactory({
      sab: abortSignalSAB,
      maxSignals: resolvedAbortSignalCapacity,
    })
    : undefined;
  const signals = createSharedMemoryTransport({
    sabObject: sab,
    isMain: true,
    thread,
    debug,
  });
  const signalBox = mainSignal(signals);
  const queue = createHostTxQueue({
    lock,
    returnLock,
    abortSignals,
  });
  const {
    enqueue,
    rejectAll,
    txIdle,
  } = queue;
  const channelHandler = new ChannelHandler();
  const { check, fastCheck } = hostDispatcherLoop({
    signalBox,
    queue,
    channelHandler,
    dispatcherOptions: host,
  });
  channelHandler.open(check);
  let worker;
  const workerUrl = source ?? tsFileUrl;
  const workerDataPayload = {
    sab: signals.sab,
    abortSignalSAB,
    abortSignalMax: usesAbortSignal === true
      ? resolvedAbortSignalCapacity
      : undefined,
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
    permission,
  };
  const baseWorkerOptions = {
    type: "module",
    workerData: workerDataPayload,
  };
  const withExecArgv = workerExecArgv && workerExecArgv.length > 0
    ? { ...baseWorkerOptions, execArgv: workerExecArgv }
    : baseWorkerOptions;
  const webWorkerCtor = globalThis.Worker;
  const canUseDenoWebWorker = IS_DENO === true &&
    typeof webWorkerCtor === "function";
  if (canUseDenoWebWorker) {
    const scriptURL = toDenoWorkerScript(workerUrl, tsFileUrl);
    const denoPermissions = toDenoWorkerPermissions(permission);
    const baseDenoOptions = {
      type: "module",
    };
    const withPermissionOptions = denoPermissions
      ? {
        ...baseDenoOptions,
        deno: {
          permissions: denoPermissions,
        },
      }
      : baseDenoOptions;
    try {
      worker = new webWorkerCtor(scriptURL, withPermissionOptions);
    } catch (error) {
      if (!denoPermissions || !isUnstableDenoWorkerOptionsError(error)) {
        throw error;
      }
      worker = new webWorkerCtor(scriptURL, baseDenoOptions);
    }
    worker.postMessage?.(workerDataPayload);
  } else {
    try {
      worker = new poliWorker(workerUrl, withExecArgv);
    } catch (error) {
      if (error?.code === "ERR_WORKER_INVALID_EXEC_ARGV") {
        const fallbackExecArgv = toWorkerSafeExecArgv(withExecArgv.execArgv);
        if (fallbackExecArgv && fallbackExecArgv.length > 0) {
          try {
            worker = new poliWorker(workerUrl, {
              ...baseWorkerOptions,
              execArgv: fallbackExecArgv,
            });
          } catch (fallbackError) {
            if (fallbackError?.code === "ERR_WORKER_INVALID_EXEC_ARGV") {
              const compatExecArgv = toWorkerCompatExecArgv(fallbackExecArgv);
              if (compatExecArgv && compatExecArgv.length > 0) {
                try {
                  worker = new poliWorker(workerUrl, {
                    ...baseWorkerOptions,
                    execArgv: compatExecArgv,
                  });
                } catch {
                  worker = new poliWorker(workerUrl, baseWorkerOptions);
                }
              } else {
                worker = new poliWorker(workerUrl, baseWorkerOptions);
              }
            } else {
              throw fallbackError;
            }
          }
        } else {
          worker = new poliWorker(workerUrl, baseWorkerOptions);
        }
      } else {
        throw error;
      }
    }
  }
  const thisSignal = signalBox.opView;
  const a_add = Atomics.add;
  const a_load2 = Atomics.load;
  const a_notify = Atomics.notify;
  const scheduleFastCheck = queueMicrotask;
  const send = () => {
    if (check.isRunning === true) {
      return;
    }
    channelHandler.notify();
    check.isRunning = true;
    if (a_load2(signalBox.rxStatus, 0) === 0) {
      a_add(thisSignal, 0, 1);
      a_notify(thisSignal, 0, 1);
    }
  };
  lock.setPromiseHandler((task, result) => {
    queue.settlePromisePayload(task, result);
    send();
  });
  const call = ({ fnNumber, timeout, abortSignal }) => {
    const enqueues = enqueue(fnNumber, timeout, abortSignal);
    return (args) => {
      const pending = enqueues(args);
      if (fastCheck.isRunning === false) {
        signalBox.txStatus[0 /* thisIsAHint */] = 1;
        fastCheck.isRunning = true;
        scheduleFastCheck(fastCheck);
        send();
      }
      return pending;
    };
  };
  const context = {
    txIdle,
    call,
    kills: async () => {
      rejectAll("Thread closed");
      channelHandler.close();
      try {
        Promise.resolve(worker.terminate()).catch(() => {});
      } catch {}
    },
    lock,
  };
  return context;
};

// src/api.ts
import {
  isMainThread as isMainThread4,
  workerData as workerData2,
} from "node:worker_threads";
import { readFileSync as readFileSync2 } from "node:fs";
import path4 from "node:path";
import { fileURLToPath as fileURLToPath4 } from "node:url";

// src/permison/protocol.ts
import path3 from "node:path";
import { existsSync as existsSync2 } from "node:fs";
import { fileURLToPath as fileURLToPath3 } from "node:url";
var DEFAULT_ENV_FILE = ".env";
var DEFAULT_DENO_LOCK_FILE = "deno.lock";
var DEFAULT_BUN_LOCK_FILES = ["bun.lockb", "bun.lock"];
var DEFAULT_STRICT_MAX_EVAL_DEPTH = 16;
var MIN_STRICT_MAX_EVAL_DEPTH = 1;
var MAX_STRICT_MAX_EVAL_DEPTH = 64;
var NODE_MODULES_DIR = "node_modules";
var DEFAULT_DENY_RELATIVE = [
  ".env",
  ".git",
  ".npmrc",
  ".docker",
  ".secrets",
];
var clampStrictMaxEvalDepth = (value) => {
  if (!Number.isFinite(value)) {
    return DEFAULT_STRICT_MAX_EVAL_DEPTH;
  }
  const int = Math.floor(value);
  if (int < MIN_STRICT_MAX_EVAL_DEPTH) {
    return MIN_STRICT_MAX_EVAL_DEPTH;
  }
  if (int > MAX_STRICT_MAX_EVAL_DEPTH) {
    return MAX_STRICT_MAX_EVAL_DEPTH;
  }
  return int;
};
var resolveStrictPermissionSettings = (input) => ({
  recursiveScan: input?.recursiveScan !== false,
  maxEvalDepth: clampStrictMaxEvalDepth(input?.maxEvalDepth),
  sandbox: input?.sandbox === true,
});
var DEFAULT_DENY_HOME = [
  ".ssh",
  ".gnupg",
  ".aws",
  ".azure",
  ".config/gcloud",
  ".kube",
];
var DEFAULT_DENY_ABSOLUTE_POSIX = [
  "/proc",
  "/proc/self",
  "/proc/self/environ",
  "/proc/self/mem",
  "/sys",
  "/dev",
  "/etc",
];
var normalizeList = (values) => {
  const out = [];
  const seen = new Set();
  for (const value of values) {
    if (seen.has(value)) {
      continue;
    }
    seen.add(value);
    out.push(value);
  }
  return out;
};
var normalizeProtocolInput = (input) =>
  !input ? undefined : typeof input === "string" ? { mode: input } : input;
var isWindows = () => {
  if (typeof process !== "undefined") {
    return process.platform === "win32";
  }
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
    if (typeof g.Deno?.cwd === "function") {
      return g.Deno.cwd();
    }
  } catch {}
  return ".";
};
var getHome = () => {
  try {
    if (typeof process !== "undefined" && typeof process.env === "object") {
      const home = process.env.HOME ?? process.env.USERPROFILE;
      if (typeof home === "string" && home.length > 0) {
        return home;
      }
    }
  } catch {}
  const g = globalThis;
  try {
    const home = g.Deno?.env?.get?.("HOME") ??
      g.Deno?.env?.get?.("USERPROFILE");
    if (typeof home === "string" && home.length > 0) {
      return home;
    }
  } catch {}
  return;
};
var expandHomePath = (value, home) => {
  if (!home) {
    return value;
  }
  if (value === "~") {
    return home;
  }
  if (value.startsWith("~/") || value.startsWith("~\\")) {
    return path3.resolve(home, value.slice(2));
  }
  return value;
};
var toAbsolutePath2 = (value, cwd, home) => {
  if (value instanceof URL) {
    if (value.protocol !== "file:") {
      return;
    }
    return path3.resolve(fileURLToPath3(value));
  }
  const expanded = expandHomePath(value, home);
  if (path3.isAbsolute(expanded)) {
    return path3.resolve(expanded);
  }
  try {
    const parsed = new URL(expanded);
    if (parsed.protocol !== "file:") {
      return;
    }
    return path3.resolve(fileURLToPath3(parsed));
  } catch {
    return path3.resolve(cwd, expanded);
  }
};
var toPath = (value, cwd, home) =>
  value == null ? undefined : toAbsolutePath2(value, cwd, home);
var toPathList = (values, cwd, home) => {
  if (!values?.length) {
    return [];
  }
  const out = [];
  for (const value of values) {
    const resolved = toPath(value, cwd, home);
    if (resolved) {
      out.push(resolved);
    }
  }
  return out;
};
var toUniquePathList = (values, cwd, home) =>
  normalizeList(toPathList(values, cwd, home));
var toEnvFiles = (input, cwd, home) => {
  const values = Array.isArray(input)
    ? input
    : input
    ? [input]
    : [DEFAULT_ENV_FILE];
  return toUniquePathList(values, cwd, home);
};
var toNodeFlags = ({
  read,
  write,
  envFiles,
  node,
}) => {
  const flags = [
    "--permission",
    ...read.map((entry) => `--allow-fs-read=${entry}`),
    ...write.map((entry) => `--allow-fs-write=${entry}`),
    ...envFiles.map((file) => `--env-file-if-exists=${file}`),
  ];
  if (node.allowWorker) {
    flags.push("--allow-worker");
  }
  if (node.allowChildProcess) {
    flags.push("--allow-child-process");
  }
  if (node.allowAddons) {
    flags.push("--allow-addons");
  }
  if (node.allowWasi) {
    flags.push("--allow-wasi");
  }
  return flags;
};
var toDenoFlags = ({
  read,
  write,
  denyRead,
  denyWrite,
  envFiles,
  denoLock,
  frozen,
  allowRun,
}) => {
  const flags = [
    `--allow-read=${read.join(",")}`,
    `--allow-write=${write.join(",")}`,
    ...envFiles.map((file) => `--env-file=${file}`),
  ];
  if (denyRead.length > 0) {
    flags.push(`--deny-read=${denyRead.join(",")}`);
  }
  if (denyWrite.length > 0) {
    flags.push(`--deny-write=${denyWrite.join(",")}`);
  }
  if (denoLock) {
    flags.push(`--lock=${denoLock}`);
    if (frozen) {
      flags.push("--frozen=true");
    }
  }
  if (allowRun === false) {
    flags.push("--deny-run");
  }
  return flags;
};
var toBunFlags = ({
  envFiles,
  allowRun,
}) => {
  const flags = envFiles.map((file) => `--env-file=${file}`);
  if (allowRun === false) {
    flags.push("--deny-run");
  }
  return flags;
};
var isPathWithin2 = (base, candidate) => {
  const relative = path3.relative(base, candidate);
  return relative === "" ||
    !relative.startsWith("..") && !path3.isAbsolute(relative);
};
var defaultSensitiveDenyPaths = (cwd, home) => {
  const projectSensitive = DEFAULT_DENY_RELATIVE.map((entry) =>
    path3.resolve(cwd, entry)
  );
  const homeSensitive = home
    ? DEFAULT_DENY_HOME.map((entry) => path3.resolve(home, entry))
    : [];
  const osSensitive = isWindows()
    ? []
    : DEFAULT_DENY_ABSOLUTE_POSIX.map((entry) => path3.resolve(entry));
  return normalizeList([...projectSensitive, ...homeSensitive, ...osSensitive]);
};
var collectWritePaths = (cwd, values) => {
  const out = normalizeList(values.length > 0 ? values : [cwd]);
  if (
    !out.some((entry) => isPathWithin2(entry, cwd) || isPathWithin2(cwd, entry))
  ) {
    out.unshift(cwd);
  }
  return normalizeList(out);
};
var collectReadPaths = ({
  cwd,
  read,
  moduleFiles,
  envFiles,
  denoLock,
  bunLock,
}) => {
  const out = [
    cwd,
    path3.resolve(cwd, NODE_MODULES_DIR),
    ...read,
    ...moduleFiles,
    ...envFiles,
  ];
  if (denoLock) {
    out.push(denoLock);
  }
  if (bunLock) {
    out.push(bunLock);
  }
  return normalizeList(out);
};
var resolveBunLock = (input, cwd, home) => {
  if (input === false) {
    return;
  }
  if (input && input !== true) {
    return toPath(input, cwd, home);
  }
  const g = globalThis;
  for (const fileName of DEFAULT_BUN_LOCK_FILES) {
    const candidate = path3.resolve(cwd, fileName);
    try {
      if (typeof g.Deno?.statSync === "function") {
        g.Deno.statSync(candidate);
        return candidate;
      }
    } catch {}
    try {
      if (typeof g.Bun?.file === "function") {
        const file = g.Bun.file(candidate);
        if (typeof file.exists === "function" && file.exists()) {
          return candidate;
        }
      }
    } catch {}
    try {
      if (existsSync2(candidate)) {
        return candidate;
      }
    } catch {}
  }
  return path3.resolve(cwd, DEFAULT_BUN_LOCK_FILES[0]);
};
var resolvePermisonProtocol = ({
  permission,
  permison,
  modules,
}) => {
  const input = normalizeProtocolInput(permission ?? permison);
  if (!input) {
    return;
  }
  const rawMode = input.mode;
  const mode = rawMode === "unsafe" || rawMode === "off" ? "unsafe" : "strict";
  const unsafe = mode === "unsafe";
  const allowConsole = input.console ?? unsafe;
  const strictSettings = resolveStrictPermissionSettings(input.strict);
  const cwd = path3.resolve(input.cwd ?? getCwd());
  const home = getHome();
  const nodeModulesPath = path3.resolve(cwd, NODE_MODULES_DIR);
  if (unsafe) {
    return {
      enabled: true,
      mode,
      unsafe: true,
      allowConsole,
      cwd,
      read: [],
      write: [],
      denyRead: [],
      denyWrite: [],
      envFiles: [],
      lockFiles: {},
      strict: strictSettings,
      node: {
        allowWorker: true,
        allowChildProcess: true,
        allowAddons: true,
        allowWasi: true,
        flags: [],
      },
      deno: {
        frozen: false,
        allowRun: true,
        flags: [],
      },
      bun: {
        allowRun: true,
        flags: [],
      },
    };
  }
  const read = toPathList(input.read, cwd, home);
  const write = toPathList(input.write, cwd, home);
  const sensitiveDefaultPaths = defaultSensitiveDenyPaths(cwd, home);
  const denyRead = normalizeList([
    ...toPathList(input.denyRead, cwd, home),
    ...sensitiveDefaultPaths,
  ]);
  const denyWrite = normalizeList([
    ...toPathList(input.denyWrite, cwd, home),
    ...sensitiveDefaultPaths,
    nodeModulesPath,
  ]);
  const isDeniedRead = (candidate) =>
    denyRead.some((deny) => isPathWithin2(deny, candidate));
  const envFiles = toEnvFiles(input.env?.files, cwd, home).filter((entry) =>
    !isDeniedRead(entry)
  );
  const denoLock = input.deno?.lock === false
    ? undefined
    : input.deno?.lock === true || input.deno?.lock === undefined
    ? path3.resolve(cwd, DEFAULT_DENO_LOCK_FILE)
    : toPath(input.deno.lock, cwd, home);
  const bunLock = resolveBunLock(input.bun?.lock, cwd, home);
  const moduleFiles = toUniquePathList(modules, cwd, home);
  const nodeSettings = {
    allowWorker: input.node?.allowWorker === true,
    allowChildProcess: input.node?.allowChildProcess === true,
    allowAddons: input.node?.allowAddons === true,
    allowWasi: input.node?.allowWasi === true,
  };
  const denoSettings = {
    frozen: input.deno?.frozen !== false,
    allowRun: input.deno?.allowRun === true,
  };
  const bunSettings = {
    allowRun: input.bun?.allowRun === true,
  };
  const resolvedRead = collectReadPaths({
    cwd,
    read,
    moduleFiles,
    envFiles,
    denoLock,
    bunLock,
  });
  const resolvedWrite = collectWritePaths(cwd, write);
  return {
    enabled: true,
    mode,
    unsafe: false,
    allowConsole,
    cwd,
    read: resolvedRead,
    write: resolvedWrite,
    denyRead,
    denyWrite,
    envFiles,
    lockFiles: {
      deno: denoLock,
      bun: bunLock,
    },
    strict: strictSettings,
    node: {
      ...nodeSettings,
      flags: toNodeFlags({
        read: resolvedRead,
        write: resolvedWrite,
        envFiles,
        node: nodeSettings,
      }),
    },
    deno: {
      ...denoSettings,
      flags: toDenoFlags({
        read: resolvedRead,
        write: resolvedWrite,
        denyRead,
        denyWrite,
        envFiles,
        denoLock,
        frozen: denoSettings.frozen,
        allowRun: denoSettings.allowRun,
      }),
    },
    bun: {
      ...bunSettings,
      flags: toBunFlags({
        envFiles,
        allowRun: bunSettings.allowRun,
      }),
    },
  };
};
var toRuntimePermissionFlags = (protocol) =>
  protocol?.enabled === true && protocol.unsafe !== true && RUNTIME === "node"
    ? protocol.node.flags
    : [];
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
  inlinerGate,
}) => {
  const strategy = typeof balancer === "object" && balancer != null
    ? balancer.strategy
    : balancer;
  if (contexts.length < 2) {
    throw new Error(
      contexts.length === 0
        ? "No threads available."
        : "Cannot rotate with a single thread.",
    );
  }
  if (handlers.length === 0) {
    throw new Error("No handlers provided.");
  }
  const allInvoker = selectStrategy(contexts, handlers, strategy);
  if (!inlinerGate) {
    return allInvoker;
  }
  const inlinerIndex = inlinerGate.index | 0;
  const threshold = Number.isFinite(inlinerGate.threshold)
    ? Math.max(1, Math.floor(inlinerGate.threshold))
    : 1;
  if (threshold <= 1 || inlinerIndex < 0 || inlinerIndex >= handlers.length) {
    return allInvoker;
  }
  const workerLaneCount = handlers.length - 1;
  if (workerLaneCount <= 0) {
    return allInvoker;
  }
  const workerHandlers = new Array(workerLaneCount);
  const workerContexts = new Array(workerLaneCount);
  for (let source = 0, lane = 0; source < handlers.length; source += 1) {
    if (source === inlinerIndex) {
      continue;
    }
    workerHandlers[lane] = handlers[source];
    workerContexts[lane] = contexts[source];
    lane += 1;
  }
  const workerOnlyInvoker = selectStrategy(
    workerContexts,
    workerHandlers,
    strategy,
  );
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
        if (rrCursor === top) {
          rrCursor = 0;
        }
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
        for (let lane = 0; lane < laneCount; lane += 1) {
          if (isSolved[lane]()) {
            return handlers[lane](args);
          }
        }
        const fallback = rrCursor;
        rrCursor += 1;
        if (rrCursor === laneCount) {
          rrCursor = 0;
        }
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
        for (let lane = 0; lane < laneCount; lane += 1) {
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
  if (timeout == null) {
    return;
  }
  if (typeof timeout === "number") {
    return timeout >= 0
      ? { ms: timeout, kind: 0, /* Reject */ value: new Error("Task timeout") }
      : undefined;
  }
  const ms = timeout.time;
  if (!(ms >= 0)) {
    return;
  }
  if ("default" in timeout) {
    return { ms, kind: 1, /* Resolve */ value: timeout.default };
  }
  if (timeout.maybe === true) {
    return { ms, kind: 1, /* Resolve */ value: undefined };
  }
  if ("error" in timeout) {
    return { ms, kind: 0, /* Reject */ value: timeout.error };
  }
  return { ms, kind: 0, /* Reject */ value: new Error("Task timeout") };
};
var raceTimeout2 = (promise, spec) =>
  new Promise((resolve, reject) => {
    let done = false;
    const timer = setTimeout(() => {
      if (done) {
        return;
      }
      done = true;
      if (spec.kind === 1 /* Resolve */) {
        resolve(spec.value);
      } else {
        reject(spec.value);
      }
    }, spec.ms);
    promise.then((value) => {
      if (done) {
        return;
      }
      done = true;
      clearTimeout(timer);
      resolve(value);
    }, (err) => {
      if (done) {
        return;
      }
      done = true;
      clearTimeout(timer);
      reject(err);
    });
  });
var INLINE_ABORT_TOOLKIT = (() => {
  const hasAborted = () => false;
  return {
    hasAborted,
  };
})();
var composeInlineCallable = (fn, timeout, useAbortToolkit = false) => {
  const normalized = normalizeTimeout2(timeout);
  const run = useAbortToolkit ? (args) => fn(args, INLINE_ABORT_TOOLKIT) : fn;
  if (!normalized) {
    return run;
  }
  return (args) => {
    const result = run(args);
    return result instanceof Promise
      ? raceTimeout2(result, normalized)
      : result;
  };
};
var createInlineExecutor = ({
  tasks,
  genTaskID: genTaskID2,
  batchSize,
}) => {
  const entries = Object.values(tasks).sort((a, b) => a.id - b.id);
  const runners = entries.map((entry) =>
    composeInlineCallable(
      entry.f,
      entry.timeout,
      entry.abortSignal !== undefined,
    )
  );
  const initCap = 16;
  let fnByIndex = new Int32Array(initCap);
  let stateByIndex = new Int8Array(initCap).fill(-1 /* Free */);
  let argsByIndex = new Array(initCap);
  let taskIdByIndex = new Array(initCap).fill(-1);
  let deferredByIndex = new Array(initCap);
  const freeStack = new Array(initCap);
  let freeTop = initCap;
  for (let i = 0; i < initCap; i++) {
    freeStack[i] = initCap - 1 - i;
  }
  const pendingQueue = new RingQueue(initCap);
  let working = 0;
  let isInMacro = false;
  let isInMicro = false;
  const batchLimit = Number.isFinite(batchSize)
    ? Math.max(1, Math.floor(batchSize ?? 1))
    : Number.POSITIVE_INFINITY;
  const channel = new MessageChannel3();
  const port1 = channel.port1;
  const port2 = channel.port2;
  const post2 = port2.postMessage.bind(port2);
  const hasPending = () => pendingQueue.isEmpty === false;
  const queueMicro = typeof queueMicrotask === "function"
    ? queueMicrotask
    : (callback) => Promise.resolve().then(callback);
  const scheduleMacro = () => {
    if (working === 0 || isInMacro) {
      return;
    }
    isInMacro = true;
    post2(null);
  };
  const send = () => {
    if (working === 0 || isInMacro || isInMicro) {
      return;
    }
    isInMicro = true;
    queueMicro(runMicroLoop);
  };
  const enqueue = (index) => {
    pendingQueue.push(index);
    send();
  };
  const enqueueIfCurrent = (index, taskID) => {
    if (
      stateByIndex[index] !== 0 /* Pending */ || taskIdByIndex[index] !== taskID
    ) {
      return;
    }
    enqueue(index);
  };
  const settleIfCurrent = (index, taskID, isError, value) => {
    if (
      stateByIndex[index] !== 0 /* Pending */ || taskIdByIndex[index] !== taskID
    ) {
      return;
    }
    const deferred = deferredByIndex[index];
    if (deferred) {
      if (isError) {
        deferred.reject(value);
      } else {
        deferred.resolve(value);
      }
    }
    cleanup(index);
  };
  function allocIndex() {
    if (freeTop > 0) {
      return freeStack[--freeTop];
    }
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
    for (let i = newCap - 1; i >= oldCap; --i) {
      freeStack[freeTop++] = i;
    }
    return freeStack[--freeTop];
  }
  function processLoop(fromMicro = false) {
    let processed = 0;
    while (processed < batchLimit) {
      const maybeIndex = pendingQueue.shiftNoClear();
      if (maybeIndex === undefined) {
        break;
      }
      const index = maybeIndex | 0;
      if (stateByIndex[index] !== 0 /* Pending */) {
        continue;
      }
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
        res.then(
          (value) => settleIfCurrent(index, taskID, false, value),
          (err) => settleIfCurrent(index, taskID, true, err),
        );
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
    if (!isInMicro) {
      return;
    }
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
    if (working === 0) {
      isInMacro = false;
    }
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
        if (taskIdByIndex[index] !== taskID) {
          return;
        }
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
      for (let index = 0; index < stateByIndex.length; index++) {
        if (stateByIndex[index] !== 0 /* Pending */) {
          continue;
        }
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
    txIdle: () => working === 0,
  };
};

// src/api.ts
var MAX_FUNCTION_ID = 65535;
var MAX_FUNCTION_COUNT = MAX_FUNCTION_ID + 1;
var resolveLocalModulePath = (value) => {
  try {
    const parsed = new URL(value);
    if (parsed.protocol !== "file:") {
      return;
    }
    return path4.resolve(fileURLToPath4(parsed));
  } catch {
    if (!path4.isAbsolute(value)) {
      return;
    }
    return path4.resolve(value);
  }
};
var assertBunStrictModuleSafety = ({
  protocol,
  modules,
}) => {
  if (!protocol || protocol.unsafe === true || RUNTIME !== "bun") {
    return;
  }
  const strictScanOptions = protocol.strict;
  for (const moduleRef of modules) {
    const modulePath = resolveLocalModulePath(moduleRef);
    if (!modulePath) {
      continue;
    }
    let source;
    try {
      source = readFileSync2(modulePath, "utf8");
    } catch {
      continue;
    }
    const result = scanCode(source, {
      depth: 0,
      origin: "preflight",
      source: modulePath,
    }, strictScanOptions);
    if (result.passed !== true) {
      throw new StrictModeViolationError({
        origin: "preflight",
        depth: 0,
        source: modulePath,
        violations: result.violations,
        scannedCode: source,
      });
    }
  }
};
var isMain = isMainThread4;
var toListAndIds = (args) => {
  const result = Object.values(args).reduce(
    (
      acc,
      v,
    ) => (acc[0].add(v.importedFrom), acc[1].add(v.id), acc[2].add(v.at), acc),
    [
      new Set(),
      new Set(),
      new Set(),
    ],
  );
  return {
    list: [...result[0]],
    ids: [...result[1]],
    at: [...result[2]],
  };
};
var createPool = ({
  threads,
  debug,
  inliner,
  balancer,
  payloadInitialBytes,
  payloadMaxBytes,
  abortSignalCapacity,
  source,
  worker,
  workerExecArgv,
  permission,
  permison,
  dispatcher,
  host,
}) =>
(tasks) => {
  if (isMainThread4 === false) {
    if (debug?.extras === true) {
      console.warn(
        "createPool has been called with : " + JSON.stringify(workerData2),
      );
    }
    const notMainThreadError = () => {
      throw new Error("createPool can only be called in the main thread.");
    };
    const throwingProxyTarget = function () {
      return notMainThreadError();
    };
    const throwingProxyHandler = {
      get: function () {
        return notMainThreadError;
      },
    };
    const mainThreadOnlyProxy = new Proxy(
      throwingProxyTarget,
      throwingProxyHandler,
    );
    return {
      shutdown: mainThreadOnlyProxy,
      call: mainThreadOnlyProxy,
    };
  }
  const { list, ids, at } = toListAndIds(tasks),
    listOfFunctions = Object.entries(tasks).map(([k, v]) => ({
      ...v,
      name: k,
    })).sort((a, b) => a.name.localeCompare(b.name));
  if (listOfFunctions.length > MAX_FUNCTION_COUNT) {
    throw new RangeError(
      `Too many tasks: received ${listOfFunctions.length}. ` +
        `Maximum is ${MAX_FUNCTION_COUNT} (Uint16 function IDs: 0..${MAX_FUNCTION_ID}).`,
    );
  }
  const usingInliner = typeof inliner === "object" && inliner != null;
  const totalNumberOfThread = (threads ?? 1) + (usingInliner ? 1 : 0);
  const permissionProtocol = resolvePermisonProtocol({
    permission,
    permison,
    modules: list,
  });
  assertBunStrictModuleSafety({
    protocol: permissionProtocol,
    modules: list,
  });
  const permissionExecArgv = toRuntimePermissionFlags(permissionProtocol);
  const allowedFlags =
    typeof process !== "undefined" && process.allowedNodeEnvironmentFlags
      ? process.allowedNodeEnvironmentFlags
      : null;
  const isNodePermissionFlag = (flag) => {
    const key = flag.split("=", 1)[0];
    return key === "--permission" || key === "--experimental-permission" ||
      key === "--allow-fs-read" || key === "--allow-fs-write" ||
      key === "--allow-worker" || key === "--allow-child-process" ||
      key === "--allow-addons" || key === "--allow-wasi";
  };
  const stripNodePermissionFlags = (flags) =>
    flags?.filter((flag) => !isNodePermissionFlag(flag));
  const dedupeFlags = (flags) => {
    const out = [];
    const seen = new Set();
    for (const flag of flags) {
      if (seen.has(flag)) {
        continue;
      }
      seen.add(flag);
      out.push(flag);
    }
    return out;
  };
  const sanitizeExecArgv = (flags) => {
    if (!flags || flags.length === 0) {
      return;
    }
    if (!allowedFlags) {
      return flags;
    }
    const filtered = flags.filter((flag) => {
      const key = flag.split("=", 1)[0];
      return allowedFlags.has(key);
    });
    return filtered.length > 0 ? filtered : undefined;
  };
  const defaultExecArgvCandidate = workerExecArgv ??
    (typeof process !== "undefined" && Array.isArray(process.execArgv)
      ? allowedFlags?.has("--expose-gc") === true
        ? process.execArgv.includes("--expose-gc")
          ? process.execArgv
          : [...process.execArgv, "--expose-gc"]
        : process.execArgv
      : undefined);
  const defaultExecArgv = permissionProtocol?.unsafe === true
    ? stripNodePermissionFlags(defaultExecArgvCandidate)
    : defaultExecArgvCandidate;
  const needsVmModuleFlag = RUNTIME === "node" &&
    permissionProtocol?.enabled === true &&
    permissionProtocol.unsafe !== true &&
    permissionProtocol.mode === "strict" &&
    permissionProtocol.strict.sandbox === true;
  const combinedExecArgv = dedupeFlags([
    ...needsVmModuleFlag ? ["--experimental-vm-modules"] : [],
    ...permissionExecArgv,
    ...defaultExecArgv ?? [],
  ]);
  const execArgv = sanitizeExecArgv(
    combinedExecArgv.length > 0 ? combinedExecArgv : undefined,
  );
  const hostDispatcher = host ?? dispatcher;
  const usesAbortSignal = listOfFunctions.some((fn) =>
    fn.abortSignal !== undefined
  );
  let workers = Array.from({
    length: threads ?? 1,
  }).map((_, thread) =>
    spawnWorkerContext({
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
      payloadInitialBytes,
      payloadMaxBytes,
      abortSignalCapacity,
      usesAbortSignal,
      permission: permissionProtocol,
    })
  );
  if (usingInliner) {
    const mainThread = createInlineExecutor({
      tasks,
      genTaskID,
      batchSize: inliner?.batchSize ?? 1,
    });
    if (inliner?.position === "first") {
      workers = [
        mainThread,
        ...workers,
      ];
    } else {
      workers.push(mainThread);
    }
  }
  const inlinerIndex = usingInliner
    ? inliner?.position === "first" ? 0 : workers.length - 1
    : -1;
  const inlinerDispatchThreshold = Number.isFinite(inliner?.dispatchThreshold)
    ? Math.max(1, Math.floor(inliner?.dispatchThreshold ?? 1))
    : 1;
  const indexedFunctions = listOfFunctions.map((fn, index) => ({
    name: fn.name,
    index,
    timeout: fn.timeout,
    abortSignal: fn.abortSignal,
  }));
  const callHandlers = new Map();
  for (const { name } of indexedFunctions) {
    callHandlers.set(name, []);
  }
  for (const worker2 of workers) {
    for (const { name, index, timeout, abortSignal } of indexedFunctions) {
      callHandlers.get(name).push(worker2.call({
        fnNumber: index,
        timeout,
        abortSignal,
      }));
    }
  }
  const useDirectHandler = (threads ?? 1) === 1 && !usingInliner;
  const buildInvoker = (handlers) =>
    useDirectHandler ? handlers[0] : managerMethod({
      contexts: workers,
      balancer,
      handlers,
      inlinerGate: usingInliner
        ? {
          index: inlinerIndex,
          threshold: inlinerDispatchThreshold,
        }
        : undefined,
    });
  const callEntries = Array.from(
    callHandlers.entries(),
    ([name, handlers]) => [name, buildInvoker(handlers)],
  );
  return {
    shutdown: async () => {
      await Promise.allSettled(workers.map((worker2) => worker2.kills()));
    },
    call: Object.fromEntries(callEntries),
  };
};
var SINGLE_TASK_KEY = "__task__";
var createSingleTaskPool = (single, options) => {
  const pool = createPool(options ?? {})({
    [SINGLE_TASK_KEY]: single,
  });
  return {
    call: pool.call[SINGLE_TASK_KEY],
    shutdown: pool.shutdown,
  };
};
function task(I) {
  const [href, at] = getCallerFilePath();
  const importedFrom = I?.href != null
    ? toModuleUrl(I.href)
    : new URL(href).href;
  const out = {
    ...I,
    id: genTaskID(),
    importedFrom,
    at,
    [endpointSymbol]: true,
  };
  out.createPool = (options) => {
    if (isMainThread4 === false) {
      return out;
    }
    return createSingleTaskPool(out, options);
  };
  return out;
}
export { createPool, isMain, task, workerMainLoop };
