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
  const SLOT_MASK = 31;
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
      task[6 /* slotBuffer */] = slotIndex;
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
      task[6 /* slotBuffer */] = slotIndex;
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
      task[6 /* slotBuffer */] = slotIndex;
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
      task[6 /* slotBuffer */] = slotIndex;
      tableLength = tl + 1;
      usedBits |= freeBit;
      hostLast ^= freeBit;
      return a_store(hostBits, 0, hostLast);
    }
    return -1;
  };
  const setSlotLength = (slotIndex, payloadLen) => {
    if ((slotIndex | 0) < 0 || slotIndex >= 32 /* slots */) {
      return false;
    }
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
import { deserialize, serialize } from "node:v8";
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
import { isMainThread } from "worker_threads";
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
        ? "KNT_ERROR_3: Value is not serializable by v8 serializer"
        : `KNT_ERROR_3: Value is not serializable by v8 serializer; ${detail}`;
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
  const reserveDynamic = (task, bytes) => {
    task[5 /* PayloadLen */] = bytes;
    if (allocTask(task) === -1) {
      return false;
    }
    return true;
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
        let objectDynamicSlot = -1;
        const reserveDynamicObject = (bytes) => {
          task[5 /* PayloadLen */] = bytes;
          if (allocTask(task) === -1) {
            return false;
          }
          objectDynamicSlot = task[6 /* slotBuffer */];
          return true;
        };
        try {
          switch (args.constructor) {
            case NodeBuffer2: {
              const bytes = args.byteLength;
              if (bytes <= staticMaxBytes) {
                const written = writeStaticBinary(args, slotIndex);
                if (written !== -1) {
                  task[2 /* Type */] = 39 /* StaticBuffer */;
                  task[5 /* PayloadLen */] = written;
                  task.value = null;
                  return true;
                }
              }
              task[2 /* Type */] = 38 /* Buffer */;
              if (!reserveDynamicObject(bytes)) {
                return false;
              }
              writeDynamicBinary(args, task[3 /* Start */]);
              task.value = null;
              return true;
            }
            case Uint8Array: {
              const bytes = args.byteLength;
              if (bytes <= staticMaxBytes) {
                const written = writeStaticBinary(args, slotIndex);
                if (written !== -1) {
                  task[2 /* Type */] = 18 /* StaticBinary */;
                  task[5 /* PayloadLen */] = written;
                  task.value = null;
                  return true;
                }
              }
              task[2 /* Type */] = 17 /* Binary */;
              if (!reserveDynamicObject(bytes)) {
                return false;
              }
              writeDynamicBinary(args, task[3 /* Start */]);
              task.value = null;
              return true;
            }
            case ArrayBuffer: {
              const view = new Uint8Array(args);
              const bytes = view.byteLength;
              if (bytes <= staticMaxBytes) {
                const written = writeStaticBinary(view, slotIndex);
                if (written !== -1) {
                  task[2 /* Type */] = 37 /* StaticArrayBuffer */;
                  task[5 /* PayloadLen */] = written;
                  task.value = null;
                  return true;
                }
              }
              task[2 /* Type */] = 36 /* ArrayBuffer */;
              if (!reserveDynamicObject(bytes)) {
                return false;
              }
              writeDynamicBinary(view, task[3 /* Start */]);
              task.value = null;
              return true;
            }
            case Object:
            case Array: {
              let text;
              try {
                text = stringifyJSON(args);
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
              if (!reserveDynamicObject(text.length * 3)) {
                return false;
              }
              const written = writeDynamicUtf8(text, task[3 /* Start */]);
              task[5 /* PayloadLen */] = written;
              setSlotLength(task[6 /* slotBuffer */], written);
              task.value = null;
              return true;
            }
            case NumericBuffer: {
              const float64 = args.toFloat64();
              task[2 /* Type */] = 14 /* NumericBuffer */;
              if (!reserveDynamicObject(float64.byteLength)) {
                return false;
              }
              writeDynamic8Binary(float64, task[3 /* Start */]);
              task.value = null;
              return true;
            }
            case Int32Array: {
              const view = args;
              const bytes = view.byteLength;
              if (bytes <= staticMaxBytes) {
                const written = writeStaticBinary(
                  new Uint8Array(view.buffer, view.byteOffset, view.byteLength),
                  slotIndex,
                );
                if (written !== -1) {
                  task[2 /* Type */] = 31 /* StaticInt32Array */;
                  task[5 /* PayloadLen */] = written;
                  task.value = null;
                  return true;
                }
              }
              task[2 /* Type */] = 19 /* Int32Array */;
              if (!reserveDynamicObject(bytes)) {
                return false;
              }
              writeDynamicBinary(
                new Uint8Array(view.buffer, view.byteOffset, view.byteLength),
                task[3 /* Start */],
              );
              task.value = null;
              return true;
            }
            case Float64Array: {
              const view = args;
              const bytes = view.byteLength;
              if (bytes <= staticMaxBytes) {
                const written = writeStatic8Binary(view, slotIndex);
                if (written !== -1) {
                  task[2 /* Type */] = 32 /* StaticFloat64Array */;
                  task[5 /* PayloadLen */] = written;
                  task.value = null;
                  return true;
                }
              }
              task[2 /* Type */] = 20 /* Float64Array */;
              if (!reserveDynamicObject(bytes)) {
                return false;
              }
              writeDynamic8Binary(view, task[3 /* Start */]);
              task.value = null;
              return true;
            }
            case BigInt64Array: {
              const view = args;
              const bytes = view.byteLength;
              if (bytes <= staticMaxBytes) {
                const written = writeStaticBinary(
                  new Uint8Array(view.buffer, view.byteOffset, view.byteLength),
                  slotIndex,
                );
                if (written !== -1) {
                  task[2 /* Type */] = 33 /* StaticBigInt64Array */;
                  task[5 /* PayloadLen */] = written;
                  task.value = null;
                  return true;
                }
              }
              task[2 /* Type */] = 21 /* BigInt64Array */;
              if (!reserveDynamicObject(bytes)) {
                return false;
              }
              writeDynamicBinary(
                new Uint8Array(view.buffer, view.byteOffset, view.byteLength),
                task[3 /* Start */],
              );
              task.value = null;
              return true;
            }
            case BigUint64Array: {
              const view = args;
              const bytes = view.byteLength;
              if (bytes <= staticMaxBytes) {
                const written = writeStaticBinary(
                  new Uint8Array(view.buffer, view.byteOffset, view.byteLength),
                  slotIndex,
                );
                if (written !== -1) {
                  task[2 /* Type */] = 34 /* StaticBigUint64Array */;
                  task[5 /* PayloadLen */] = written;
                  task.value = null;
                  return true;
                }
              }
              task[2 /* Type */] = 22 /* BigUint64Array */;
              if (!reserveDynamicObject(bytes)) {
                return false;
              }
              writeDynamicBinary(
                new Uint8Array(view.buffer, view.byteOffset, view.byteLength),
                task[3 /* Start */],
              );
              task.value = null;
              return true;
            }
            case DataView: {
              const view = args;
              const bytes = view.byteLength;
              if (bytes <= staticMaxBytes) {
                const written = writeStaticBinary(
                  new Uint8Array(view.buffer, view.byteOffset, view.byteLength),
                  slotIndex,
                );
                if (written !== -1) {
                  task[2 /* Type */] = 35 /* StaticDataView */;
                  task[5 /* PayloadLen */] = written;
                  task.value = null;
                  return true;
                }
              }
              task[2 /* Type */] = 23 /* DataView */;
              if (!reserveDynamicObject(bytes)) {
                return false;
              }
              writeDynamicBinary(
                new Uint8Array(view.buffer, view.byteOffset, view.byteLength),
                task[3 /* Start */],
              );
              task.value = null;
              return true;
            }
            case Date: {
              const time = args.getTime();
              Float64View[0] = time;
              task[2 /* Type */] = 25 /* Date */;
              task[3 /* Start */] = Uint32View[0];
              task[4 /* End */] = Uint32View[1];
              task.value = null;
              return true;
            }
            case Promise: {
              const markedTask = task;
              if (markedTask[PromisePayloadMarker] !== true) {
                markedTask[PromisePayloadMarker] = true;
                args.then((value) => {
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
          }
          {
            let binary;
            try {
              binary = serialize(args);
            } catch (error) {
              const detail = error instanceof Error
                ? error.message
                : String(error);
              return encoderError({
                task,
                type: 3, /* Serializable */
                onPromise,
                detail,
              });
            }
            if (binary.byteLength <= staticMaxBytes) {
              const written = writeStaticBinary(binary, slotIndex);
              if (written !== -1) {
                task[2 /* Type */] = 30 /* StaticSerializable */;
                task[5 /* PayloadLen */] = written;
                task.value = null;
                return true;
              }
            }
            task[2 /* Type */] = 13 /* Serializable */;
            if (!reserveDynamicObject(binary.byteLength)) {
              return false;
            }
            writeDynamicBinary(binary, task[3 /* Start */]);
            task.value = null;
            return true;
          }
        } catch (error) {
          if (objectDynamicSlot !== -1) {
            free(objectDynamicSlot);
          }
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
        setSlotLength(task[6 /* slotBuffer */], written);
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
        setSlotLength(task[6 /* slotBuffer */], written);
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
  const {
    readUtf8: readDynamicUtf8,
    readBytesCopy: readDynamicBytesCopy,
    readBytesView: readDynamicBytesView,
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
    readBytesView: readStaticBytesView,
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
        free(task[6 /* slotBuffer */]);
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
        free(task[6 /* slotBuffer */]);
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
        free(task[6 /* slotBuffer */]);
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
        free(task[6 /* slotBuffer */]);
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
        free(task[6 /* slotBuffer */]);
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
        free(task[6 /* slotBuffer */]);
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
        free(task[6 /* slotBuffer */]);
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
        free(task[6 /* slotBuffer */]);
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
        free(task[6 /* slotBuffer */]);
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
        free(task[6 /* slotBuffer */]);
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
        free(task[6 /* slotBuffer */]);
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
        free(task[6 /* slotBuffer */]);
        return;
      case 39 /* StaticBuffer */:
        task.value = readStaticBufferCopy(
          0,
          task[5 /* PayloadLen */],
          slotIndex,
        );
        return;
      case 13 /* Serializable */:
        task.value = deserialize(
          readDynamicBytesView(
            task[3 /* Start */],
            task[3 /* Start */] + task[5 /* PayloadLen */],
          ),
        );
        free(task[6 /* slotBuffer */]);
        return;
      case 30 /* StaticSerializable */:
        task.value = deserialize(
          readStaticBytesView(0, task[5 /* PayloadLen */], slotIndex),
        );
        return;
      case 14 /* NumericBuffer */:
        task.value = NumericBuffer.fromFloat64(
          readDynamic8BytesFloatView(
            task[3 /* Start */],
            task[3 /* Start */] + task[5 /* PayloadLen */],
          ),
        );
        free(task[6 /* slotBuffer */]);
        return;
    }
  };
};

// src/memory/lock.ts
var PromisePayloadMarker = Symbol.for("knitting.promise.payload");
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

// src/worker/rx-queue.ts
var createWorkerRxQueue = ({
  listOfFunctions,
  workerOptions,
  lock,
  returnLock,
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
  const IDX_FLAGS = 0 /* FlagsToHost */;
  const IDX_FN = 0 /* FunctionID */;
  const FLAG_REJECT = 1 /* Reject */;
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
          const result = jobs[slot[IDX_FN]](slot.value);
          slot[IDX_FLAGS] = 0;
          if (result instanceof Promise) {
            awaiting++;
            try {
              result.then(
                (value) => settleNow(slot, false, value, true),
                (err) => settleNow(slot, true, err, true),
              );
            } catch (err) {
              settleNow(slot, true, err, true);
            }
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

// src/worker/get-functions.ts
var normalizeTimeout = (timeout) => {
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
var raceTimeout = (promise, spec) =>
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
var isThenable = (value) => {
  if (value == null) {
    return false;
  }
  const type = typeof value;
  if (type !== "object" && type !== "function") {
    return false;
  }
  return typeof value.then === "function";
};
var composeWorkerCallable = (fixed) => {
  const fn = fixed.f;
  const timeout = normalizeTimeout(fixed.timeout);
  if (!timeout) {
    return fn;
  }
  return (args) => {
    const result = fn(args);
    return isThenable(result) ? raceTimeout(result, timeout) : result;
  };
};
var getFunctions = async ({ list, ids, at }) => {
  const modules = list.map((specifier) => toModuleUrl(specifier));
  const results = await Promise.all(modules.map(async (imports) => {
    const module = await import(imports);
    return Object.entries(module).filter(([_, value]) =>
      value != null && typeof value === "object" &&
      value?.[endpointSymbol] === true
    ).map(([name, value]) => ({
      ...value,
      name,
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
    run: composeWorkerCallable(fixed),
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
var p_now = performance.now.bind(performance);
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
    const until = p_now() + spinMicroseconds / 1000;
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
      if ((spinChecks++ & 63) === 0 && p_now() >= until) {
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

// src/worker/loop.ts
var jsrIsGreatAndWorkWithoutBugs = () => null;
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
var workerMainLoop = async (workerData2) => {
  installTerminationGuard();
  installUnhandledRejectionSilencer();
  const {
    debug,
    sab,
    thread,
    startAt,
    workerOptions,
    lock,
    returnLock,
  } = workerData2;
  if (!sab) {
    throw new Error("worker missing transport SAB");
  }
  if (
    !lock?.headers || !lock?.lockSector || !lock?.payload ||
    !lock?.payloadSector
  ) {
    throw new Error("worker missing lock SABs");
  }
  if (
    !returnLock?.headers || !returnLock?.lockSector || !returnLock?.payload ||
    !returnLock?.payloadSector
  ) {
    throw new Error("worker missing return lock SABs");
  }
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
    Math.max(1, workerData2.totalNumberOfThread) * 50;
  const parkMs = timers?.parkMs ??
    Math.max(1, workerData2.totalNumberOfThread) * 50;
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
    list: workerData2.list,
    isWorker: true,
    ids: workerData2.ids,
    at: workerData2.at,
  });
  if (debug?.logImportedUrl === true) {
    console.log(workerData2.list);
  }
  if (listOfFunctions.length === 0) {
    console.log(workerData2.list);
    console.log(workerData2.ids);
    console.log(listOfFunctions);
    throw "No imports were found.";
  }
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
  });
  a_store3(rxStatus, 0, 1);
  const BATCH_MAX = 32;
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
if (isMainThread3 === false) {
  workerMainLoop(workerData);
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
function createHostTxQueue({
  max,
  lock,
  returnLock,
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
  const queue = Array.from({ length: max ?? 10 }, (_, index) => newSlot(index));
  const freeSockets = Array.from({ length: max ?? 10 }, (_, i) => i);
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
    enqueue: (functionID) => (rawArgs) => {
      if (inUsed === queue.length) {
        const newSize = inUsed + 10;
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
      slot.value = rawArgs;
      slot[0 /* FunctionID */] = functionID;
      slot[1 /* ID */] = index;
      slot.resolve = deferred.resolve;
      slot.reject = deferred.reject;
      if (!encode(slot)) {
        handleEncodeFailure(slot);
      }
      inUsed = inUsed + 1 | 0;
      return deferred.promise;
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
  host,
  payloadInitialBytes,
  payloadMaxBytes,
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
  };
  const baseWorkerOptions = {
    type: "module",
    workerData: workerDataPayload,
  };
  const withExecArgv = workerExecArgv && workerExecArgv.length > 0
    ? { ...baseWorkerOptions, execArgv: workerExecArgv }
    : baseWorkerOptions;
  try {
    worker = new poliWorker(workerUrl, withExecArgv);
  } catch (error) {
    if (error?.code === "ERR_WORKER_INVALID_EXEC_ARGV") {
      worker = new poliWorker(workerUrl, baseWorkerOptions);
    } else {
      throw error;
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
  const call = ({ fnNumber }) => {
    const enqueues = enqueue(fnNumber);
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
var composeInlineCallable = (fn, timeout) => {
  const normalized = normalizeTimeout2(timeout);
  if (!normalized) {
    return fn;
  }
  return (args) => {
    const result = fn(args);
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
    composeInlineCallable(entry.f, entry.timeout)
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
  source,
  worker,
  workerExecArgv,
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
  const usingInliner = typeof inliner === "object" && inliner != null;
  const totalNumberOfThread = (threads ?? 1) + (usingInliner ? 1 : 0);
  const allowedFlags =
    typeof process !== "undefined" && process.allowedNodeEnvironmentFlags
      ? process.allowedNodeEnvironmentFlags
      : null;
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
  const defaultExecArgv = workerExecArgv ??
    (typeof process !== "undefined" && Array.isArray(process.execArgv)
      ? allowedFlags?.has("--expose-gc") === true
        ? process.execArgv.includes("--expose-gc")
          ? process.execArgv
          : [...process.execArgv, "--expose-gc"]
        : process.execArgv
      : undefined);
  const execArgv = sanitizeExecArgv(defaultExecArgv);
  const isDispatcherOptions = (value) =>
    typeof value === "object" && value !== null && ("host" in value);
  const hostDispatcher = host ??
    (isDispatcherOptions(dispatcher) ? dispatcher.host : dispatcher);
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
  }));
  const callHandlers = new Map();
  for (const { name } of indexedFunctions) {
    callHandlers.set(name, []);
  }
  for (const worker2 of workers) {
    for (const { name, index } of indexedFunctions) {
      callHandlers.get(name).push(worker2.call({
        fnNumber: index,
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
var task = (I) => {
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
};
export { createPool, isMain, task, workerMainLoop };
