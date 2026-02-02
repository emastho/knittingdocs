---
title: Supported payloads
description: Data types you can send through knitting.
sidebar:
  order: 18
---

The transport supports the following payloads:

- `number` (including `NaN`, `Infinity`, and `-Infinity`)
- `string`
- `boolean`
- `bigint`
- `undefined` and `null`
- plain `Object` and `Array` (JSON serialized)
- `Map` and `Set` (v8 serialize)
- `Uint8Array`, `Int32Array`, `Float64Array`, `BigInt64Array`, `BigUint64Array`
- `DataView`
- `Error` (name, message, stack)
- `Date`
- `symbol` from `Symbol.for(...)` only
- `Promise<supported>` (resolved on the host before dispatch)

If you need multiple values, pass a tuple or object as the single argument.
Functions are not supported as payloads.

```ts
type JSONValue =
  | string
  | number
  | boolean
  | null
  | JSONArray
  | JSONObject;

interface JSONObject {
  [key: string]: JSONValue;
}

interface JSONArray extends Array<JSONValue> {}

type Serializable = string | object | number | boolean | bigint;

type ValidInput =
  | bigint
  | void
  | JSONValue
  | Map<Serializable, Serializable>
  | Set<Serializable>
  | symbol
  | Uint8Array
  | Int32Array
  | Float64Array
  | BigInt64Array
  | BigUint64Array
  | DataView
  | Error
  | Date;

type Args = ValidInput | Serializable;

type MaybePromise<T> = T | Promise<T>;

type TaskInput = Args | PromiseLike<Args>;
```
