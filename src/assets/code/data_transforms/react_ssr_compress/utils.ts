import { brotliCompressSync } from "node:zlib";
import { renderUserCardHost } from "../react_ssr/render_user_card.tsx";
import { buildUserPayloads } from "../react_ssr/utils.ts";

export type CompressionResult = {
  ms: number;
  bytes: number;
};

export function buildCompressionPayloads(count: number): string[] {
  return buildUserPayloads(count);
}

export function compressHtml(html: string) {
  return brotliCompressSync(html);
}

export function sumCompressedBytes(
  chunks: ArrayLike<{ byteLength: number }>,
): number {
  let total = 0;
  for (let i = 0; i < chunks.length; i++) {
    total += chunks[i]!.byteLength;
  }
  return total;
}

export function runHostCompression(payloads: string[]): CompressionResult {
  const started = performance.now();
  let compressedBytes = 0;

  for (let i = 0; i < payloads.length; i++) {
    const html = renderUserCardHost(payloads[i]!);
    compressedBytes += compressHtml(html).byteLength;
  }

  return { ms: performance.now() - started, bytes: compressedBytes };
}

export function printCompressionMetrics(
  mode: string,
  requests: number,
  ms: number,
  compressedBytes: number,
): void {
  const secs = Math.max(1e-9, ms / 1000);
  const rps = requests / secs;
  console.log(`${mode} took       : ${ms.toFixed(2)} ms`);
  console.log(`${mode} throughput : ${rps.toFixed(0)} req/s`);
  console.log(`${mode} compressed : ${compressedBytes.toLocaleString()}`);
}
