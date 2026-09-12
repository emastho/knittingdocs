import { task } from "knitting";
import { brotliCompressSync } from "node:zlib";
import { renderUserCardHost } from "../react_ssr/render_user_card.tsx";

export const compressHtml = (html: string): Uint8Array =>
  brotliCompressSync(html);

/**
 * Render the card to HTML and Brotli-compress it. Exported so the benchmark can
 * run exactly the same work on the host instead of keeping a second copy of it.
 */
export function renderAndCompressHost(payloadJson: string): Uint8Array {
  return compressHtml(renderUserCardHost(payloadJson));
}

export const renderUserCardCompressed = task({
  f: renderAndCompressHost,
});
