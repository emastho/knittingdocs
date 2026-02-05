import { task } from "@vixeny/knitting";
import { brotliCompressSync } from "node:zlib";
import { renderUserCardHost } from "../react_ssr/render_user_card.tsx";

function compressHtml(html: string) {
  return brotliCompressSync(html);
}

export const renderUserCardCompressed = task({
  f: (payload: string) => {
    const card = renderUserCardHost(payload);
    const compressed = compressHtml(card.html);
    return compressed;
  },
});
