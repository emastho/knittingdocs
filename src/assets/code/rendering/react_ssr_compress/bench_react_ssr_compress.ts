import { createPool, isMain } from "knitting";
import { bench, boxplot, run, summary } from "mitata";
import { renderUserCard } from "../react_ssr/render_user_card.tsx";
import { buildUserPayloads } from "../react_ssr/utils.ts";
import {
  compressHtml,
  renderAndCompressHost,
  renderUserCardCompressed,
} from "./render_user_card_compressed.tsx";

// Brotli is expensive enough that the host lane is worth having here: unlike the
// plain SSR example, the inliner earns its place on this workload.
const THREADS = 4;
const REQUESTS = 100;

async function main() {
  const payloads = buildUserPayloads(REQUESTS);
  using pool = createPool({
    threads: THREADS,
    inliner: { batchSize: 8 },
  })({ renderUserCardCompressed, renderUserCard });
  let sink = 0;

  const onWorker = pool.call.renderUserCardCompressed;
  const renderOnly = pool.call.renderUserCard;

  const hostBytes = runHost(payloads);
  const workerBytes = await runWorkerCompress(onWorker, payloads);
  const splitBytes = await runHostCompress(renderOnly, payloads);
  const parity = hostBytes === workerBytes && hostBytes === splitBytes;
  console.log(
    `byte parity check: host=${hostBytes.toLocaleString()} ` +
      `worker=${workerBytes.toLocaleString()} ` +
      `split=${splitBytes.toLocaleString()} ` +
      (parity ? "OK match" : "MISMATCH"),
  );
  if (!parity) throw new Error("Compressed byte totals differ.");

  console.log("\nReact SSR + compression benchmark (mitata)");
  console.log("workload: parse + normalize + render + brotli");
  console.log("requests per iteration:", REQUESTS.toLocaleString());
  console.log("threads:", THREADS, "+ inliner\n");

  boxplot(() => {
    summary(() => {
      bench("host: render + compress", () => {
        sink = runHost(payloads);
      });

      bench("worker: render only, host compresses", async () => {
        sink = await runHostCompress(renderOnly, payloads);
      });

      bench("worker: render + compress", async () => {
        sink = await runWorkerCompress(onWorker, payloads);
      });
    });
  });

  await run();
  console.log("last compressed bytes:", sink.toLocaleString());
}

function runHost(payloads: string[]): number {
  let compressedBytes = 0;
  for (let i = 0; i < payloads.length; i++) {
    compressedBytes += renderAndCompressHost(payloads[i]!).byteLength;
  }
  return compressedBytes;
}

// Both steps on the worker: only the compressed bytes cross the boundary.
async function runWorkerCompress(
  callCompressed: (payload: string) => Promise<Uint8Array>,
  payloads: string[],
): Promise<number> {
  const jobs = payloads.map(callCompressed);
  const results = await Promise.all(jobs);

  let total = 0;
  for (let i = 0; i < results.length; i++) total += results[i]!.byteLength;
  return total;
}

// Render on the worker, compress on the host: the full HTML crosses back, and
// every brotli call lands on the thread you were trying to keep free.
async function runHostCompress(
  callRender: (payload: string) => Promise<string>,
  payloads: string[],
): Promise<number> {
  const jobs = payloads.map(callRender);
  const results = await Promise.all(jobs);

  let total = 0;
  for (let i = 0; i < results.length; i++) {
    total += compressHtml(results[i]!).byteLength;
  }
  return total;
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
