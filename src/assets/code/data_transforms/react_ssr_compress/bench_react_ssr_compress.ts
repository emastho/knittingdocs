import { createPool, isMain } from "@vixeny/knitting";
import { bench, boxplot, run, summary } from "mitata";
import { renderUserCardHost } from "../react_ssr/render_user_card.tsx";
import { renderUserCardCompressed } from "./render_user_card_compressed.tsx";
import {
  buildCompressionPayloads,
  compressHtml,
  sumCompressedBytes,
} from "./utils.ts";

const THREADS = 2;
const REQUESTS = 2_000;


async function main() {
  const payloads = buildCompressionPayloads(REQUESTS);
  const pool = createPool({ threads: THREADS })({ renderUserCardCompressed });
  let sink = 0;

  try {
    const hostBytes = runHost(payloads);
    const knittingBytes = await runWorkers(
      pool.call.renderUserCardCompressed,
      payloads,
    );
    if (hostBytes !== knittingBytes) {
      throw new Error("Host and worker compressed byte totals differ.");
    }

    console.log("React SSR + compression benchmark (mitata)");
    console.log("workload: parse + normalize + render + brotli");
    console.log("requests per iteration:", REQUESTS.toLocaleString());
    console.log("threads:", THREADS);

    boxplot(() => {
      summary(() => {
        bench(`host (${REQUESTS.toLocaleString()} req)`, () => {
          sink = runHost(payloads);
        });

        bench(
          `knitting (${THREADS} thread(s), ${REQUESTS.toLocaleString()} req)`,
          async () => {
            sink = await runWorkers(pool.call.renderUserCardCompressed, payloads);
          },
        );
      });
    });

    await run();
    console.log("last compressed bytes:", sink.toLocaleString());
  } finally {
    pool.shutdown();
  }
}


function runHost(payloads: string[]): number {
  let compressedBytes = 0;
  for (let i = 0; i < payloads.length; i++) {
    const html = renderUserCardHost(payloads[i]!);
    compressedBytes += compressHtml(html).byteLength;
  }
  return compressedBytes;
}

async function runWorkers(
  callRender: (payload: string) => Promise<{ byteLength: number }>,
  payloads: string[],
): Promise<number> {
  const jobs: Promise<{ byteLength: number }>[] = [];
  for (let i = 0; i < payloads.length; i++) {
    jobs.push(callRender(payloads[i]!));
  }

  const results = await Promise.all(jobs);
  return sumCompressedBytes(results);
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
