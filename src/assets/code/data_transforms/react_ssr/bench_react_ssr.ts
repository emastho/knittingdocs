import { createPool, isMain } from "@vixeny/knitting";
import { bench, boxplot, run, summary } from "mitata";
import { renderUserCard, renderUserCardHost } from "./render_user_card.tsx";
import { buildUserPayloads } from "./utils.ts";

const THREADS = 1;
const REQUESTS = 2_000;

async function main() {
  const payloads = buildUserPayloads(REQUESTS);
  const pool = createPool({
    threads: THREADS,
    inliner: {
      batchSize: 6,
    },
  })({ renderUserCard });
  let sink = 0;

  try {
    const hostBytes = runHost(payloads);
    const knittingBytes = await runWorkers(pool.call.renderUserCard, payloads);
    if (hostBytes !== knittingBytes) {
      throw new Error("Host and worker HTML byte totals differ.");
    }

    console.log("React SSR benchmark (mitata)");
    console.log("workload: parse + normalize + render to HTML");
    console.log("requests per iteration:", REQUESTS.toLocaleString());
    console.log("threads:", THREADS, " + inliner");

    boxplot(() => {
      summary(() => {
        bench(`host (${REQUESTS.toLocaleString()} req)`, () => {
          sink = runHost(payloads);
        });

        bench(
          `knitting (${THREADS} thread(s) + main , ${REQUESTS.toLocaleString()} req)`,
          async () => {
            sink = await runWorkers(pool.call.renderUserCard, payloads);
          },
        );
      });
    });

    await run();
    console.log("last html bytes:", sink.toLocaleString());
  } finally {
    pool.shutdown();
  }
}

function runHost(payloads: string[]): number {
  let htmlBytes = 0;
  for (let i = 0; i < payloads.length; i++) {
    const html = renderUserCardHost(payloads[i]!);
    htmlBytes += html.length;
  }
  return htmlBytes;
}

async function runWorkers(
  callRender: (payload: string) => Promise<string>,
  payloads: string[],
): Promise<number> {
  const jobs: Promise<string>[] = [];
  for (let i = 0; i < payloads.length; i++) {
    jobs.push(callRender(payloads[i]!));
  }

  const results = await Promise.all(jobs);
  let htmlBytes = 0;
  for (let i = 0; i < results.length; i++) {
    htmlBytes += results[i]!.length;
  }
  return htmlBytes;
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
