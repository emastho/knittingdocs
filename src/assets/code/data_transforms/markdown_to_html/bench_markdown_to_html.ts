import { createPool, isMain } from "@vixeny/knitting";
import { bench, boxplot, run, summary } from "mitata";
import {
  markdownToHtmlCompressed,
  markdownToHtmlCompressedHost,
} from "./render_markdown.ts";
import { buildMarkdownDocs, sumChunkBytes } from "./utils.ts";

const THREADS = 2;
const DOCS = 2_000;

function runHost(markdowns: string[]): number {
  let compressedBytes = 0;
  for (let i = 0; i < markdowns.length; i++) {
    compressedBytes += markdownToHtmlCompressedHost(markdowns[i]!).byteLength;
  }
  return compressedBytes;
}

async function runWorkers(
  callRender: (markdown: string) => Promise<Uint8Array>,
  markdowns: string[],
): Promise<number> {
  const jobs: Promise<Uint8Array>[] = [];
  for (let i = 0; i < markdowns.length; i++) {
    jobs.push(callRender(markdowns[i]!));
  }

  const chunks = await Promise.all(jobs);
  return sumChunkBytes(chunks);
}

async function main() {
  const markdowns = buildMarkdownDocs(DOCS);
  const pool = createPool({ threads: THREADS })({ markdownToHtmlCompressed });
  let sink = 0;

  try {
    const hostBytes = runHost(markdowns);
    const knittingBytes = await runWorkers(
      pool.call.markdownToHtmlCompressed,
      markdowns,
    );
    if (hostBytes !== knittingBytes) {
      throw new Error("Host and worker compressed byte totals differ.");
    }

    console.log("Markdown -> HTML benchmark (mitata)");
    console.log("workload: parse + render + brotli");
    console.log("docs per iteration:", DOCS.toLocaleString());
    console.log("threads:", THREADS);

    boxplot(() => {
      summary(() => {
        bench(`host (${DOCS.toLocaleString()} docs)`, () => {
          sink = runHost(markdowns);
        });

        bench(
          `knitting (${THREADS} thread(s), ${DOCS.toLocaleString()} docs)`,
          async () => {
            sink = await runWorkers(pool.call.markdownToHtmlCompressed, markdowns);
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

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
