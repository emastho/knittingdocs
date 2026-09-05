import { createPool, isMain } from "knitting";
import { bench, boxplot, run, summary } from "mitata";
import { ensureCorpus, indexArchive, loadArchive } from "./arxiv_corpus.ts";
import { parsePaper, parsePaperHost } from "./tex_parse.ts";

const THREADS = 4;

async function main() {
  const paths = await ensureCorpus();
  using pool = createPool({ threads: THREADS })({ indexArchive, parsePaper });

  const onHost = () => hostJob(paths);
  const splitJob = () => hostUnpacksWorkerParses(pool.call.parsePaper, paths);
  const workerJob = () => workerDoesBoth(pool.call.indexArchive, paths);

  const hostWords = await onHost();
  const splitWords = await splitJob();
  const workerWords = await workerJob();
  const parity = hostWords === splitWords && hostWords === workerWords;
  console.log(
    `word parity check: host=${hostWords.toLocaleString()} ` +
      `split=${splitWords.toLocaleString()} ` +
      `worker=${workerWords.toLocaleString()} ` +
      (parity ? "OK match" : "MISMATCH"),
  );
  if (!parity) throw new Error("Word counts differ between placements.");

  console.log("\nLaTeX corpus benchmark (mitata)");
  console.log("workload: gunzip + untar + inline inputs + expand macros + extract prose");
  console.log("papers per iteration:", paths.length);
  console.log("threads:", THREADS, "\n");

  let sink = 0;
  boxplot(() => {
    summary(() => {
      bench("host: unpack + parse", async () => {
        sink = await onHost();
      });

      bench("worker: parse only, host unpacks", async () => {
        sink = await splitJob();
      });

      bench("worker: unpack + parse", async () => {
        sink = await workerJob();
      });
    });
  });

  await run();
  console.log("last word count:", sink.toLocaleString());
}

/** Everything on the main thread. */
async function hostJob(paths: string[]): Promise<number> {
  let words = 0;
  for (const path of paths) {
    words += parsePaperHost(await loadArchive(path)).words;
  }
  return words;
}

/**
 * Split down the middle: the host gunzips and untars, the worker parses.
 *
 * This is the tempting shape -- offload the part that looks expensive -- and it
 * leaves the decompression on the thread you were trying to free.
 */
async function hostUnpacksWorkerParses(
  call: (source: Awaited<ReturnType<typeof loadArchive>>) => Promise<{ words: number }>,
  paths: string[],
): Promise<number> {
  const sources = await Promise.all(paths.map(loadArchive));
  const records = await Promise.all(sources.map(call));
  return records.reduce((total, record) => total + record.words, 0);
}

/** The whole job on the worker: only a path crosses the boundary. */
async function workerDoesBoth(
  call: (path: string) => Promise<{ words: number }>,
  paths: string[],
): Promise<number> {
  const records = await Promise.all(paths.map(call));
  return records.reduce((total, record) => total + record.words, 0);
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
