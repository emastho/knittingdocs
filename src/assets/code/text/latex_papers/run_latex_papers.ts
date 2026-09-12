import { createPool, isMain } from "knitting";
import { ensureCorpus, indexArchive } from "./arxiv_corpus.ts";
import type { PaperRecord } from "./tex_parse.ts";

const THREADS = 4;

async function main() {
  // First run downloads the sources from arXiv; later runs read the cache.
  const paths = await ensureCorpus();
  using pool = createPool({ threads: THREADS })({ indexArchive });

  const started = performance.now();
  const records = await Promise.all(paths.map(pool.call.indexArchive));
  const elapsedMs = performance.now() - started;

  const total = (pick: (record: PaperRecord) => number) =>
    records.reduce((sum, record) => sum + pick(record), 0);
  const citationKeys = new Set(records.flatMap((record) => record.citationKeys));

  console.log(
    `\nIndexed ${records.length} arXiv submissions on ${THREADS} workers ` +
      `in ${elapsedMs.toFixed(0)} ms\n`,
  );
  console.log("  id           words   sec   eq  fig  tab  cites  title");
  for (const record of [...records].sort((a, b) => b.words - a.words)) {
    console.log(
      `  ${record.id.padEnd(11)}` +
        `${record.words.toLocaleString().padStart(6)}` +
        `${String(record.sections.length).padStart(6)}` +
        `${String(record.equations).padStart(5)}` +
        `${String(record.figures).padStart(5)}` +
        `${String(record.tables).padStart(5)}` +
        `${String(record.citationKeys.length).padStart(7)}  ` +
        (record.pdfOnly ? "(PDF-only submission)" : record.title.slice(0, 44)),
    );
  }

  console.log("\n  LaTeX in       :", total((r) => r.texBytes).toLocaleString(), "bytes");
  console.log("  prose out      :", total((r) => r.textBytes).toLocaleString(), "bytes");
  console.log("  words          :", total((r) => r.words).toLocaleString());
  console.log("  macros expanded:", total((r) => r.macrosExpanded).toLocaleString());
  console.log(
    "  citations      :",
    `${total((r) => r.citationKeys.length).toLocaleString()} ` +
      `(${citationKeys.size.toLocaleString()} unique keys)`,
  );
  console.log("  PDF-only       :", records.filter((r) => r.pdfOnly).length, "with no body to index");
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
