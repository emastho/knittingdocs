import { createPool, isMain } from "knitting";
import { bench, boxplot, run, summary } from "mitata";
import { batched, buildInvoices } from "./invoice_fixtures.ts";
import {
  type Invoice,
  renderInvoiceBatch,
  renderInvoiceBatchHost,
  unpackDocuments,
} from "./render_invoice.ts";

const INVOICES = 200;
const THREADS = 4;

// Batch so there are several batches per worker: enough to amortize dispatch,
// not so few that one slow batch holds up the round.
const BATCH = 12;

async function main() {
  const invoices = buildInvoices(INVOICES);
  const batches = batched(invoices, BATCH);
  using pool = createPool({ threads: THREADS })({ renderInvoiceBatch });
  const callBatch = pool.call.renderInvoiceBatch;

  const hostDocs = await runHost(batches);
  const workerDocs = await runWorkers(callBatch, batches);
  const hostBytes = totalBytes(hostDocs);
  const workerBytes = totalBytes(workerDocs);
  const parity = hostDocs.length === workerDocs.length &&
    hostBytes === workerBytes;
  console.log(
    `pdf parity check: ${hostDocs.length} documents, ` +
      `host=${hostBytes.toLocaleString()} bytes ` +
      `worker=${workerBytes.toLocaleString()} bytes ` +
      (parity ? "OK match" : "MISMATCH"),
  );
  if (!parity) throw new Error("Host and worker PDF output differ.");

  console.log("\nPDF invoice rendering benchmark (mitata)");
  console.log("workload: lay out an A4 invoice and serialize the PDF");
  console.log("invoices per iteration:", INVOICES.toLocaleString());
  console.log(
    "average document:",
    `${(hostBytes / hostDocs.length / 1024).toFixed(1)} KB`,
  );
  console.log("threads:", THREADS, "| batch:", BATCH, "\n");

  let sink = 0;
  boxplot(() => {
    summary(() => {
      bench(`host (${INVOICES} invoices)`, async () => {
        sink = totalBytes(await runHost(batches));
      });

      bench(`knitting (${THREADS} threads, ${INVOICES} invoices)`, async () => {
        sink = totalBytes(await runWorkers(callBatch, batches));
      });
    });
  });

  await run();
  console.log("last total bytes:", sink.toLocaleString());
}

function totalBytes(documents: Uint8Array[]): number {
  let total = 0;
  for (let i = 0; i < documents.length; i++) total += documents[i]!.byteLength;
  return total;
}

async function runHost(batches: Invoice[][]): Promise<Uint8Array[]> {
  const documents: Uint8Array[] = [];
  for (const batch of batches) {
    documents.push(...unpackDocuments(await renderInvoiceBatchHost(batch)));
  }
  return documents;
}

async function runWorkers(
  callBatch: (invoices: Invoice[]) => Promise<Uint8Array>,
  batches: Invoice[][],
): Promise<Uint8Array[]> {
  const packed = await Promise.all(batches.map(callBatch));
  return packed.flatMap(unpackDocuments);
}

if (isMain) {
  main().catch((error) => {
    console.error(error);
    process.exitCode = 1;
  });
}
