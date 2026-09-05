import { task } from "knitting";
import { PDFDocument, rgb, StandardFonts } from "pdf-lib";

export type InvoiceLine = {
  description: string;
  quantity: number;
  unitCents: number;
};

export type Invoice = {
  number: string;
  customer: string;
  issuedAt: string;
  lines: InvoiceLine[];
};

const PAGE = { width: 595.28, height: 841.89 } as const; // A4, in points
const MARGIN = 48;
const ROW_HEIGHT = 18;
const EPOCH = new Date("2026-01-01T00:00:00Z");

const money = (cents: number) =>
  (cents / 100).toLocaleString("en-US", { minimumFractionDigits: 2 });

/**
 * Build a one-or-more page A4 invoice and return the PDF bytes. This is the
 * whole workload: laying out rows, embedding fonts, and deflating the result.
 */
export async function renderInvoiceHost(invoice: Invoice): Promise<Uint8Array> {
  const doc = await PDFDocument.create();
  // pdf-lib stamps the current time into every document. Pin it, or the same
  // invoice produces different bytes on every run and parity checks are useless.
  doc.setCreationDate(EPOCH);
  doc.setModificationDate(EPOCH);
  doc.setProducer("knitting-example");

  const font = await doc.embedFont(StandardFonts.Helvetica);
  const bold = await doc.embedFont(StandardFonts.HelveticaBold);

  let page = doc.addPage([PAGE.width, PAGE.height]);
  let y = PAGE.height - MARGIN - 14;

  page.drawText("INVOICE", { x: MARGIN, y, size: 22, font: bold });
  y -= 26;
  page.drawText(`${invoice.number}   ${invoice.customer}`, {
    x: MARGIN,
    y,
    size: 10,
    font,
  });
  page.drawText(invoice.issuedAt, {
    x: PAGE.width - MARGIN - 60,
    y,
    size: 10,
    font,
  });
  y -= 28;

  let totalCents = 0;
  for (const line of invoice.lines) {
    // Overflow onto a new page rather than drawing off the bottom edge.
    if (y < MARGIN + ROW_HEIGHT * 2) {
      page = doc.addPage([PAGE.width, PAGE.height]);
      y = PAGE.height - MARGIN - 14;
    }

    const cents = line.quantity * line.unitCents;
    totalCents += cents;

    page.drawText(line.description, { x: MARGIN, y, size: 10, font });
    page.drawText(String(line.quantity), { x: 400, y, size: 10, font });
    page.drawText(money(cents), { x: 470, y, size: 10, font });
    page.drawLine({
      start: { x: MARGIN, y: y - 4 },
      end: { x: PAGE.width - MARGIN, y: y - 4 },
      thickness: 0.3,
      color: rgb(0.82, 0.82, 0.82),
    });
    y -= ROW_HEIGHT;
  }

  page.drawText(`Total  ${money(totalCents)}`, {
    x: 400,
    y: y - 10,
    size: 12,
    font: bold,
  });

  return doc.save();
}

/**
 * Pack several PDFs into one buffer: a little-endian u32 count, then a u32
 * length per document, then the documents back to back.
 *
 * This exists because only a *top-level* Uint8Array survives the return trip as
 * binary. A Uint8Array nested inside an array or an object arrives as a plain
 * object with numeric keys -- no error, just a silently useless and much larger
 * result. So a batch has to come back as one contiguous buffer.
 */
export function packDocuments(documents: Uint8Array[]): Uint8Array {
  const headerBytes = 4 + documents.length * 4;
  let total = headerBytes;
  for (const doc of documents) total += doc.byteLength;

  const packed = new Uint8Array(total);
  const header = new DataView(packed.buffer);
  header.setUint32(0, documents.length, true);

  let offset = headerBytes;
  for (let i = 0; i < documents.length; i++) {
    header.setUint32(4 + i * 4, documents[i]!.byteLength, true);
    packed.set(documents[i]!, offset);
    offset += documents[i]!.byteLength;
  }

  return packed;
}

export function unpackDocuments(packed: Uint8Array): Uint8Array[] {
  const header = new DataView(packed.buffer, packed.byteOffset);
  const count = header.getUint32(0, true);
  const documents = new Array<Uint8Array>(count);

  let offset = 4 + count * 4;
  for (let i = 0; i < count; i++) {
    const length = header.getUint32(4 + i * 4, true);
    documents[i] = packed.subarray(offset, offset + length);
    offset += length;
  }

  return documents;
}

/**
 * Render a whole batch on the worker. One call per invoice spends more time on
 * dispatch than on rendering, and one packed return keeps the bytes contiguous.
 */
export async function renderInvoiceBatchHost(
  invoices: Invoice[],
): Promise<Uint8Array> {
  const documents = new Array<Uint8Array>(invoices.length);
  for (let i = 0; i < invoices.length; i++) {
    documents[i] = await renderInvoiceHost(invoices[i]!);
  }
  return packDocuments(documents);
}

export const renderInvoice = task<Invoice, Uint8Array>({
  f: renderInvoiceHost,
});

export const renderInvoiceBatch = task<Invoice[], Uint8Array>({
  f: renderInvoiceBatchHost,
});
