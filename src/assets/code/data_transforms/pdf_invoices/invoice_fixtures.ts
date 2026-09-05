import type { Invoice, InvoiceLine } from "./render_invoice.ts";

/**
 * Synthetic billing run. Line counts vary so that some invoices spill onto a
 * second page -- a fixed-size document would hide the layout work entirely.
 */

const PRODUCTS = [
  "Worker pool seat",
  "Shared memory arena",
  "Priority support hour",
  "Build minutes, 1k block",
  "Managed queue, monthly",
  "Audit log retention, 30d",
];

const REGIONS = ["us-east", "us-west", "eu-central", "ap-south"];

export function buildInvoices(count: number): Invoice[] {
  const invoices = new Array<Invoice>(count);

  for (let i = 0; i < count; i++) {
    const lineCount = 24 + (i % 60);
    const lines = new Array<InvoiceLine>(lineCount);

    for (let k = 0; k < lineCount; k++) {
      lines[k] = {
        description: `${PRODUCTS[(i + k) % PRODUCTS.length]} - ${
          REGIONS[(i + k) % REGIONS.length]
        } tier ${(i + k) % 4}`,
        quantity: 1 + ((i + k) % 7),
        unitCents: 1_200 + ((i * 7 + k * 13) % 8_800),
      };
    }

    invoices[i] = {
      number: `INV-2026-${10_000 + i}`,
      customer: `Customer ${i % 500}`,
      issuedAt: "2026-09-05",
      lines,
    };
  }

  return invoices;
}

export function batched<T>(values: T[], size: number): T[][] {
  const batches: T[][] = [];
  for (let i = 0; i < values.length; i += size) {
    batches.push(values.slice(i, i + size));
  }
  return batches;
}
