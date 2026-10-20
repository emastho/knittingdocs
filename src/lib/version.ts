import { readFileSync } from "node:fs";
import { join } from "node:path";

// Shared by benchmark pages and agent documentation; never infer the latest
// published release from the docs site's own package version or a range.
export const docsKnittingVersion: string = JSON.parse(
  readFileSync(
    join(process.cwd(), "node_modules", "@vixeny", "knitting", "package.json"),
    "utf8",
  ),
).version;
