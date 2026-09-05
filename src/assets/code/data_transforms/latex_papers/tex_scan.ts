/** One arXiv submission: every .tex file in the tarball, keyed by path. */
export type PaperSource = {
  id: string;
  files: Record<string, string>;
};

// Reading TeX far enough to find the prose in it. A real LaTeX engine this is
// not -- it is the amount of the language you have to understand to turn a
// submission into something you can index, which is a much smaller language
// than the one TeX actually implements.

/**
 * Read a balanced `{...}` group starting at the opening brace.
 *
 * This is the workhorse of the whole parser, and the reason parsing a paper is
 * real CPU work rather than a few regexes: braces nest, and TeX lets you escape
 * them, so you cannot match them without walking the string.
 */
export function readGroup(
  src: string,
  open: number,
): { body: string; end: number } | null {
  if (src[open] !== "{") return null;
  let depth = 0;
  for (let i = open; i < src.length; i++) {
    const ch = src[i];
    if (ch === "\\") {
      i++; // an escaped brace is a character, not a delimiter
      continue;
    }
    if (ch === "{") depth++;
    else if (ch === "}") {
      depth--;
      if (depth === 0) return { body: src.slice(open + 1, i), end: i + 1 };
    }
  }
  return null;
}

export function skipOptional(src: string, at: number): number {
  if (src[at] !== "[") return at;
  const close = src.indexOf("]", at);
  return close === -1 ? at : close + 1;
}

export function readCommandName(src: string, backslash: number): string {
  let i = backslash + 1;
  while (i < src.length && /[A-Za-z]/.test(src[i]!)) i++;
  if (i === backslash + 1) return src[i] ?? ""; // \\, \%, \& and friends
  let name = src.slice(backslash + 1, i);
  if (src[i] === "*") name += "*";
  return name;
}

/** Drop `%` comments, but not `\%`, and keep the line structure. */
export function stripComments(src: string): string {
  const lines = src.split("\n");
  for (let i = 0; i < lines.length; i++) {
    const line = lines[i]!;
    let at = line.indexOf("%");
    // A `%` is only a comment when the backslashes before it are an even run;
    // `\%` is a literal percent sign, and `\\%` is a line break then a comment.
    while (at > 0) {
      let backslashes = 0;
      for (let j = at - 1; j >= 0 && line.charCodeAt(j) === 92; j--) backslashes++;
      if (backslashes % 2 === 0) break;
      at = line.indexOf("%", at + 1);
    }
    if (at !== -1) lines[i] = line.slice(0, at);
  }
  return lines.join("\n");
}

/**
 * Splice `\input`/`\include` files in, so the paper becomes one string.
 *
 * A paper is only meaningful as a whole -- a task that took one .tex file at a
 * time would be splitting a document mid-sentence. This is why the unit of work
 * here is a submission, not a file.
 */
function inlineInputs(
  files: Record<string, string>,
  entry: string,
  seen: Set<string>,
): string {
  if (seen.has(entry)) return "";
  seen.add(entry);
  const src = stripComments(files[entry] ?? "");
  let out = "";
  let i = 0;
  while (i < src.length) {
    const backslash = src.indexOf("\\", i);
    if (backslash === -1) {
      out += src.slice(i);
      break;
    }
    out += src.slice(i, backslash);
    const name = readCommandName(src, backslash);
    if (name !== "input" && name !== "include") {
      out += src.slice(backslash, backslash + 1 + Math.max(name.length, 1));
      i = backslash + 1 + Math.max(name.length, 1);
      continue;
    }
    const group = readGroup(src, backslash + 1 + name.length);
    if (!group) {
      out += src.slice(backslash, backslash + 1 + name.length);
      i = backslash + 1 + name.length;
      continue;
    }
    out += "\n" + inlineInputs(files, resolveName(files, group.body), seen) +
      "\n";
    i = group.end;
  }
  return out;
}

function resolveName(files: Record<string, string>, raw: string): string {
  const wanted = raw.trim().replace(/^\.\//, "");
  for (const candidate of [wanted, `${wanted}.tex`]) {
    if (files[candidate] !== undefined) return candidate;
  }
  // Tarballs nest sources in directories; match on the basename as a fallback.
  const base = wanted.split("/").pop()!;
  for (const key of Object.keys(files)) {
    const keyBase = key.split("/").pop()!;
    if (keyBase === base || keyBase === `${base}.tex`) return key;
  }
  return wanted;
}

type Macro = { arity: number; body: string };

/**
 * Collect `\newcommand`-style definitions.
 *
 * Every paper invents its own shorthand -- `\newcommand{\R}{\mathbb{R}}`,
 * `\newcommand{\model}{Transformer}` -- and leaving them unexpanded means your
 * index is full of tokens no reader ever typed.
 */
export function collectMacros(src: string): Map<string, Macro> {
  const macros = new Map<string, Macro>();
  const definers = /\\(?:re)?newcommand\*?|\\providecommand\*?|\\def/g;
  let match: RegExpExecArray | null;
  while ((match = definers.exec(src)) !== null) {
    let i = match.index + match[0].length;
    let name: string | null = null;

    if (src[i] === "{") {
      const group = readGroup(src, i);
      if (!group) continue;
      const inner = group.body.trim();
      if (!inner.startsWith("\\")) continue;
      name = inner.slice(1);
      i = group.end;
    } else if (src[i] === "\\") {
      name = readCommandName(src, i);
      i += 1 + name.length;
    }
    if (!name || !/^[A-Za-z]+\*?$/.test(name)) continue;

    let arity = 0;
    if (src[i] === "[") {
      const close = src.indexOf("]", i);
      if (close !== -1) {
        arity = Number.parseInt(src.slice(i + 1, close), 10) || 0;
        i = close + 1;
      }
    }
    i = skipOptional(src, i); // an optional-argument default value
    const body = readGroup(src, i);
    if (!body) continue;
    macros.set(name, { arity, body: body.body });
  }
  return macros;
}

// Macro bodies call other macros, so one pass is not enough. Papers do not nest
// them deeply, though, and a fixed ceiling is what keeps a recursive definition
// from turning one bad submission into a hung worker.
const MAX_EXPANSION_PASSES = 4;

export function expandMacros(
  src: string,
  macros: Map<string, Macro>,
): { text: string; expansions: number } {
  let text = src;
  let expansions = 0;

  for (let pass = 0; pass < MAX_EXPANSION_PASSES; pass++) {
    let out = "";
    let i = 0;
    let hits = 0;

    while (i < text.length) {
      const backslash = text.indexOf("\\", i);
      if (backslash === -1) {
        out += text.slice(i);
        break;
      }
      out += text.slice(i, backslash);
      const name = readCommandName(text, backslash);
      const macro = name ? macros.get(name) : undefined;
      if (!macro) {
        const width = 1 + Math.max(name.length, 1);
        out += text.slice(backslash, backslash + width);
        i = backslash + width;
        continue;
      }

      let cursor = backslash + 1 + name.length;
      const args: string[] = [];
      for (let a = 0; a < macro.arity; a++) {
        while (text[cursor] === " ") cursor++;
        const group = readGroup(text, cursor);
        if (!group) break;
        args.push(group.body);
        cursor = group.end;
      }
      if (args.length < macro.arity) {
        const width = 1 + name.length;
        out += text.slice(backslash, backslash + width);
        i = backslash + width;
        continue;
      }

      out += macro.body.replace(/#(\d)/g, (_, digit: string) =>
        args[Number(digit) - 1] ?? "");
      i = cursor;
      hits++;
    }

    text = out;
    expansions += hits;
    if (hits === 0) break;
  }

  return { text, expansions };
}

/**
 * Pick the file that starts the document, and return it already resolved.
 *
 * A tarball has no manifest, so the entry point is whatever holds
 * `\begin{document}` -- but submissions routinely ship several: a paper, a
 * rebuttal, a supplementary, a leftover style demo, each with its own
 * `\documentclass`. The one you want is not the longest file, it is the one
 * that pulls in the most document once its `\input`s are resolved. YOLOv3 is
 * the case that forces this: its entry point is 3 KB that inlines the paper,
 * while the supplementary next to it is 11 KB on its own.
 *
 * Resolving is the expensive part, so the winner's text comes back with it
 * rather than being rebuilt by the caller.
 */
export function resolveDocument(
  files: Record<string, string>,
): { main: string; merged: string } | null {
  let best: { main: string; merged: string } | null = null;
  for (const [name, text] of Object.entries(files)) {
    if (!text.includes("\\begin{document}")) continue;
    const merged = inlineInputs(files, name, new Set());
    if (best === null || merged.length > best.merged.length) {
      best = { main: name, merged };
    }
  }
  return best;
}

/** Everything between `\begin{document}` and `\end{document}`. */
export function documentBody(src: string): string {
  const start = src.indexOf("\\begin{document}");
  if (start === -1) return src;
  const from = start + "\\begin{document}".length;
  const end = src.lastIndexOf("\\end{document}");
  return end > from ? src.slice(from, end) : src.slice(from);
}
