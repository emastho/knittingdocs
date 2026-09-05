import { task } from "knitting";
import {
  documentBody,
  type PaperSource,
  readGroup,
  resolveDocument,
  skipOptional,
  readCommandName,
  collectMacros,
  expandMacros,
} from "./tex_scan.ts";

export type { PaperSource };

export type Section = {
  level: number;
  title: string;
};

export type PaperRecord = {
  id: string;
  title: string;
  sections: Section[];
  citationKeys: string[];
  /** Comments stripped, macros expanded, math replaced with placeholders. */
  text: string;
  texBytes: number;
  textBytes: number;
  words: number;
  equations: number;
  figures: number;
  tables: number;
  macrosDefined: number;
  macrosExpanded: number;
  /** True when the tarball is a PDF wrapped in a stub .tex, with no real body. */
  pdfOnly: boolean;
};


// A real LaTeX engine this is not. It is the amount of LaTeX you have to
// understand to turn a paper into something you can index or embed, which is a
// much smaller language than the one TeX actually implements.

const SECTION_COMMANDS: Record<string, number> = {
  chapter: 0,
  section: 1,
  subsection: 2,
  subsubsection: 3,
};

// Macros whose braces hold prose: drop the macro, keep the argument.
const UNWRAP = new Set([
  "emph", "textit", "textbf", "texttt", "textsc", "textrm", "textsf",
  "underline", "mbox", "text", "mathrm", "footnote", "caption", "title",
  "author", "abstract", "paragraph", "subparagraph", "textsuperscript",
]);

// Macros whose braces hold machinery: drop the macro and the argument with it.
const DROP_WITH_ARG = new Set([
  "documentclass", "usepackage", "bibliography", "bibliographystyle",
  "includegraphics", "label", "ref", "eqref", "pageref", "cite", "citep",
  "citet", "citealp", "citeauthor", "citeyear", "input", "include",
  "hypersetup", "setlength", "vspace", "hspace", "includepdf", "pdfoutput",
  "newtheorem", "geometry", "definecolor", "url", "thanks", "nocite",
  "color", "pagestyle", "bibliographyfont", "addtolength",
]);

// `\href{url}{text}`, `\textcolor{red}{text}`: two groups, and only the last
// one is prose.
const KEEP_LAST_GROUP = new Set(["href", "textcolor", "hyperref", "colorbox"]);

// `\newcommand{\dmodel}{d_{\text{model}}}` has two groups and neither is prose.
// Treated like the others it would paste every macro body into the output, which
// is how you end up indexing `d_\textmodel` as if an author had written it.
const DEFINERS = new Set([
  "newcommand", "renewcommand", "providecommand", "def", "DeclareMathOperator",
]);

// Environments whose content is not prose at all.
const SKIP_ENVIRONMENTS = new Set([
  "equation", "equation*", "align", "align*", "eqnarray", "eqnarray*",
  "gather", "gather*", "multline", "multline*", "displaymath", "math",
  "array", "tabular", "tabular*", "tabularx", "matrix", "pmatrix", "bmatrix",
  "verbatim", "lstlisting", "tikzpicture", "thebibliography", "algorithmic",
  "algorithm", "picture", "filecontents", "filecontents*",
]);

const MATH_ENVIRONMENTS = new Set([
  "equation", "equation*", "align", "align*", "eqnarray", "eqnarray*",
  "gather", "gather*", "multline", "multline*", "displaymath",
]);

type EnvCounts = { equations: number; figures: number; tables: number };

/**
 * Remove environments whose content is not prose, counting them on the way out.
 *
 * Nesting is the whole difficulty: a `figure` holding a `tabular` holding an
 * `align` has to come out as one unit, so this tracks depth per environment
 * name rather than searching for the next `\end`.
 */
function stripEnvironments(src: string): { text: string; counts: EnvCounts } {
  const counts: EnvCounts = { equations: 0, figures: 0, tables: 0 };
  const marker = /\\(begin|end)\s*\{([^}]*)\}/g;
  let out = "";
  let cursor = 0;
  let skipping: string | null = null;
  let depth = 0;
  let match: RegExpExecArray | null;

  while ((match = marker.exec(src)) !== null) {
    const [, kind, rawName] = match;
    const name = rawName!.trim();

    if (skipping === null) {
      if (kind === "begin") {
        const base = name.replace(/\*$/, "");
        if (MATH_ENVIRONMENTS.has(name)) counts.equations++;
        else if (base === "figure" || base === "subfigure") counts.figures++;
        else if (base === "table") counts.tables++;

        if (SKIP_ENVIRONMENTS.has(name)) {
          out += src.slice(cursor, match.index) + "\n";
          skipping = name;
          depth = 1;
          continue;
        }
      }
      out += src.slice(cursor, match.index);
      cursor = marker.lastIndex;
      continue;
    }

    if (name !== skipping) continue;
    if (kind === "begin") depth++;
    else if (--depth === 0) {
      skipping = null;
      cursor = marker.lastIndex;
    }
  }

  if (skipping === null) out += src.slice(cursor);
  return { text: out, counts };
}

function stripMath(src: string): { text: string; equations: number } {
  let equations = 0;
  const bump = () => {
    equations++;
    return " ";
  };
  const text = src
    .replace(/\$\$[\s\S]*?\$\$/g, bump)
    .replace(/\\\[[\s\S]*?\\\]/g, bump)
    .replace(/(?<!\\)\$(?:\\.|[^$\\])*\$/g, () => " ")
    .replace(/\\\((?:[\s\S]*?)\\\)/g, () => " ");
  return { text, equations };
}

type Walked = {
  text: string;
  sections: Section[];
  citationKeys: string[];
};

/**
 * The last pass: keep prose, drop markup, and pick up structure on the way.
 *
 * Three kinds of macro get three different treatments -- some hold prose worth
 * keeping, some hold machinery worth dropping whole, and the long tail is
 * neither, so the macro goes and its braces stay.
 */
function walkMacros(
  src: string,
  sections: Section[] = [],
  citationKeys: string[] = [],
  depth = 0,
): Walked {
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
    if (!name) {
      i = backslash + 1;
      continue;
    }
    let cursor = backslash + 1 + name.length;
    const base = name.replace(/\*$/, "");

    if (DEFINERS.has(base)) {
      // Drop the name group and the body group both.
      if (src[cursor] === "\\") cursor += 1 + readCommandName(src, cursor).length;
      let group = readGroup(src, cursor);
      if (group) cursor = group.end;
      cursor = skipOptional(src, skipOptional(src, cursor));
      group = readGroup(src, cursor);
      if (group) cursor = group.end;
      out += " ";
      i = cursor;
      continue;
    }

    if (base in SECTION_COMMANDS) {
      cursor = skipOptional(src, cursor);
      const group = readGroup(src, cursor);
      if (group) {
        const title = cleanInline(group.body);
        sections.push({ level: SECTION_COMMANDS[base]!, title });
        out += `\n\n${title}\n\n`;
        i = group.end;
        continue;
      }
    }

    if (base.startsWith("cite") || base === "nocite") {
      cursor = skipOptional(src, skipOptional(src, cursor));
      const group = readGroup(src, cursor);
      if (group) {
        for (const key of group.body.split(",")) {
          const trimmed = key.trim();
          if (trimmed) citationKeys.push(trimmed);
        }
        out += " ";
        i = group.end;
        continue;
      }
    }

    if (KEEP_LAST_GROUP.has(base)) {
      const url = readGroup(src, skipOptional(src, cursor));
      const label = url ? readGroup(src, url.end) : null;
      if (label) {
        out += walkMacros(label.body, sections, citationKeys, depth + 1).text;
        i = label.end;
        continue;
      }
    }

    if (UNWRAP.has(base)) {
      cursor = skipOptional(src, cursor);
      const group = readGroup(src, cursor);
      // The braces held prose, and prose holds more macros -- `\emph{\texttt{x}}`
      // only comes out clean if the body is walked too, not pasted through.
      if (group && depth < MAX_UNWRAP_DEPTH) {
        out += walkMacros(group.body, sections, citationKeys, depth + 1).text;
        i = group.end;
        continue;
      }
    }

    if (DROP_WITH_ARG.has(base)) {
      cursor = skipOptional(src, cursor);
      const group = readGroup(src, cursor);
      if (group) {
        out += " ";
        i = group.end;
        continue;
      }
    }

    // Everything else: drop the command, keep whatever it wrapped.
    out += " ";
    i = cursor;
  }

  return { text: out, sections, citationKeys };
}

// Prose nests, but not forever. The ceiling keeps a pathological document from
// turning into a stack overflow inside a worker.
const MAX_UNWRAP_DEPTH = 12;

function cleanInline(raw: string): string {
  return raw
    .replace(/\\[A-Za-z]+\*?/g, " ")
    .replace(/\\./g, " ") // \\, \&, \% and the rest of the escapes
    .replace(/[{}$]/g, "")
    .replace(/\s+/g, " ")
    .trim();
}

function tidy(raw: string): string {
  return raw
    .replace(/[{}]/g, "")
    .replace(/~/g, " ")
    .replace(/[ \t]+/g, " ")
    .replace(/ ?\n ?/g, "\n")
    .replace(/\n{3,}/g, "\n\n")
    .trim();
}

export function parsePaperHost(source: PaperSource): PaperRecord {
  const texBytes = Object.values(source.files)
    .reduce((total, text) => total + text.length, 0);
  const resolved = resolveDocument(source.files);

  if (resolved === null) {
    return emptyRecord(source.id, texBytes);
  }

  const merged = resolved.merged;
  // Definitions live in the preamble; prose lives in the body. Collect from the
  // whole file, then index only what is between \begin{document} and its \end,
  // because a preamble full of \usepackage lines is not text anybody wrote.
  const macros = collectMacros(merged);
  const { text: expanded, expansions } = expandMacros(documentBody(merged), macros);

  const titleMatch = /\\title\s*(?:\[[^\]]*\])?\s*\{/.exec(merged);
  const titleGroup = titleMatch
    ? readGroup(merged, titleMatch.index + titleMatch[0].length - 1)
    : null;

  const { text: withoutEnvs, counts } = stripEnvironments(expanded);
  const { text: withoutMath, equations: inlineEquations } = stripMath(
    withoutEnvs,
  );
  const walked = walkMacros(withoutMath);
  const text = tidy(walked.text);
  const words = text.length === 0 ? 0 : text.split(/\s+/).length;

  return {
    id: source.id,
    title: titleGroup ? cleanInline(titleGroup.body) : "",
    sections: walked.sections,
    citationKeys: walked.citationKeys,
    text,
    texBytes,
    textBytes: text.length,
    words,
    equations: counts.equations + inlineEquations,
    figures: counts.figures,
    tables: counts.tables,
    macrosDefined: macros.size,
    macrosExpanded: expansions,
    // Some submissions are a PDF with a two-line .tex wrapper around it. There
    // is nothing to index, and a corpus job should say so rather than record a
    // paper with no words in it.
    pdfOnly: merged.includes("\\includepdf") && words < 200,
  };
}

function emptyRecord(id: string, texBytes: number): PaperRecord {
  return {
    id,
    title: "",
    sections: [],
    citationKeys: [],
    text: "",
    texBytes,
    textBytes: 0,
    words: 0,
    equations: 0,
    figures: 0,
    tables: 0,
    macrosDefined: 0,
    macrosExpanded: 0,
    pdfOnly: false,
  };
}

export const parsePaper = task<PaperSource, PaperRecord>({ f: parsePaperHost });
