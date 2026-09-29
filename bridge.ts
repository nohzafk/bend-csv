// csv-abnf for a TypeScript host: the parser behind one function.
//
//   import { parse, CsvParseError } from "./bridge.ts";
//
//   const rows = parse("a,b\r\n");                    // string[][]
//   const more = parse(text, { separator: ";" });
//
// Throws CsvParseError when the input is not a file of the format. The refusal
// carries no position and no reason: this parser has neither (its laws are
// stated on the rows and on whether a file was read at all), so a host that
// needs to know *where* a defect is wants a parser that reports positions, such as Deno's @std/csv.
//
// SIZE. The parser holds a token per character and reads the input three times,
// so this path costs memory rather than stack: about 400 MB of heap per MB of
// input, against the native build's 74, and a 10 MB file takes 1.8 s and 4 GB.
// A host parsing very large files should prefer the native build
// (`bend native/bench.bend -o native/bench`).
//
// The byte-order mark is stripped here, because that is the host's job.
//
// The separator is checked here rather than in the core, and that is deliberate:
// the parser reads LF, CR and the quote as themselves before it ever compares
// them with the separator, so a host that passed one would get the reading of a
// file whose separator never appears. The core states that; the host refuses it.

import { parse_sep } from "./dist/core.mjs";

export class CsvParseError extends Error {
  constructor(message = "not a file of the format") {
    super(message);
    this.name = "CsvParseError";
  }
}

const flat = <T,>(xs: any): T[] => {
  const out: T[] = [];
  for (let x = xs; x.$ === "Con"; x = x.tail) out.push(x.head);
  return out;
};

export function parse(input: string, options: { separator?: string } = {}): string[][] {
  const separator = options.separator ?? ",";
  const points = [...separator];
  if (points.length !== 1) {
    throw new TypeError(`the separator must be one character: ${JSON.stringify(separator)}`);
  }
  const cp = points[0].codePointAt(0)!;
  if (cp === 10 || cp === 13 || cp === 34) {
    throw new TypeError(
      `the separator cannot be LF, CR or the quote (${JSON.stringify(separator)}): the parser reads those as themselves first`,
    );
  }
  const text = input.startsWith("\uFEFF") ? input.slice(1) : input;
  const answer: any = parse_sep(cp, text);
  if (answer.$ === "Rejected") throw new CsvParseError();
  return flat<any>(answer.rows).map((field) => flat<string>(field));
}
