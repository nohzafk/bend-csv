// The oracle for bend-csv: this parser against the reference.
//
//   bun oracle.ts        the sweep; exits 1 on any difference that is not
//                        classified below
//   bun oracle.ts -v     every case, one line each
//
// What is compared strictly: whether the input is read at all, and the rows.
//
// Two difference classes, reported as known rather than hidden (the blank-record
// class is the approved semantic change: this parser keeps a blank line as a
// record of one empty field, the reference drops it):
//   * blank records: the rows equal the reference's rows with [""] inserted at
//     every blank line an independent scan of the input finds (see blanks()).
//     Any other difference, an extra, missing or misplaced row, fails.
//   * a CRLF inside an escaped field. This parser keeps the CR (a deliberate
//     decision: the CR is data), and the reference
//     normalizes it to LF. A mismatch counts as known only when the input holds
//     a CR and the rows agree after every CRLF in this parser's fields would
//     be read as LF. Anything else is a failure.
//
// Not compared at all: a byte-order mark (the host's job; no input here carries one), and the separators LF, CR and the quote:
// both this parser and the reference's caller read those as themselves rather
// than as a separator, so a sweep over them would be comparing two different
// questions.
//
// The sweep runs once per separator, over the alphabet {a, the separator,
// comma, quote, LF, CR} up to length four, plus random inputs up to length
// twelve from a fixed seed, so a failure reproduces.

import { parse as ref } from "./reference/std/parse.ts";
// The value is imported at run time so CORE can point the sweep at a mutant.
const mine: any = await import(process.env.CORE ?? "./dist/core.mjs");

const verbose = process.argv.includes("-v");

type Canon = { ok: true; rows: string[][] } | { ok: false };

const flat = <T,>(xs: any): T[] => (xs.$ === "Nil" ? [] : [xs.head, ...flat<T>(xs.tail)]);

// This parser answers Parsed{rows} or Rejected{}; a refusal's kind and position
// are not part of any claim here.
function a(sep: number, s: string): Canon {
  const r = mine.parse_sep(sep, s);
  if (r.$ === "Rejected") return { ok: false };
  return { ok: true, rows: flat<any>(r.rows).map((f) => flat<string>(f)) };
}

// The reference returns the rows, or throws on an input it will not read.
function b(sep: string, s: string): Canon {
  try {
    return { ok: true, rows: ref(s, { separator: sep }) };
  } catch {
    return { ok: false };
  }
}

const same = (p: string[][], q: string[][]) => JSON.stringify(p) === JSON.stringify(q);
const normalize = (rows: string[][]) => rows.map((r) => r.map((f) => f.split("\r\n").join("\n")));

// Blank records, found by a scan that does not use the parser: the positions
// (as a count of non-blank records before it) of every line that is empty at a
// record start outside quotes: LF, CRLF, or a lone CR that ends the input.
function blanks(s: string): number[] {
  const at: number[] = [];
  let i = 0;
  let recs = 0;
  while (i < s.length) {
    if (s[i] === "\n") { at.push(recs); i += 1; continue; }
    if (s[i] === "\r" && s[i + 1] === "\n") { at.push(recs); i += 2; continue; }
    if (s[i] === "\r" && i + 1 === s.length) { at.push(recs); i += 1; continue; }
    let q = false;
    while (i < s.length && (q || s[i] !== "\n")) { if (s[i] === '"') q = !q; i += 1; }
    i += 1;
    recs += 1;
  }
  return at;
}

// The reference's rows with an empty-field record put back at every blank line.
function withBlanks(rows: string[][], at: number[]): string[][] {
  const out: string[][] = [];
  let k = 0;
  for (let r = 0; r <= rows.length; r++) {
    while (k < at.length && at[k] === r) { out.push([""]); k += 1; }
    if (r < rows.length) out.push(rows[r]);
  }
  return out;
}

// ok: identical. known-crlf: only a CRLF in a quoted field differs.
// known-blank: differs only by the blank records this parser keeps and the
// reference drops -- exactly those, at exactly the places the scan finds.
// known-blank-crlf: both classes at once.
function klass(x: Canon, y: Canon, input: string): "ok" | "known-crlf" | "known-blank" | "known-blank-crlf" | "bad" {
  if (x.ok !== y.ok) return "bad";
  if (!x.ok) return "ok";
  if (same(x.rows, y.rows)) return "ok";
  const at = blanks(input);
  const want = withBlanks(y.rows, at);
  if (at.length > 0 && same(x.rows, want)) return "known-blank";
  if (input.includes("\r") && at.length === 0 && same(normalize(x.rows), y.rows)) return "known-crlf";
  if (input.includes("\r") && at.length > 0 && same(normalize(x.rows), want)) return "known-blank-crlf";
  return "bad";
}

const show = (s: string) => JSON.stringify(s);

let total = 0;
let known = 0;
let knownBlank = 0;
let knownBoth = 0;
const wrong = new Map<string, string[]>();

function check(sep: string, cp: number, s: string) {
  total += 1;
  const x = a(cp, s);
  const y = b(sep, s);
  const k = klass(x, y, s);
  if (k === "ok") {
    if (verbose) console.log(`ok    sep=${show(sep)} in=${show(s)} ${x.ok ? JSON.stringify(x.rows) : "refused"}`);
    return;
  }
  const line = `sep=${show(sep)} in=${show(s)} | here=${x.ok ? JSON.stringify(x.rows) : "refused"} ref=${y.ok ? JSON.stringify(y.rows) : "refused"}`;
  if (k !== "bad") {
    if (k === "known-crlf") known += 1;
    else if (k === "known-blank") knownBlank += 1;
    else knownBoth += 1;
    if (verbose) console.log(`known ${line}`);
    return;
  }
  const seen = wrong.get("disagree") ?? [];
  if (seen.length < 8) seen.push(line);
  wrong.set("disagree", seen);
}

function* allStrings(alphabet: string[], max: number): Generator<string> {
  let frontier: string[] = [""];
  for (let n = 0; n <= max; n++) {
    for (const s of frontier) yield s;
    const next: string[] = [];
    for (const s of frontier) for (const c of alphabet) next.push(s + c);
    frontier = next;
  }
}

let seed = 0x2f6e2b1;
function rnd(n: number): number {
  seed = (seed * 1103515245 + 12345) & 0x7fffffff;
  return seed % n;
}

// The comma, and five more. Two of them are letters: a separator that also
// appears as text in the input is a case the falsifier was blind to once.
const SEPS = [",", ";", "\t", " ", "\u00a3", "\u20ac", "\u{1f600}", "a", "b"];

for (const sep of SEPS) {
  const cp = sep.codePointAt(0)!;
  const alphabet = [...new Set(["a", ",", "\"", "\n", "\r", sep])];
  for (const s of allStrings(alphabet, 4)) check(sep, cp, s);
  for (let i = 0; i < 20000; i++) {
    let s = "";
    const n = rnd(13);
    for (let j = 0; j < n; j++) s += alphabet[rnd(alphabet.length)];
    check(sep, cp, s);
  }
}

console.log(`${total} inputs compared; known classes: ${knownBlank} blank-record, ${known} quoted-CRLF, ${knownBoth} both`);
if (wrong.size === 0) {
  console.log("AGREE: the parser reads what the reference reads, on every input not classified above");
  process.exit(0);
}
for (const [, lines] of wrong) {
  console.log(`\ndisagreeing (${lines.length} shown):`);
  for (const l of lines) console.log(`  ${l}`);
}
console.log("\nDISAGREE: this parser and the reference part ways outside the known class");
process.exit(1);
