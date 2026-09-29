// Falsify csv-abnf's laws, before any of them is approved.
//
//   bun falsify.ts            every law, with a minimal counterexample each
//   bun falsify.ts -v         also show each law's instance count
//   CORE=./mutant.mjs bun falsify.ts   the control: a broken parser must be
//                             caught, or the falsifier is decoration
//
// A law here is a claim about the parser's answers, checked over many
// inputs. The checker is not involved: what is tested is the STATEMENT, which is
// where a draft law is most likely to be wrong.
//
// Each law below is the same law LAWS.bend states, by the same name, with the
// same hypotheses; a hypothesis the Bend statement forgets is a refutation here,
// which is the point of writing both.

const mine: any = await import(process.env.CORE ?? "./dist/core.mjs");

const verbose = process.argv.includes("-v");

// ---- lists, and what the parser answers ----

function fromL(l: any): any[] {
  const o: any[] = [];
  for (let x = l; x.$ === "Con"; x = x.tail) o.push(x.head);
  return o;
}

// csv-abnf answers Parsed{rows} or Rejected{}; a refusal's kind and position are
// not part of any claim here, so both collapse to rows or "refused".
const myRows = (r: any): string[][] | null =>
  r.$ === "Parsed" ? fromL(r.rows).map((f: any) => fromL(f)) : null;
const canon = (rows: string[][] | null) => (rows === null ? "refused" : "rows" + JSON.stringify(rows));

let SEP = ",";
let CP = 44;
const parse = (s: string) => myCanon(s);
const myCanon = (s: string) => canon(myRows(mine.parse_sep(CP, s)));
const myDecode = (s: string) => {
  const r = mine.parse_sep(CP, s);
  const rows = myRows(r);
  return rows && rows.length === 1 && rows[0].length === 1 ? JSON.stringify(rows[0][0]) : "none";
};

const quoted = (s: string) => s.includes('"');
const cleanRecord = (s: string) => !s.includes(SEP) && !/["\n\r]/.test(s);

// ---- what a law is ----

type Case = string[];

type Law = {
  name: string;
  // what the law assumes of the separator; absent means nothing
  sepOk?: (sep: string) => boolean;
  // one line of plain language, for the approval list
  plain: string;
  holds: (c: Case) => boolean;
  gen: "single" | "pair";
};

const LAWS: Law[] = [
  {
    name: "abnf_empty_input_is_no_record",
    plain: "The empty input holds no record at all.",
    holds: ([s]) => s !== "" || myCanon(s) === "rows[]",
    gen: "single",
  },
  {
    name: "abnf_trailing_newline_adds_nothing",
    plain: "A newline at the very end of the input changes nothing: the record it closes is the one the end of the input would close anyway.",
    holds: ([s]) => myCanon(s + "\n") === myCanon(s),
    gen: "single",
  },
  {
    name: "abnf_blank_line_adds_nothing",
    plain: "With no quote in the input, an empty line produces no record, so inserting one changes nothing at all.",
    holds: ([a, b]) => quoted(a + b) || myCanon(a + "\n\n" + b) === myCanon(a + "\n" + b),
    gen: "pair",
  },
  {
    name: "abnf_clean_input_is_one_field",
    plain: "An input with no separator, no quote and no newline is one record holding one field: the input itself. An empty input holds no record.",
    holds: ([s]) => !cleanRecord(s) || myCanon(s) === (s === "" ? "rows[]" : `rows${JSON.stringify([[s]])}`),
    gen: "single",
  },
  {
    name: "abnf_separator_makes_two_fields",
    sepOk: (sep) => sep !== "\n" && sep !== "\r",
    plain: "Two clean records put on one line with the separator between them are one record of two fields.",
    holds: ([a, b]) => !cleanRecord(a) || !cleanRecord(b) || myCanon(a + SEP + b) === `rows${JSON.stringify([[a, b]])}`,
    gen: "pair",
  },
  {
    name: "abnf_quoted_field_is_its_content",
    sepOk: (sep) => sep !== '"',
    plain: "A quoted field whose content holds no quote of its own is exactly that content, separators and newlines and all.",
    holds: ([s]) => quoted(s) || myCanon('"' + s + '"') === `rows${JSON.stringify([[s]])}`,
    gen: "single",
  },
  {
    name: "abnf_doubled_quote_is_one_quote",
    sepOk: (sep) => sep !== '"',
    plain: "Inside an escaped field, two quotes in the text are one quote in the field (RFC 4180 2DQUOTE).",
    holds: () => myDecode('"a""b"') === JSON.stringify('a"b'),
    gen: "single",
  },
  {
    name: "abnf_lone_empty_field_keeps_its_row",
    sepOk: (sep) => sep !== '"',
    plain: "A quoted empty field is a field, so the row survives: the row is kept.",
    holds: () => myCanon('""\n') === `rows${JSON.stringify([[""]])}`,
    gen: "single",
  },
  {
    name: "abnf_cr_inside_a_field_is_content",
    // The input's own letters are the hypothesis: with the separator `a`, the
    // `a` in `a\rb` is a separator and the claim is false. Stated for every
    // separator in LAWS.bend with these two hypotheses, and found by running
    // the sweep with `a` and `b` among the separators.
    sepOk: (sep) => sep !== "a" && sep !== "b",
    plain: "A CR the line does not end at is content: the record is a-r-b, and the CRLF ends it.",
    holds: () => myCanon("a\rb\r\n") === `rows${JSON.stringify([["a\rb"]])}`,
    gen: "single",
  },
];

// ---- the inputs ----

// The separators the sweep runs. Two of them are letters that appear in the
// laws' own test inputs: a separator the input also uses as text is the case
// that caught `abnf_cr_inside_a_field_is_content`, which is stated for every
// separator and was false for `a`.
const SEPS = [",", ";", "\t", " ", "\u00a3", "\n", "\r", '"', "a", "b"];
let ALPHABET: string[] = [];

const setSep = (sep: string) => {
  SEP = sep;
  CP = sep.codePointAt(0)!;
  ALPHABET = sep === "," ? ["a", ",", '"', "\n", "\r"] : ["a", sep, '"', "\n", "\r", ","];
};

// Every input over the alphabet up to maxLen characters.
function* exhaustive(maxLen: number): Generator<string> {
  let frontier: string[] = [""];
  for (let n = 0; n <= maxLen; n++) {
    for (const s of frontier) yield s;
    const next: string[] = [];
    for (const s of frontier) for (const c of ALPHABET) next.push(s + c);
    frontier = next;
  }
}

let seed = 0x2f6e2b1;
function rnd(n: number): number {
  seed = (seed * 1103515245 + 12345) & 0x7fffffff;
  return seed % n;
}
function randomString(maxLen: number): string {
  let s = "";
  const n = rnd(maxLen + 1);
  for (let i = 0; i < n; i++) s += ALPHABET[rnd(ALPHABET.length)];
  return s;
}

// A counterexample as small as it goes: drop each character in turn, and keep
// the drop when the law is still false. Simple delta debugging -- what is wanted
// is a counterexample a reader can check by eye.
function shrink(holds: (c: Case) => boolean, c: Case): Case {
  let best = c.slice();
  let changed = true;
  while (changed) {
    changed = false;
    for (let i = 0; i < best.length; i++) {
      const t = best[i];
      if (t.length === 0) continue;
      for (let j = 0; j < t.length; j++) {
        const cand = best.slice();
        cand[i] = t.slice(0, j) + t.slice(j + 1);
        if (!holds(cand)) {
          best = cand;
          changed = true;
          break;
        }
      }
      if (changed) break;
    }
  }
  return best;
}

// ---- the sweep ----

const DEPTH = 4;
const RANDOM = 12000;
let failed = 0;

for (const law of LAWS) {
  let instances = 0;
  let counter: Case | null = null;
  let refSep = "";
  const check = (c: Case) => {
    instances += 1;
    if (counter === null && !law.holds(c)) counter = c;
  };
  for (const sep of SEPS) {
    if (law.sepOk && !law.sepOk(sep)) continue;
    setSep(sep);
    if (law.gen === "single") {
      for (const s of exhaustive(DEPTH)) check([s]);
    } else {
      for (const s of exhaustive(DEPTH - 1)) check([s, ""]);
      const singles = [...exhaustive(DEPTH - 2)];
      for (const a of singles) for (const b of singles) check([a, b]);
    }
    for (let i = 0; i < RANDOM; i++) {
      check(law.gen === "single" ? [randomString(14)] : [randomString(8), randomString(8)]);
    }
    if (counter !== null) {
      refSep = sep;
      break;
    }
  }
  if (counter === null) {
    console.log(`HOLDS   ${law.name.padEnd(38)} ${instances} instances`);
    if (verbose) console.log(`        ${law.plain}`);
  } else {
    failed += 1;
    const small = shrink(law.holds, counter);
    console.log(`REFUTED ${law.name.padEnd(38)} ${instances} instances, separator ${JSON.stringify(refSep)}`);
    console.log(`        counterexample: ${small.map((x) => JSON.stringify(x)).join("  +  ")}`);
    console.log(`        ${law.plain}`);
  }
}

console.log(`\n${LAWS.length - failed}/${LAWS.length} laws survived; ${failed} refuted`);
// With CORE set the run is a control: a refutation is the expected outcome, so
// surviving laws are the failure.
process.exit(process.env.CORE && failed === 0 ? 1 : 0);
