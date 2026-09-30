# bend-csv

A CSV parser written in Bend, with a native build, a prebuilt JavaScript module,
and machine-checked proofs for twelve properties of its core.

**Fast without giving up proofs.** In our 10 MB benchmark, the native build is
about **2x as fast as Deno's `@std/csv` parser and uses 39% less peak memory**.
The generated JavaScript build is close in speed: 265 ms versus 297 ms, though
it uses more memory. The reference runs in Bun for these comparisons.
See [Performance](#performance) for the results and measurement scope.

Use the core from Bend, or use the TypeScript bridge to get `string[][]` rows.
The JavaScript module is included: no Bend compiler or build step is needed
for TypeScript use. Both interfaces support custom separators, quoted fields,
and multiline field content.

This is a whole-input reader, not a streaming parser or CSV writer. Invalid
CSV produces an error without a location or detailed explanation.

## Getting started

Bend callers need Bend 2.0.34. TypeScript callers use `bridge.ts` and the
included prebuilt module; they do not need Bend or the emitter.
Build and verification tools are listed in the contributing section below.

### Bend

Import `bend-csv` from Bend Hub. Save this as `example.bend`, then run
`bend example.bend`:

```bend
import Base
import bend-csv@0.1.0.0/core.bend as C

def describe(r: C.Ans) -> String:
  match r:
    case C.Parsed{rows}:
      "read " ++ Nat.show(List.length(&2, List<&2, String>, rows)) ++ " rows"
    case C.Rejected{}:
      "invalid CSV"

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(describe(C.parse("a,b\r\nc,d\r\n")))           # read 2 rows
    IO.print(describe(C.parse_sep(59, "a;b\r\nc;d\r\n")))  # read 2 rows
    IO.print(describe(C.parse("a,\"b")))                    # invalid CSV
```

`parse(s)` uses a comma. `parse_sep(sep, s)` takes a separator as a Unicode code
point; `59` is a semicolon. Both return `Parsed{rows}` or `Rejected{}`.
The rows are Bend lists of lists of strings.

Bend requires `match` to inspect a parameter or field, so this example passes
the result to `describe` before matching it.

### TypeScript

`bridge.ts` imports the prebuilt module `dist/core.mjs` (with its declarations
`dist/core.d.mts`), which is committed. Using the bridge needs neither Bend nor
a build step.

The bridge wraps the generated module and converts Bend lists to arrays:

```ts
import { parse, CsvParseError } from "./bridge.ts";

const rows = parse('a,b\r\nc,"d""e"\r\n');
// [["a", "b"], ["c", 'd"e']]

const semi = parse("a;b\n", { separator: ";" });
// [["a", "b"]]

try {
  parse('a,"b'); // Unclosed quoted field.
} catch (e) {
  if (e instanceof CsvParseError) console.log("invalid CSV");
  else throw e;
}
```

The bridge removes an initial byte-order mark (U+FEFF). It throws `TypeError`
if the separator is not exactly one Unicode code point, or is LF, CR, or `"`.
Invalid CSV throws `CsvParseError`. Neither error handling nor BOM removal
changes the core's parsing rules.

JavaScript callers need a runtime or build step that can load `bridge.ts`.
The generated `dist/core.mjs` is JavaScript, but returns Bend data rather than
arrays. The TypeScript bridge is the convenient interface for array results.

## Performance

The native build beats Deno's established `@std/csv` parser on both time and
peak memory at every measured size. At 10 MB it is **about 2x as fast and uses
39% less peak memory**. The generated JavaScript build is close in speed:
36 ms versus 36 ms at 1 MB, and 265 ms versus 297 ms at 10 MB.

The JavaScript build does not match the reference's memory use. At 10 MB it
uses 400 MB versus 286 MB (about 1.4x); at 1 MB it uses 92 MB versus 50 MB.

These are results from one 14-core Apple machine with 36 GB of memory.
The reference is the Deno standard-library parser **running in Bun**, not a
measurement of the Deno runtime.

| Build and input | bend-csv: time / peak RSS | Reference: time / peak RSS |
| --- | --- | --- |
| Native, 0.1 MB | 2 ms / 4 MB | 4.4 ms / 26 MB |
| Native, 1 MB | 11 ms / 19 MB | 33 ms / 50 MB |
| Native, 10 MB | 147 ms / 172 MB | 291 ms / 284 MB |
| JavaScript, 1 MB | 36 ms / 92 MB | 36 ms / 50 MB |
| JavaScript, 10 MB | 265 ms / 400 MB | 297 ms / 286 MB |

These comparisons apply to this corpus and benchmark setup, not to arbitrary
CSV files or host applications. They measure the native and generated cores,
not the end-to-end TypeScript bridge.

The largest native input measured is 40 MB: 623 ms and 682 MB peak RSS for
about 1.7 million rows. The largest JavaScript input measured is 10 MB.
Both builds complete those inputs without a stack overflow.

### Measurement scope

- Each size runs in three fresh processes. The table reports the shortest time
  and highest peak RSS, which can come from different runs.
- The JavaScript benchmark calls the generated core directly, **not the
  TypeScript bridge**. Its timer includes dynamic module import, parsing, and
  counting the resulting rows. It does not convert all fields to arrays.
- The native timer includes parsing, counting rows, fields, and characters, and
  printing that summary. File reading occurs before the timer starts.
- Peak RSS is the whole process's maximum resident memory, measured with macOS
  `time -l`. It includes input preparation, the result, and the runtime.
  Native and JavaScript results have different representations and runtime
  overheads.

The corpus combines quoted commas and doubled quotes, a quoted LF with empty
fields, and an empty quoted field. Record endings are CRLF. It excludes CRLF
inside quoted fields, where the parsers differ.

Reproduce the benchmarks from the checkout:

```sh
bend native/bench.bend -o native/bench
bun native/scale.ts 10
bun bench_js.ts
```

See [NOTES.md](NOTES.md) for additional measurements and benchmark details.

## Parsing behavior

Fields remain strings. The parser does not interpret headers or convert values
to numbers. Separators inside quoted fields are content, and doubled quotes
inside a quoted field become a single quote.

These examples use the TypeScript bridge with its default comma separator:

| Input | Result |
| --- | --- |
| `""` (empty input) | `[]` |
| `'a,b\r\n'` | `[["a", "b"]]` |
| `'a,b\n'` | `[["a", "b"]]` |
| `'a\r\n\r\nb'` | `[["a"], [""], ["b"]]` |
| `'""\r\n'` | `[[""]]` |
| `',\r\n'` | `[["", ""]]` |
| `'a\rb\r\n'` | `[["a\rb"]]` |
| `'"a\r\nb"'` | `[["a\r\nb"]]` |
| `'a,"b'` | throws `CsvParseError` |

### Errors and separator constraints

The core returns `Rejected{}` for malformed quoting, such as an unclosed quoted
field or a quote inside an unquoted field. The bridge turns rejection into
`CsvParseError`. There is no line number, column number, or detailed reason.
If your application needs to point users to an error, use a parser with
location-aware diagnostics, such as Deno's `@std/csv`.

Bend callers should use a separator other than LF, CR, or `"`. The core does not
validate this argument; the bridge does. See [LAWS.bend](LAWS.bend) for the exact
separator hypotheses of each proved property.

## Verified properties

The twelve laws are in [LAWS.bend](LAWS.bend), with proofs in
[PROOF.bend](PROOF.bend). A law states a property of the core; its proof covers
that statement under its specified hypotheses. Together, these laws do not
establish full RFC conformance or fully specify every parsing behavior.

| Property | Scope |
| --- | --- |
| Empty input produces no records | Any separator |
| Adding LF after an input whose last character is not LF changes nothing (no phantom row) | Any separator and input; not claimed for empty input or input already ending in LF, where the LF is a blank row |
| A blank LF line is a record of one empty field, read exactly as a `""` line | Any prefix without a quote; separator is not a quote |
| A blank CRLF line is read exactly as a `""` line | Same |
| A blank first line (LF, or CRLF) is read exactly as a first `""` line | Separator is not a quote |
| Clean input produces one field containing that input; empty input produces no records | No separator, quote, CR, or LF in the input |
| Joining two clean strings with a separator produces two fields | Separator is neither LF nor CR |
| A quoted field returns its content | Content has no quotes; separator is not a quote |
| A doubled quote becomes one quote | The specific input `"a""b"`; separator is not a quote |
| A quoted empty field keeps its row | The specific input `""\n`; separator is not a quote |
| CR within an unquoted field remains content | The specific input `a\rb\r\n`; separator is neither `a` nor `b` |

The table summarizes the statements. The source defines their exact quantifiers
and hypotheses.

### What the checks establish

- **Proofs:** `bend --check-only PROOF.bend` accepts all twelve proofs and prints
  `ALL PROOFS CHECK`.
- **Tests:** the oracle compares outputs with Deno's `@std/csv`. The falsifier
  checks each law on about 100,000 generated inputs. A planted bug provides a
  control for the falsifier.
- **Mutation checks:** each law has a corresponding code edit that makes it
  false. The suite checks a counterexample and requires the targeted proof to
  fail.

Tests can expose bugs; they do not extend the scope of a proof.

The current twelve proofs pass both Bend 2.0.34's `--check-only` and the
BendTT kernel recheck (`bend --verdict PROOF.bend`). The automated suite runs
the kernel recheck wherever the kernel builds (not in CI). See the [toolchain notes](NOTES.md#the---verdict-caveat).

## Format details

These details matter when exact record preservation or RFC compatibility is
part of your application's contract.

### Relationship to RFC 4180

This is not a strict implementation of the
[RFC 4180 ABNF](https://www.rfc-editor.org/rfc/rfc4180#section-2).
Blank records follow the RFC's empty-field grammar. Accepting CR in unquoted
fields is an extension, not a rule required by the RFC.

- **Empty records:** the RFC defines `record = field *(COMMA field)` and
  `non-escaped = *TEXTDATA`. A field can therefore be empty, and an empty field
  can form a record. This parser returns no rows for empty input, and every blank
  line (LF or CRLF, including leading, trailing and consecutive ones) is a
  record containing one empty field, exactly as `""` is. Ending an unfinished
  record with a line end adds no extra row: `a` and `a\n` both give one row,
  while `a\n\n` gives `a` and a blank row. A CR that ends the input is a line
  ending, so `\r` alone is one blank row.
- **Line endings:** the RFC uses CRLF between records. This parser also accepts
  LF. It treats a final CR outside a quoted field as a line ending.
  Within an unquoted field, a CR not followed by LF is content. For example,
  `a\rb\r\n` becomes one field containing `a\rb`. The RFC's unquoted
  `TEXTDATA` excludes CR and LF.
- **Character repertoire and separators:** the RFC's ABNF specifies ASCII
  `TEXTDATA` and comma separators. This parser also accepts Unicode text and
  custom separators.

Inside a quoted field, CR and LF remain content, including the full CRLF pair.
That behavior follows the RFC's `escaped` production, which explicitly permits
both characters.

### Behavioral comparison with Deno's `@std/csv`

The test suite compares this parser with the Deno parser on 192,447
inputs. They agree on 180,085 of those inputs. The remaining 12,362 differ in
two reported classes: 11,910 differ only by blank records (this parser keeps a
blank line as a row of one empty field, the reference drops it), 332 differ only
by a CRLF inside a quoted field (this parser preserves the pair, the reference
normalizes it), and 120 differ by both. The blank-record class is accepted only
when the rows equal the reference's rows with `[""]` inserted at exactly the
blank lines found by an independent scan of the input; any other difference
fails the suite.

These are test results for that corpus, not a proof that the parsers agree on
all other inputs. The reference is not part of this repository: `scripts/fetch-reference.sh`
fetches Deno's `@std/csv` at one pinned commit into `reference/std`.

## Contributing

Building and verification need Bend exactly as in
`BEND_VERSION` (2.0.34), plus `bun` and `npx` on `PATH`. Run `bun install` first
to install the pinned `bend-emit@0.3.0` build dependency.

```sh
bun install --frozen-lockfile    # verification dependencies
sh scripts/fetch-reference.sh    # Deno's @std/csv at a pinned commit, for the oracle and benchmarks
sh scripts/build.sh              # core.bend -> dist/core.mjs + dist/core.d.mts
sh test.sh                       # builds the same way, then runs the full gate
```

`scripts/build.sh [source.bend] [outdir]` is the only build; `test.sh` and CI
both use it. Commit the regenerated `dist/` with the change to `core.bend`; CI
fails when the committed `dist/` differs from a fresh build.

The suite requires the Bend version in `BEND_VERSION` (currently 2.0.34).
With another version, it prints `SKIP` and exits successfully without running
the checks. A successful exit alone therefore does not mean verification ran.

## License

MIT. See [LICENSE](LICENSE).
