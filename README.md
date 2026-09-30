# csv-abnf

An RFC 4180 CSV parser written in Bend. Each of its nine laws has a
machine-checked proof. You can use it from Bend, and from a JavaScript or
TypeScript host.

## What you get

**Laws, not luck.** Tests tend to leave some RFC 4180 rules to chance. Here each
of those rules is a law with a proof. For example, `abnf_doubled_quote_is_one_quote`
is the RFC's `2DQUOTE` rule: two quotes inside a quoted field are one quote in
the field's value. The nine laws are in `LAWS.bend`. The proofs are in
`PROOF.bend`. `bend --check-only PROOF.bend` prints `ALL PROOFS CHECK`.

**Speed and size, measured.**

- Native (a binary built by Bend's C backend): about twice as fast as Deno's
  `@std/csv`, and lighter than it at every size measured, 0.1 MB to 40 MB.
- JavaScript (the module Bend emits): faster than Deno's at 10 MB (265 ms against
  297 ms), and about 1.4x heavier in memory.

The tables are below.

## Three kinds of evidence

| Kind | What it covers | How |
| --- | --- | --- |
| Proved | The nine laws | Bend's checker |
| Tested | The parser against Deno's `@std/csv` on 192,447 inputs; each law against about 100,000 generated inputs; one planted edit ("mutant") per law | `sh test.sh` |
| Measured | Time and peak memory | `native/scale.ts`, `bench_js.ts` |

A test can find a bug. It cannot prove that there is none. The proofs settle the
laws. The tests and the measurements cover the rest. The proofs state what the
parser does on the inputs each law names. They do not say that the parser
agrees with every other CSV parser.

The proof checker used is `bend --check-only`. The stricter `bend --verdict`
recheck is not run. From Bend 2.0.34 the two can disagree on a proof, because
the kernel has not caught up with the checker. See `NOTES.md`.

## Compared with Deno's `@std/csv`

| | csv-abnf | Deno `@std/csv` |
| --- | --- | --- |
| Proofs | 9 laws, machine-checked | none |
| Native, 10 MB | 147 ms, 172 MB | 291 ms, 284 MB (run in bun) |
| Native, 1 MB | 11 ms, 19 MB | 33 ms, 50 MB |
| Native, 0.1 MB | 2 ms, 4 MB | 4.4 ms, 26 MB |
| JavaScript, 10 MB | 265 ms, 400 MB | 297 ms, 286 MB |
| Positions and reasons on error | no | yes |
| CRLF inside a quoted field | read as content | see below |
| Runs in a browser | a JavaScript host uses the emitted module | yes |
| Language | Bend | TypeScript |

Differences you need to know:

- **No positions, no reasons.** A refusal says only that the input is not a file
  of the format. This is deliberate: the parser keeps no position, and each law
  is stated on the rows and on whether a file was read at all. If you must tell
  a user where a defect is, use a parser that reports positions, such as Deno's.
- **CRLF inside a quoted field.** This parser reads a CRLF inside a quoted field
  as content. The two parsers differ on such inputs. The oracle counts them and
  does not hide them: 452 of the 192,447 compared inputs. On every other input
  they agree.
- **Bend module, not a browser library.** Deno's parser is a TypeScript module.
  This one is a Bend module. A JavaScript host takes the module that Bend emits
  (`dist/core.mjs`, built by `sh test.sh` with `vendor/bend-emit`). Or it builds the
  native binary (`bend native/bench.bend -o native/bench`).

Two notes on the numbers:

- Timing does not repeat between runs. The same 10 MB JavaScript parse has come
  out at 437 ms and 450 ms on consecutive runs in an earlier measurement. Read
  the time columns as a factor, not as a figure. Peak memory repeats closely.
- The native comparison is a binary against a JavaScript parser. Read it as what
  a host gets from each, not as one language being faster than another.

All numbers come from one 14-core Apple machine with 36 GB of memory. The
corpus has three record shapes (quoted commas and doubled quotes; a quoted
newline with empty fields; an empty quoted field), CRLF line ends, and never a
CRLF inside a quoted field. The largest input measured is 40 MB (native) and
10 MB (JavaScript).

### Native

| input | this parser | Deno's `@std/csv` (in bun) |
| --- | --- | --- |
| 0.1 MB | 2 ms, 4 MB | 4.4 ms, 26 MB |
| 1 MB | 11 ms, 19 MB | 33 ms, 50 MB |
| 10 MB | 147 ms, 172 MB | 291 ms, 284 MB |

Native alone, up to 40 MB:

| input | time | peak memory |
| --- | --- | --- |
| 0.5 MB | 5 ms | 11 MB |
| 1 MB | 11 ms | 19 MB |
| 2 MB | 24 ms | 36 MB |
| 5 MB | 70 ms | 87 MB |
| 10 MB | 147 ms | 172 MB |
| 20 MB | 304 ms | 342 MB |
| 40 MB | 623 ms | 682 MB |

Time is linear in the input size. Memory is about 17 MB per MB of input at 40 MB,
against 22 MB per MB for Deno's parser. Nothing runs out of stack: the 40 MB
input has 1.7 million rows.

### JavaScript

The emitted module against Deno's `@std/csv`. One process per parse, three runs
each.

| input | this parser | Deno's `@std/csv` |
| --- | --- | --- |
| 1 KB | 1 ms, 19 MB | 1 ms, 15 MB |
| 16 KB | 2 ms, 22 MB | 2 ms, 20 MB |
| 256 KB | 10 ms, 35 MB | 9 ms, 34 MB |
| 1 MB | 36 ms, 92 MB | 36 ms, 50 MB |
| 10 MB | 265 ms, 400 MB | 297 ms, 286 MB |

The rows agree with Deno's at every size. The peak includes the runtime's own
footprint (about 15 MB), so the small sizes say nothing about memory. At 10 MB
this parser uses about 40 MB of process per MB of input. Deno's uses about 29.

## Use it from Bend

Get the source with `git clone --recurse-submodules`. The package is **not yet on
Bend Hub**. Until it is, import the file from your clone:

```bend
import Base
import ./core.bend as C

# C.parse(s) reads a comma-separated file.
# C.parse_sep(sep, s) takes the separator as a code point (59 is ";").
# Both answer C.Parsed{rows} or C.Rejected{}.

def describe(r: C.Ans) -> String:
  match r:
    case C.Parsed{rows}:
      "read " ++ Nat.show(List.length(&2, List<&2, String>, rows)) ++ " rows"
    case C.Rejected{}:
      "not a file of the format"

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(describe(C.parse("a,b\r\nc,d\r\n")))     # read 2 rows
    IO.print(describe(C.parse_sep(59, "a;b\r\n")))    # read 1 rows
    IO.print(describe(C.parse("a,\"b")))              # not a file of the format
```

Save this beside `core.bend` and run `bend file.bend`. Bend does not let you
`match` on a call directly, so the answer goes through a `def` (`describe`).

### After publication

The publish form is a named one. The version needs **four** numbers. Bend
rejects `@0.1.0` with "at four numbers like 1.0.0.0".

```sh
bend login                                   # once
bend core.bend --publish csv-abnf@0.1.0.0
```

A published package is imported like this:

```bend
import csv-abnf@0.1.0.0/core.bend as C
```

Nothing has been published. A publish is public and permanent. A `LICENSE` file
beside the entry decides the license.

## Use it from TypeScript or JavaScript

Use the bridge, `bridge.ts`. It calls the emitted module in `dist/`. Build
`dist/` with `sh test.sh`, or with
`bun ./vendor/bend-emit/src/emit.ts core.bend dist`.

```ts
import { parse, CsvParseError } from "./bridge.ts";

// A comma-separated file. The byte-order mark is stripped.
const rows = parse("\uFEFFa,b\r\nc,\"d\"\"e\"\r\n");
// [["a", "b"], ["c", "d\"e"]]

// Another separator.
const semi = parse("a;b\n", { separator: ";" });
// [["a", "b"]]

// A refusal is an error.
try {
  parse("a,\"b");                      // a quote that never closes
} catch (e) {
  if (e instanceof CsvParseError) console.log("not a file of the format");
  else throw e;
}
```

What the bridge does that the bare module does not:

- **It strips a byte-order mark** (U+FEFF) at the start of the text. That is the
  host's job, not the parser's.
- **It refuses a separator that the parser would read as itself.** These are LF, CR,
  the quote, and any string that is not exactly one character. The bridge throws
  a `TypeError` for them.

The check is in the bridge and not in the core. The core reads LF, CR and the
quote as themselves before it compares them with the separator. A file read with
one of them as separator would have a separator that never appears. The
core's laws say so in their hypotheses. Adding the check to the core would add a
claim, and each claim in the core needs a law.

`bend core.bend -o core.mjs` builds the module alone. Its answer is Bend data
(`{ $: "Parsed", rows }`, with lists as `Con`/`Nil` cells), not arrays. Use the
bridge if you want arrays.

## API

**Bend** (`core.bend`)

| Function | Meaning |
| --- | --- |
| `parse(s)` | Parse `s` with a comma as separator |
| `parse_sep(sep, s)` | Parse `s` with the code point `sep` as separator |

Each returns `Parsed{rows}`, where `rows` is a list of records and each record is a
list of strings, or `Rejected{}`.

**TypeScript** (`bridge.ts`)

| Item | Meaning |
| --- | --- |
| `parse(text, { separator })` | Returns `string[][]`. `separator` is one character, default `","`. |
| `CsvParseError` | Thrown when the input is not a file of the format |

**What the answer does not carry:** a position or a reason. A refusal is one bit.
The parser is one walk that keeps no position, and the laws are stated on the rows
and on whether a file was read. A caller that needs a position needs a different
parser.

RFC 4180 details this parser follows: a blank line is not a record; a CR that
does not end a line is content; a trailing newline adds no record.

## Requirements

- Bend 2.0.34 (`BEND_VERSION`). With another release, `sh test.sh` prints `SKIP`
  and exits 0.
- `bun`, for the bridge, the oracle and the gate.
- The submodules under `vendor/` (`git submodule update --init`). `core.bend`
  itself needs only `Base`.
- `reference/std` is Deno's `@std/csv` (MIT), copied unchanged as the oracle.

`sh test.sh` is the gate. It checks the core, the emitted module, the bridge, the
oracle, the falsifier, the proofs and the mutants.

## License

MIT. See `LICENSE`.

Internals (the gate, how the proofs are built, the harness traps, the commands):
see [NOTES.md](NOTES.md).
