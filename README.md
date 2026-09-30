# csv-abnf

RFC 4180 CSV parsing in Bend, written in the shape of the grammar it implements,
with a machine-checked proof for each of its laws. Nine laws, all proved; one
entry point for Bend, one for a JavaScript or TypeScript host.

The parser is one walk over the input -- the mode it is in and what it has read
so far are passed as arguments -- so the rules of the grammar are the cases of
that walk, and each rule is a law. It is tested against Deno's `@std/csv` (vendored in
`reference/std`) as an oracle, but an oracle can find a bug and proves nothing;
the proofs are what settle the laws.

Clone with `git clone --recurse-submodules`: the proofs and the module builder
live in submodules under `vendor/` (see "What a checkout carries").

`sh test.sh` is the gate: eight steps, each of which can fail.

## Using it from Bend

A Bend file imports it and calls one of two functions:

```bend
import Base
import ./core.bend as C

# C.parse(s) is the comma instance; C.parse_sep(sep, s) takes the separator's
# code point. Both answer C.Parsed{rows} or C.Rejected{}:

def fields_of(line: String) -> String:
  match C.parse(line):
    case C.Parsed{rows}:
      "read"
    case C.Rejected{}:
      "not a file of the format"
```

The answer carries no position and no reason: this parser has neither, and that
is deliberate (the shape below says why). A caller that needs to know *where* a
defect is wants a parser that reports positions, such as Deno's `@std/csv`.

Once published (see below), the same file comes from the hub by content hash,
and nothing else changes:

```bend
import 0x<hash>/core.bend as C
```

## Using it from TypeScript or JavaScript

A host gets the parser as an ES module, and it reads at any size; the numbers,
and what it costs, are under "The JavaScript lane" below.

Two ways, and the difference matters:

```ts
// The bridge a host uses: a byte-order mark stripped, the separator checked,
// a refusal as an error.
import { parse, CsvParseError } from "./bridge.ts";

const rows = parse("a,b\r\n");                 // [["a", "b"]]
const more = parse(text, { separator: ";" });  // or throw CsvParseError
```

```sh
# Or the module on its own, built by the toolchain:
bend core.bend -o core.mjs
```

`bridge.ts` strips a byte-order mark (the host's job) and refuses a separator the
parser would read as itself before comparing it -- LF, CR, the quote, or more
than one character. That check lives in the bridge and not in the core on
purpose: the core reads those characters as themselves, so a host passing one
would get the reading of a file whose separator never appears. Adding the check
to the core would be a new claim, and here every claim has a law.

There is no input-size ceiling on this path: the walk compiles to a loop in the
emitted module, so a host can hand it a whole file. The largest measured is 10 MB
-- 582,543 rows, 656 ms, 690 MB of process, through `bridge.ts`. Bend's JavaScript
lane does impose such a ceiling on other shapes: a self-call in a field that is
not the last one becomes a JavaScript recursion, one frame per character. For the
fastest reading of bulk input, build the parser natively
(`bend native/bench.bend -o native/bench`).

## What is proved, and how

| | |
| --- | --- |
| the laws | nine, in `LAWS.bend`; `bend --check-only PROOF.bend` says `ALL PROOFS CHECK` |
| the parser | `core.bend`, 174 lines; `bend --check-only core.bend` says the same |
| the proofs | `PROOF.bend`, 577 lines, one section per law |

The gate checks, in order: the core; the module the toolchain builds; the bridge
a host uses; the parser against the reference over ~190k inputs; every law
falsified over ~100k inputs with a controlled falsifier; every law proved; a
mutant for every law that makes it false and breaks its own proof; and that
nothing here imports from outside the repository.

Three kinds of evidence, kept apart on purpose:

- **proved**: the nine laws, by bend's checker. (`--verdict`, the BendTT kernel,
  is not run: from Bend 2.0.34 the checker shares a graph it has proved equal and
  the kernel has not caught up, so the two can disagree on a proof the checker
  accepts. This is the toolchain's state, not this library's.)
- **tested**: the oracle against Deno's `@std/csv` (192,447 inputs, one
  difference class counted rather than hidden), the falsifier, the mutants.
- **measured**: time and memory, below.

## The grammar

RFC 4180 section 2, transcribed; every line of it is commented onto the def that
implements it.

```
file        = [header CRLF] record *(CRLF record) [CRLF]
header      = name *(COMMA name)
name        = field
record      = field *(COMMA field)
field       = (escaped / non-escaped)
escaped     = DQUOTE *(TEXTDATA / COMMA / CR / LF / 2DQUOTE) DQUOTE
non-escaped = *TEXTDATA
COMMA       = %x2C          CR = %x0D        DQUOTE = %x22
LF          = %x0A          CRLF = CR LF
TEXTDATA    = %x20-21 / %x23-2B / %x2D-7E
```

Three refinements, each measured against the reference and each what a first
guess gets wrong:

- **a blank line is not a record.** `record` as written can be an empty field, so
  the grammar over-generates here; the reading drops it. It falls out of the step:
  a line end met before any field has begun closes nothing, while `""` has already
  begun one, so it is a record holding one empty field.
- **a CR the line does not end at is content.** CR is not TEXTDATA, but `a\rb` is
  one field. A record ends at LF, at CRLF, or at a CR the input ends on.
- **a trailing newline adds no record.**

## The shape, and why it is this shape

`bend` rejects a self-call unless, reading the arguments left to right, one
shrinks and everything before it is passed unchanged, and it never reads a
helper's result as a subterm. So "peel a piece with a helper, then recurse on
what it left" cannot be written, and a pass that consumes to a variable depth is
one walk whose self-call takes a pattern-bound tail. What that leaves:

- **one walk for the whole grammar** -- a record ending, a field ending and the
  field's own text all decided at the same character -- with the input as the first
  parameter, the mode it is in second, and what has been read in the rest;
- **a mode for each position in the grammar** -- the start of a field, a bare
  field, an escaped one, just after a quote, and three more that hold a CR back
  until the next character says whether it ended the line or was content.

Nothing recurses on a computed value, and nothing matches one: the modes are
parameters and a character's kind is a constructor.

The law that makes the point is `abnf_doubled_quote_is_one_quote`: RFC 4180's
`2DQUOTE` alternative -- two quotes in the text are one quote in the field -- is
a rule that tests alone tend to leave to chance, and here it is a law.

The state is the mode, the text of the field being read, the fields of the record
being read, and the rows finished, with no positions anywhere. A separator closes
a field, a line end closes a record, and the CR is held in a mode of its own.

Fusing the walk is also what made the proofs smaller. The shape before this one
had a walk per level of the grammar with a map between them, and a proof about a
list has to reason about the list it is handed, so it needed mirrored functions
-- `tx`, `push`, `add_push`, `one_cons` -- whose only job was to undo the order a
layer had accumulated in. With one walk there is nothing to mirror: each mode's
induction hypothesis says what the walk does to the input that is left, and two
mathlib facts about `String.append` close the steps. `PROOF.bend` went from 951
lines to 577 while proving the same nine laws.

## The laws

Nine, in `LAWS.bend`. Each is falsified over ~100k inputs across ten separators
before it is proved, and each has a mutant that makes it false and breaks its own
proof.

| law | what it says | hypotheses |
| --- | --- | --- |
| `abnf_empty_input_is_no_record` | the empty input holds no record | none |
| `abnf_trailing_newline_adds_nothing` | a newline at the very end changes nothing | none |
| `abnf_blank_line_adds_nothing` | an empty line produces no record | no quote in the input |
| `abnf_clean_input_is_one_field` | a clean input is one record of one field, itself; empty means no record | `Clean(sep, s)` |
| `abnf_separator_makes_two_fields` | two clean records joined by the separator are two fields | `Clean`, separator is not LF or CR |
| `abnf_quoted_field_is_its_content` | a quoted field's content is that content | no quote in it, separator is not the quote |
| `abnf_doubled_quote_is_one_quote` | `"a""b"` is the field `a"b` | separator is not the quote |
| `abnf_lone_empty_field_keeps_its_row` | a quoted empty field is a field, so the row survives | separator is not the quote |
| `abnf_cr_inside_a_field_is_content` | `a\rb\r\n` is one record `a\rb` | separator is not `a` or `b` |

The hypotheses are not decoration, and the falsifier is what put them there:
`abnf_lone_empty_field_keeps_its_row` is false for the separator `"`, and
`abnf_cr_inside_a_field_is_content` is false for the separator `a` or `b` -- the
input's own letters. The falsifier's separator set therefore includes letters.

## Speed, measured

Two lanes, and they are not the same thing: a native binary built by Bend's C
backend, and the JavaScript module the toolchain emits. Both are measured on the
same corpus -- three record shapes (quoted commas and doubled quotes; a quoted
newline with empty fields; an empty quoted field), repeated to the target size,
CRLF line ends, never a CRLF inside a quoted field -- on a 14-core Apple machine
with 36 GB of memory. The two scripts are `native/scale.ts` and `bench_js.ts`.

Each table comes from one run of one script, and the runs are minutes apart at
best. Peak memory repeats closely; timing does not. The same 10 MB parse in the
JavaScript lane has come out at 437 ms and 450 ms on consecutive runs, and a
machine under other load moves it further. Treat the time columns as a factor,
not a figure.

### The native lane

`bend native/bench.bend -o native/bench`. One run per size, timed by the
benchmark itself, peak resident set from macOS's `time -l`. `native/scale.ts`
rebuilds that binary when `core.bend` is newer than it, and prints when the binary
it used was built -- a table taken from a stale binary is wrong in a way that
looks exactly like a table taken from a good one.

| input | time | throughput | peak RSS |
| --- | --- | --- | --- |
| 0.5 MB | 5 ms | 100 MB/s | 11 MB |
| 1 MB | 11 ms | 91 MB/s | 19 MB |
| 2 MB | 24 ms | 83 MB/s | 36 MB |
| 5 MB | 70 ms | 71 MB/s | 87 MB |
| 10 MB | 147 ms | 68 MB/s | 172 MB |
| 20 MB | 304 ms | 66 MB/s | 342 MB |
| 40 MB | 623 ms | 64 MB/s | 682 MB |

Time is linear in the input and memory is linear behind it, at about 17 MB of
process per MB of input by 40 MB: the input and the result, because the walk holds
nothing per character. Nothing runs out of stack either -- 40 million characters,
1.7 million rows. Throughput tapers with size, from 100 MB/s on half a megabyte to
64 MB/s on forty; that is the cache and the allocator, not the walk. On 36 GB the
arithmetic puts the limit near two gigabytes of CSV. It is arithmetic, not a
measurement, and the largest input measured is 40 MB.

Against the reference, on the same corpus and by the same method
(`bun native/scale.ts <MB>` runs both):

| input | this parser (native) | Deno's `@std/csv` (in bun) |
| --- | --- | --- |
| 0.1 MB | 2 ms, 4 MB | 4.4 ms, 26 MB |
| 1 MB | 11 ms, 19 MB | 33 ms, 50 MB |
| 10 MB | 147 ms, 172 MB | 291 ms, 284 MB |

So it is about twice as fast as the reference at every size from 0.1 MB up, and
lighter than it at every size too: 172 MB against 284 MB at 10 MB, and 682 MB
against 884 MB at 40 MB, which is 17 MB per MB of input against 22. The reference
is a JavaScript parser and this is a native binary, so read the comparison as what
a host gets from each, not as one language being faster than another.

Threads do not enter into it: the parse is one dependent chain, so there is
nothing for the runtime to split.

| 5 MB, threads | time | peak RSS |
| --- | --- | --- |
| default | 70 ms | 87 MB |
| `--threads 10` | 71 ms | 87 MB |

`sh native/threads.sh <file>` repeats that on any file.

### The JavaScript lane

The module `bend core.bend -o core.mjs` emits -- what `bridge.ts` calls -- against
Deno's `@std/csv`, one process per parse, three runs each, time and peak resident
set (`bun bench_js.ts`):

| input | this parser | Deno's `@std/csv` |
| --- | --- | --- |
| 1 KB | 1 ms, 19 MB | 1 ms, 15 MB |
| 4 KB | 2 ms, 19 MB | 1 ms, 17 MB |
| 16 KB | 2 ms, 24 MB | 2 ms, 20 MB |
| 64 KB | 5 ms, 31 MB | 3 ms, 24 MB |
| 256 KB | 15 ms, 43 MB | 9 ms, 34 MB |
| 1 MB | 58 ms, 110 MB | 36 ms, 50 MB |
| 10 MB | 437 ms, 747 MB | 292 ms, 286 MB |

Both read every size, and the rows agree at every one of them. The peak includes
the runtime's own footprint (about 15 MB), so the small sizes say nothing about
memory. What the larger ones say is that this lane is about 1.5x slower than
Deno's and about 2.6x heavier -- 75 MB of process per MB of input against 29 --
but those two numbers are not the same kind of thing. About 19 MB per MB is what
the parse holds: with `bun:jsc`'s heap statistics, the live heap after a forced
collection is 193 MB at 10 MB, and the native lane needs 172 MB for the same
corpus. The rest is churn -- one sliced string and one rope node per character --
and an emitter can still take it out, by walking the input by index instead of
slicing a character off the front. That is bend-emit's work, not the core's. What
the lane buys is the proofs: Deno's parser has none, and a host needs no build step
of its own, Bend's ES module being the whole parser.

## What a checkout carries

`git clone --recurse-submodules` (or `git submodule update --init` after a plain
clone) fetches `vendor/`; `bun install` fetches the dev dependency. `test.sh`
says so if `vendor/` is empty.

| | needs |
| --- | --- |
| `core.bend` | nothing: it imports `Base` alone |
| `LAWS.bend`, `PROOF.bend` | `vendor/bendlib/packages/bend-mathlib` (the list and string lemmas), a submodule |
| `bridge.ts` | the module in `dist/`, which the gate builds with `vendor/bend-emit` (a submodule) |
| `oracle.ts` | `reference/std` (Deno's `@std/csv`, MIT), a plain directory |
| `falsify.ts`, `check_mutants.ts` | `bend-falsify`, a dev dependency pinned in `package.json` |
| `native/` | nothing: `bend` builds it |

`reference/std` is third-party code, copied unchanged; its `PIN` file names the
commit it was taken at. `BEND_VERSION` names the Bend release the gate expects;
with another release installed, `sh test.sh` prints `SKIP` and exits 0.

## Publishing to Bend Hub

`core.bend` imports `Base` alone, so it publishes on its own:

```sh
bend login                        # once
bend core.bend --publish csv-abnf@0.1.0
```

That uploads the file with everything it imports and prints the import line
(`import 0x<hash>/core.bend as C`). Two things to know: **a publish is public and
permanent**, and a `LICENSE` file beside the entry decides the license (without
one a package is MIT-0, and adding one later changes the hash, so it would be a
new version). The proofs need not ship with the claim -- a law left open in one
file can be filled in another, which is how `LAWS.bend` and `PROOF.bend` are
split. If they are published too they drag the vendored mathlib along: 452 KB of
lemmas the parser does not need.

## License

MIT. See `LICENSE`.
