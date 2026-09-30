# Notes: how csv-abnf is built and checked

This file holds the internal material that the README leaves out. Nothing here
is needed to use the parser. It is moved from the earlier README, with two
corrections marked "Correction".

## The gate: `sh test.sh`

The gate has eight steps. Each can fail.

1. The core checks (`bend --check-only core.bend` prints `ALL PROOFS CHECK`), and no
   proof of it rests on unsafe code.
2. The core builds into a typed module in `dist/` (with `vendor/bend-emit`).
   `bend-emit` exits 0 even when Bend cannot compile the file, so the gate reads
   its log and not its exit code. Otherwise the oracle would measure a stale
   module.
3. A host reaches the parser through `bridge.ts` (`check_bridge.ts`), including
   the refusals the bridge owes a host: a separator the parser would read as
   itself.
4. The parser agrees with the reference (`oracle.ts`, Deno's `@std/csv` in
   `reference/std`) on every small input, about 190k in all (192,447). The one
   known difference class, a CRLF inside a quoted field, is reported and not
   hidden: 452 inputs.
5. Every law is falsified over about 100k inputs (`falsify.ts`, with
   `bend-falsify`). The falsifier itself is controlled: see "Harness traps".
6. Every law is proved (`bend --check-only PROOF.bend`).
7. Every law has a mutant (`check_mutants.ts`): one planted edit to `core.bend`
   that makes the law false at a named input. That law's own proof must fail where
   the table says.
8. The library stands alone: no `*.bend` file imports from outside the repository.
   The step greps only `*.bend` files, so this file cannot trip it.

`test.sh` also checks that `vendor/` is not empty, and skips itself (`SKIP`, exit
0) when the installed Bend is not the release in `BEND_VERSION`.

### The `--verdict` caveat

`bend --verdict` rechecks a proof with the BendTT kernel. The gate does not run
it. From Bend 2.0.34 the checker shares a graph that it has proved equal, and the
kernel has not caught up. The two can disagree on a proof that the checker
accepts. This is the toolchain's state, not this library's.

## Harness traps

Two traps in the checking harness shaped it.

- **The falsifier's planted bug.** A falsifier that finds nothing may be broken.
  Step 5 therefore runs the same sweep against a copy of the core with one planted
  bug (the `sed` line in `test.sh` drops the appended character:
  `String.append(txt, one(c))` becomes `txt`). The falsifier must refute the laws
  on that core. If the laws survive, the gate fails with "the falsifier caught
  nothing when the core was broken". The gate also checks that the planted line
  exists in `core.bend` and that the edit took effect.
- **The stale benchmark binary.** A table taken from a stale binary is wrong in a
  way that looks exactly like a table taken from a good one. `native/scale.ts`
  rebuilds `native/bench` when `core.bend` is newer than it, and prints when the
  binary it used was built.

## The falsifier's separator list

`falsify.ts` runs each law over these ten separators:

```
","  ";"  "\t"  " "  "\u00a3"  "\n"  "\r"  '"'  "a"  "b"
```

Two of them are letters that appear in the laws' own test inputs. A separator that
the input also uses as text is the case that caught `abnf_cr_inside_a_field_is_content`:
it is stated for every separator and was false for `a`. The falsifier is also what
put the hypotheses in the law table below.

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


## Measurement method

Two lanes: a native binary built by Bend's C backend, and the JavaScript module
that the emitter in `vendor/bend-emit` builds. Both are measured on the same
corpus, on a 14-core Apple machine with 36 GB of memory. The scripts are
`native/scale.ts` and `bench_js.ts`.

- Native: `bend native/bench.bend -o native/bench`. One run per size, timed by the
  benchmark itself. Peak resident set comes from macOS's `time -l`.
  `bun native/scale.ts <MB>` runs the native binary and the reference.
- JavaScript: `bun bench_js.ts`. One process per parse, three runs each.

Each table comes from one run of one script. Peak memory repeats closely. Timing
does not.

Throughput, native, from the same runs: 100 MB/s at 0.5 MB, 91 at 1 MB, 83 at
2 MB, 71 at 5 MB, 68 at 10 MB, 66 at 20 MB, 64 at 40 MB. The old README
attributed the taper to the cache and the allocator, not the walk. That is an
explanation. No measurement in the repository tests it. Memory is about 17 MB of process per MB of
input by 40 MB. On 36 GB, arithmetic puts the limit near two gigabytes of CSV.
That is arithmetic, not a measurement.

### Threads

The parse is one dependent chain, so the runtime has nothing to split.

| 5 MB, threads | time | peak RSS |
| --- | --- | --- |
| default | 70 ms | 87 MB |
| `--threads 10` | 71 ms | 87 MB |

`sh native/threads.sh <file>` repeats this on any file.

### Where the JavaScript lane's memory goes

At 10 MB, about 19 MB per MB of input is what the parse holds. With `bun:jsc`'s
heap statistics, the live heap after a forced collection is 193 MB, and the native
lane needs 172 MB for the same corpus. The rest is the text of each field, built
a character at a time, and the input itself: what building a string in JavaScript
costs. Earlier measurements were several times heavier, because the emitter
sliced a character off the front of the input once per character. It now carries
such a string as a pair of the string and an index into it, and materialises
nothing.

Bend's JavaScript lane does impose a size ceiling on other shapes: a self-call in
a field that is not the last one becomes a JavaScript recursion, one frame per
character. The walk in this parser compiles to a loop, so it has no such ceiling.
Correction: the earlier README quoted a 10 MB run of 582,543 rows, 656 ms, 690 MB
through `bridge.ts`. Those figures are older than the table in the README (265 ms,
400 MB at 10 MB) and are not repeated there.

## What a checkout carries

`git clone --recurse-submodules` (or `git submodule update --init` after a plain
clone) fetches `vendor/`. `bun install` fetches the dev dependency.

| | needs |
| --- | --- |
| `core.bend` | nothing: it imports `Base` alone |
| `LAWS.bend`, `PROOF.bend` | `vendor/bendlib/packages/bend-mathlib` (the list and string lemmas), a submodule |
| `bridge.ts` | the module in `dist/`, which the gate builds with `vendor/bend-emit` (a submodule) |
| `oracle.ts` | `reference/std` (Deno's `@std/csv`, MIT), a plain directory |
| `falsify.ts`, `check_mutants.ts` | `bend-falsify`, a dev dependency pinned in `package.json` |
| `native/` | nothing: `bend` builds it |

`reference/std` is third-party code, copied unchanged. Its `PIN` file names the
commit it was taken at.

## Publishing

`core.bend` imports `Base` alone, so it publishes on its own:

```sh
bend login                                   # once
bend core.bend --publish csv-abnf@0.1.0.0
```

Correction: the earlier README wrote `csv-abnf@0.1.0`. Bend rejects it: the
version needs four numbers. The command uploads the file with everything it
imports, and it prints the import line. A publish is public and permanent. A
`LICENSE` file beside the entry decides the license. Without one, a package is
MIT-0, and adding one later changes the hash, so it would be a new version. The
proofs need not ship with the claim: a law left open in one file can be filled in
another, which is how `LAWS.bend` and `PROOF.bend` are split. If the proofs are
published too, they drag the vendored mathlib along: 452 KB of lemmas the parser
does not need. Nothing has been published.

An unnamed publish gives a content-hash import (`import 0x<hash>/core.bend as C`).

## Sizes

`core.bend` is 174 lines. `LAWS.bend` is 125. `PROOF.bend` is 577, one section
per law.
