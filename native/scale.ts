// The native lane, beside Deno's `@std/csv` on the same corpus, one size per
// run.
//
//   bun native/scale.ts 10      ten megabytes
//
// One size per invocation on purpose: this parser holds a token per character,
// so a big file is a memory event, and a memory event takes the shell with it.
//
// The two parsers read the same text: the corpus is generated here for the
// native binary (which reads a file) and by the same rule inside
// `bench_js.ts --one ref`, which the reference runs in. One process per parse,
// three runs each, `/usr/bin/time -l` for the peak; the peak of the reference
// includes bun's own footprint, and the native one includes almost nothing.
//
// Timings are printed, not asserted.

import { $ } from "bun";

const dir = import.meta.dir;
const root = `${dir}/..`;
const mb = Number(process.argv[2] ?? "1");
// No CRLF inside a quoted field: the class where the two read differently
// (the reference normalizes it), and the reason the comparison excludes it.
const R = ['alpha,"be,ta",42,"say ""hi"""\r\n', '"multi\nline",,x\r\n', 'plain,words here,"",end\r\n'];

if (!(await Bun.file(`${dir}/bench`).exists())) await $`bend ${dir}/bench.bend -o ${dir}/bench`.quiet();

// The corpus is generated to a whole number of kilobytes, because that is what
// the reference worker is told, and both must build the identical string --
// rounding here once put the two parsers on inputs 16 rows apart.
const kb = Math.round(mb * 1024);
const rows: string[] = [];
let len = 0;
for (let i = 0; len < kb * 1024; i++) {
  const r = R[i % R.length];
  rows.push(r);
  len += r.length;
}
const file = `/tmp/csv-abnf-bench-${mb}mb.csv`;
await Bun.write(file, rows.join(""));

async function once(cmd: string[]): Promise<{ out: string; peak: number }> {
  const p = Bun.spawn(["/usr/bin/time", "-l", ...cmd], { stdout: "pipe", stderr: "pipe" });
  const [out, err] = await Promise.all([new Response(p.stdout).text(), new Response(p.stderr).text()]);
  await p.exited;
  const peak = Number(/(\d+)\s+maximum resident set size/.exec(err)?.[1] ?? 0) / 1024 / 1024;
  return { out: out.trim(), peak };
}

async function best(cmd: string[]) {
  const times: number[] = [];
  let peak = 0;
  let out = "";
  for (let i = 0; i < 3; i++) {
    const r = await once(cmd);
    out = r.out;
    peak = Math.max(peak, r.peak);
    // The native bench prints "ms 123"; the reference worker prints the number
    // alone on its first line.
    const ms = /ms (\d+)/.exec(r.out)?.[1] ?? r.out.split("\n")[0];
    const n = Number(ms);
    if (Number.isFinite(n)) times.push(n);
  }
  return { ms: times.length ? Math.min(...times) : NaN, peak, out };
}

const mine = await best([`${dir}/bench`, file]);
const ref = await best(["bun", `${root}/bench_js.ts`, "--one", "ref", String(kb)]);

console.log(`${mb} MB input (${(len / 1024 / 1024).toFixed(2)} MB actually), ${rows.length} lines`);
console.log(`  this parser (native)     ${mine.ms} ms, peak ${mine.peak.toFixed(0)} MB   ${mine.out.split("\n")[0]}`);
console.log(`  Deno's @std/csv (bun)    ${ref.out.split("\n")[0]} ms, peak ${ref.peak.toFixed(0)} MB   ${ref.out.split("\n")[1]} rows`);
