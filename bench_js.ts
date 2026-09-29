// The JavaScript lane: this parser's emitted module against Deno's `@std/csv`,
// on the same corpus, time and peak memory, at sizes doubling from 1 KB to
// 10 MB.
//
//   bun bench_js.ts                       the table
//   bun bench_js.ts --one mine 256        one parse in this process (internal)
//
// Each parse runs in a FRESH process, wrapped in `/usr/bin/time -l`, so the
// peak resident set is the real peak rather than what the heap happens to hold
// when the parse returns. The time is the parse alone, taken inside that
// process; the peak includes the runtime's own footprint (about 35 MB), which
// is why a size below ~64 KB has almost nothing to say about memory.
//
// The two lanes differ in cost, not in what they can read: this one conses a
// token per character and reads the input three times.

import { $ } from "bun";

const R = ['alpha,"be,ta",42,"say ""hi"""\r\n', '"multi\nline",,x\r\n', 'plain,words here,"",end\r\n'];
function corpus(kb: number): string {
  const parts: string[] = [];
  let len = 0;
  for (let i = 0; len < kb * 1024; i++) {
    const r = R[i % R.length];
    parts.push(r);
    len += r.length;
  }
  return parts.join("");
}

// ---- worker: one parse, one process ----
if (process.argv[2] === "--one") {
  const which = process.argv[3];
  const text = corpus(Number(process.argv[4] ?? "16"));
  const flat = (xs: any): any[] => {
    const out: any[] = [];
    for (let x = xs; x.$ === "Con"; x = x.tail) out.push(x.head);
    return out;
  };
  let rows: number;
  const t0 = performance.now();
  if (which === "mine") {
    const mine: any = await import("./dist/core.mjs");
    const r = mine.parse_sep(44, text);
    rows = r.$ === "Rejected" ? -1 : flat(r.rows).length;
  } else {
    const { parse } = await import("./reference/std/parse.ts");
    rows = parse(text).length;
  }
  console.log((performance.now() - t0).toFixed(1));
  console.log(rows);
  process.exit(0);
}

// ---- driver: fresh process per (parser, size), three runs each ----
const SIZES = [1, 4, 16, 64, 256, 1024, 10240];
const REPS = 3;

async function run(which: string, kb: number) {
  const times: number[] = [];
  const peaks: number[] = [];
  let rows = -1;
  for (let i = 0; i < REPS; i++) {
    const proc = Bun.spawn(["/usr/bin/time", "-l", "bun", import.meta.path, "--one", which, String(kb)], {
      stdout: "pipe",
      stderr: "pipe",
    });
    const [out, err] = await Promise.all([new Response(proc.stdout).text(), new Response(proc.stderr).text()]);
    await proc.exited;
    const lines = out.trim().split("\n");
    times.push(Number(lines[0]));
    rows = Number(lines[1] ?? rows);
    peaks.push(Number(/(\d+)\s+maximum resident set size/.exec(err)?.[1] ?? 0) / 1024 / 1024);
  }
  return { ms: Math.min(...times), mb: Math.max(...peaks), rows };
}

console.log("size      this parser                 Deno's @std/csv             rows");
for (const kb of SIZES) {
  const mine = await run("mine", kb);
  const ref = await run("ref", kb);
  const cell = (r: Awaited<ReturnType<typeof run>>) => `${r.ms.toFixed(0)} ms, ${r.mb.toFixed(0)} MB`;
  const ok = mine.rows === ref.rows ? "same" : "DIFFERENT";
  console.log(`${String(kb >= 1024 ? kb / 1024 + " MB" : kb + " KB").padEnd(9)} ${cell(mine).padEnd(28)} ${cell(ref).padEnd(28)} ${ok}`);
}
