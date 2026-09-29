// The gate's check that a host reaches the parser through bridge.ts, and that
// the bridge refuses what it says it refuses.
//
//   bun check_bridge.ts

import { CsvParseError, parse } from "./bridge.ts";

let bad = 0;
function eq(what: string, got: unknown, want: unknown) {
  if (JSON.stringify(got) !== JSON.stringify(want)) {
    console.log(`FAIL ${what}: got ${JSON.stringify(got)}, want ${JSON.stringify(want)}`);
    bad += 1;
  }
}

eq("two fields", parse("a,b\r\n"), [["a", "b"]]);
eq("a quoted field holding the separator", parse('"a,b",c\r\n'), [["a,b", "c"]]);
eq("doubled quotes", parse('"say ""hi"""\r\n'), [['say "hi"']]);
eq("a trailing newline adds nothing", parse("a\r\n"), [["a"]]);
eq("a blank line is no record", parse("a\r\n\r\nb\r\n"), [["a"], ["b"]]);
eq("a CR inside a field is content", parse("a\rb\r\n"), [["a\rb"]]);
eq("a quoted empty field keeps its row", parse('""\r\n'), [[""]]);
eq("the empty input", parse(""), []);
eq("another separator", parse("a;b\r\n", { separator: ";" }), [["a", "b"]]);
eq("a byte-order mark is the host's", parse("\uFEFFa,b\r\n"), [["a", "b"]]);

let refused = false;
try {
  parse('a"b\r\n');
} catch (e) {
  refused = e instanceof CsvParseError;
}
eq("a bare quote is refused, as an error", refused, true);

let unreadable = false;
try {
  parse('"a\r\n');
} catch (e) {
  unreadable = e instanceof CsvParseError;
}
eq("an unclosed quote is refused", unreadable, true);

let separatorRefused = false;
try {
  parse("a\nb", { separator: "\n" });
} catch (e) {
  separatorRefused = e instanceof TypeError;
}
eq("a separator the parser would read itself is refused here", separatorRefused, true);

let longSeparatorRefused = false;
try {
  parse("a,,b", { separator: ",," });
} catch (e) {
  longSeparatorRefused = e instanceof TypeError;
}
eq("a separator of more than one character is refused", longSeparatorRefused, true);

console.log(bad === 0 ? "bridge: a host reaches the parser, and each refusal is an error" : `bridge: ${bad} checks failed`);
process.exit(bad === 0 ? 0 : 1);
