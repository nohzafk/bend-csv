// csv-abnf's mutants: for each law, a change to core.bend that makes it false,
// the literals at which it is false, and the def its proof must fail in.
// The harness is bend-falsify; test.sh runs this.
//
// `from` is ONE whole line of core.bend (the harness replaces lines, not text),
// with `nth` when that line occurs more than once.
//
// A premise binder takes its evidence as a literal: Clean and NoQuote reduce on
// a literal string, so a character's facts are `{==}` and the empty tail is
// `Unit{}`.

import { type Mutant, runMutants } from "bend-falsify";

const CLEAN1 = "({==}, {==}, {==}, {==}, Unit{})"; // Clean of one ordinary character
const NOQUOTE1 = "({==}, Unit{})"; // NoQuote of one character that is not a quote

const MUTANTS: Mutant[] = [
  {
    law: "abnf_empty_input_is_no_record",
    section: "abnf_empty_input_is_no_record",
    from: "      done",
    to: "      whole(cur, done)",
    why: "an empty line counts as a record, so the empty input holds one empty record",
    failsIn: "Laws.abnf_empty_input_is_no_record",
    at: { sep: "44" },
  },
  {
    law: "abnf_trailing_newline_adds_nothing",
    section: "abnf_trailing_newline_adds_nothing",
    from: "      recs(t, RRec{}, TNil{}, add_rec(cur, done))",
    nth: 1,
    to: "      recs(t, RRec{}, TCon{KLf{}, cur}, done)",
    why: "a newline is kept as content and closes no record, so a trailing one changes the answer",
    // It fails in the blank-line walk, which this proof stands on: the same LF
    // case is what both of them reason about.
    failsIn: "blank_walk",
    // The walk lemmas it stands on live in these other sections.
    with: ["abnf_clean_input_is_one_field", "abnf_separator_makes_two_fields", "abnf_quoted_field_is_its_content", "abnf_blank_line_adds_nothing"],
    at: { sep: "44", s: '"a"' },
  },
  {
    law: "abnf_blank_line_adds_nothing",
    section: "abnf_blank_line_adds_nothing",
    from: "      done",
    to: "      whole(cur, done)",
    why: "an empty line counts as a record, so inserting one adds a row",
    failsIn: "blank_walk",
    with: ["abnf_quoted_field_is_its_content"],
    at: { sep: "44", a: '"x"', b: '"y"', ha: NOQUOTE1, hb: NOQUOTE1 },
  },
  {
    law: "abnf_clean_input_is_one_field",
    section: "abnf_clean_input_is_one_field",
    from: "      recs(t, RRec{}, TCon{KText{c}, cur}, done)",
    nth: 2,
    to: "      recs(t, RRec{}, cur, done)",
    why: "an ordinary character is dropped instead of kept in the record",
    failsIn: "recs_tx",
    at: { sep: "44", s: '"a"', h: CLEAN1 },
  },
  {
    law: "abnf_separator_makes_two_fields",
    section: "abnf_separator_makes_two_fields",
    from: "      fields(t, FOut{}, TNil{}, whole(cur, done))",
    nth: 1,
    to: "      fields(t, FOut{}, TCon{KSep{c}, cur}, done)",
    why: "a separator is kept as content and cuts no field",
    failsIn: "fields_sep",
    with: ["abnf_clean_input_is_one_field"],
    at: { sep: "44", hl: "{==}", hc: "{==}", a: '"x"', b: '"y"', ha: CLEAN1, hb: CLEAN1 },
  },
  {
    law: "abnf_quoted_field_is_its_content",
    section: "abnf_quoted_field_is_its_content",
    from: "      esc(t, EIn{}, SNil{})",
    to: "      bare(t, SNil{})",
    why: "a leading quote is read as an ordinary character, so a quoted field refuses",
    failsIn: "quoted_body",
    at: { sep: "44", hq: "{==}", s: '","', h: NOQUOTE1 },
  },
  {
    law: "abnf_doubled_quote_is_one_quote",
    section: "abnf_doubled_quote_is_one_quote",
    from: "      esc(t, EIn{}, String.append(txt, SCon{Chr{34}, SNil{}}))",
    to: "      esc(t, EIn{}, txt)",
    why: "the 2DQUOTE alternative keeps nothing, so two quotes in the text are none in the field",
    failsIn: "dq_bool",
    at: { sep: "44", hq: "{==}" },
  },
  {
    law: "abnf_lone_empty_field_keeps_its_row",
    section: "abnf_lone_empty_field_keeps_its_row",
    from: "      Some{txt}",
    nth: 2,
    to: "      None{}",
    why: "a quoted empty field is not a field, so its row is refused",
    failsIn: "Laws.abnf_lone_empty_field_keeps_its_row",
    at: { sep: "44", hq: "{==}" },
  },
  {
    law: "abnf_cr_inside_a_field_is_content",
    section: "abnf_cr_inside_a_field_is_content",
    from: "      recs(t, RRec{}, TCon{KText{c}, TCon{KCr{}, cur}}, done)",
    to: "      recs(t, RRec{}, TCon{KText{c}, cur}, done)",
    why: "a CR that ends no record is dropped instead of kept as content",
    failsIn: "Laws.abnf_cr_inside_a_field_is_content",
    at: { sep: "44", ha: "{==}", hb: "{==}" },
  },
];

runMutants(import.meta.dir, MUTANTS);
