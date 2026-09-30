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

const CLEAN2 = "({==}, {==}, {==}, {==}, ({==}, {==}, {==}, {==}, Unit{}))"; // Clean of two ordinary characters

// `from` lines are lines of the fused core.bend (`go`). failsIn names the def a
// proof must fail in; the proofs are open on this branch, so each names its law's
// own def, `Laws.<law>`, until the walk lemmas exist.
const MUTANTS: Mutant[] = [
  {
    law: "abnf_empty_input_is_no_record",
    section: "abnf_empty_input_is_no_record",
    from: "      Parsed{List.reverse(&2, List<&2, String>, close_empty(flds, rows))}",
    nth: 1,
    to: "      Parsed{List.reverse(&2, List<&2, String>, row(txt, flds, rows))}",
    why: "the end of input at a field start closes a record of one empty field, so the empty input holds one record",
    failsIn: "tn_base",
    at: { sep: "44" },
  },
  {
    law: "abnf_trailing_newline_adds_nothing",
    section: "abnf_trailing_newline_adds_nothing",
    from: "      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Nil{}, row(txt, flds, rows))",
    nth: 1,
    to: "      go(t, ME{}, cls_of(sep, t), sep, String.append(txt, one(Chr{10})), flds, rows)",
    why: "a newline after a bare field is kept as content in an open escaped field and closes no record, so a trailing one changes the answer",
    failsIn: "go_step",
    with: ["abnf_clean_input_is_one_field", "abnf_separator_makes_two_fields", "abnf_quoted_field_is_its_content", "abnf_blank_line_adds_nothing"],
    at: { sep: "44", s: '"a"' },
  },
  {
    law: "abnf_blank_line_adds_nothing",
    section: "abnf_blank_line_adds_nothing",
    from: "      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Nil{}, close_empty(flds, rows))",
    nth: 1,
    to: "      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Nil{}, row(txt, flds, rows))",
    why: "an empty line counts as a record of one empty field, so inserting one adds a row",
    failsIn: "go_step",
    with: ["abnf_quoted_field_is_its_content"],
    at: { sep: "44", a: '"x"', b: '"y"', ha: NOQUOTE1, hb: NOQUOTE1 },
  },
  {
    law: "abnf_clean_input_is_one_field",
    section: "abnf_clean_input_is_one_field",
    from: "      go(t, MB{}, cls_of(sep, t), sep, String.append(txt, one(c)), flds, rows)",
    to: "      go(t, MB{}, cls_of(sep, t), sep, txt, flds, rows)",
    why: "an ordinary character in a bare field is dropped instead of appended (needs two characters: the first one enters MB through MS)",
    failsIn: "walk_mb",
    at: { sep: "44", s: '"ab"', h: CLEAN2 },
  },
  {
    law: "abnf_separator_makes_two_fields",
    section: "abnf_separator_makes_two_fields",
    from: "      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Con{txt, flds}, rows)",
    nth: 1,
    to: "      go(t, MB{}, cls_of(sep, t), sep, String.append(txt, one(c)), flds, rows)",
    why: "a separator in a bare field is kept as content and cuts no field",
    failsIn: "walk_mb_sep",
    with: ["abnf_clean_input_is_one_field"],
    at: { sep: "44", hl: "{==}", hc: "{==}", a: '"x"', b: '"y"', ha: CLEAN1, hb: CLEAN1 },
  },
  {
    law: "abnf_quoted_field_is_its_content",
    section: "abnf_quoted_field_is_its_content",
    from: "      go(t, ME{}, cls_of(sep, t), sep, SNil{}, flds, rows)",
    to: "      go(t, MB{}, cls_of(sep, t), sep, one(c), flds, rows)",
    why: "a leading quote is read as an ordinary character, so a quoted field refuses",
    failsIn: "go_step",
    at: { sep: "44", hq: "{==}", s: '","', h: NOQUOTE1 },
  },
  {
    law: "abnf_doubled_quote_is_one_quote",
    section: "abnf_doubled_quote_is_one_quote",
    from: "      go(t, ME{}, cls_of(sep, t), sep, String.append(txt, one(Chr{34})), flds, rows)",
    to: "      go(t, ME{}, cls_of(sep, t), sep, txt, flds, rows)",
    why: "the 2DQUOTE alternative keeps nothing, so two quotes in the text are none in the field",
    failsIn: "go_step",
    at: { sep: "44", hq: "{==}" },
  },
  {
    law: "abnf_lone_empty_field_keeps_its_row",
    section: "abnf_lone_empty_field_keeps_its_row",
    from: "      go(t, MS{}, cls_of(sep, t), sep, SNil{}, Nil{}, row(txt, flds, rows))",
    nth: 2,
    to: "      Rejected{}",
    why: "a newline right after a closing quote refuses instead of closing the row, so a quoted empty field's row is refused",
    failsIn: "go_step",
    at: { sep: "44", hq: "{==}" },
  },
  {
    law: "abnf_cr_inside_a_field_is_content",
    section: "abnf_cr_inside_a_field_is_content",
    from: "      go(t, MB{}, cls_of(sep, t), sep, String.append(String.append(txt, one(Chr{13})), one(c)), flds, rows)",
    to: "      go(t, MB{}, cls_of(sep, t), sep, String.append(txt, one(c)), flds, rows)",
    why: "a CR that ends no record is dropped instead of kept as content",
    failsIn: "go_step",
    at: { sep: "44", ha: "{==}", hb: "{==}" },
  },
];

runMutants(import.meta.dir, MUTANTS);
