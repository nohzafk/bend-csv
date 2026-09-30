import Base
import ./core.bend as A

# bend-csv's laws.
#
# Twelve laws about core.bend (the fused walk `go`). Agreement with another CSV parser is not a law
# here: it is checked by oracle.ts, which is a test, and an oracle can find a bug
# but proves nothing.
#
# Each law below states the grammar for core.bend. What each needs of the
# separator is a hypothesis rather than an assumption, and the notes beside the
# laws say why: three of them are false without it.

# ---- the vocabulary the laws use ----
#
# Clean is the input the parser reads with no decision anywhere -- no
# separator, no quote, no CR, no LF; NoQuote is the input that cannot reach any
# of the three quote defects.

def Clean(sep: U32, s: String) -> Type:
  match s:
    case SNil{}:
      Unit
    case SCon{Chr{x}, t}:
      {U32.is_eq(sep, x) == False{} : Bool} & {U32.is_eq(x, 34) == False{} : Bool} & {U32.is_eq(x, 13) == False{} : Bool} & {U32.is_eq(x, 10) == False{} : Bool} & Clean(sep, t)

def NoQuote(s: String) -> Type:
  match s:
    case SNil{}:
      Unit
    case SCon{Chr{x}, t}:
      {U32.is_eq(x, 34) == False{} : Bool} & NoQuote(t)

# ---- the laws ----

# What a clean input must parse to: no record at all when it is empty, and one
# record of one field -- itself -- when it is not. Matched on the string rather
# than computed through a test for emptiness, so that a proof reduces it by the
# same case split the induction uses.
def CleanAnswer(s: String) -> A.Ans:
  match s:
    case SNil{}:
      A.Parsed{Nil{}}
    case SCon{c, t}:
      A.Parsed{Con{Con{s, Nil{}}, Nil{}}}

law abnf_empty_input_is_no_record:
  for +sep: U32
  {A.parse_sep(sep, "") == A.Parsed{Nil{}} : A.Ans}

# Ending an unfinished record adds no row. If the input does not already end
# at a line end (its last character x is not LF), a final LF only closes the
# record the end of input would have closed anyway. The law is silent when the
# input is empty or already ends in LF: there a further LF is a blank line and
# adds a row (see the blank-line laws).
law abnf_ending_an_unfinished_record_adds_no_row:
  for +sep: U32
  for +s: String
  for +x: U32
  for hx: {U32.is_eq(x, 10) == False{} : Bool}
  {A.parse_sep(sep, String.append(String.append(s, SCon{Chr{x}, SNil{}}), "\n"))
    == A.parse_sep(sep, String.append(s, SCon{Chr{x}, SNil{}})) : A.Ans}

# A blank line is a record of one empty field, kept in place: it reads exactly
# as the line "" (a quoted empty field, which the law
# abnf_lone_empty_field_keeps_its_row and abnf_quoted_field_is_its_content pin
# to one row holding one empty field). Stated after any prefix that has not
# opened a quote (NoQuote), for LF blank lines and CRLF blank lines, and at
# the very start of the input.
law abnf_blank_line_is_a_record:
  for +sep: U32
  for +hq: {U32.is_eq(sep, 34) == False{} : Bool}
  for +a: String
  for ha: NoQuote(a)
  for +b: String
  {A.parse_sep(sep, String.append(a, String.append("\n\n", b)))
    == A.parse_sep(sep, String.append(a, String.append("\n\"\"\n", b))) : A.Ans}

law abnf_crlf_blank_line_is_a_record:
  for +sep: U32
  for +hq: {U32.is_eq(sep, 34) == False{} : Bool}
  for +a: String
  for ha: NoQuote(a)
  for +b: String
  {A.parse_sep(sep, String.append(a, String.append("\n\r\n", b)))
    == A.parse_sep(sep, String.append(a, String.append("\n\"\"\n", b))) : A.Ans}

law abnf_leading_blank_line_is_a_record:
  for +sep: U32
  for +hq: {U32.is_eq(sep, 34) == False{} : Bool}
  for +b: String
  {A.parse_sep(sep, String.append("\n", b))
    == A.parse_sep(sep, String.append("\"\"\n", b)) : A.Ans}

law abnf_leading_crlf_blank_line_is_a_record:
  for +sep: U32
  for +hq: {U32.is_eq(sep, 34) == False{} : Bool}
  for +b: String
  {A.parse_sep(sep, String.append("\r\n", b))
    == A.parse_sep(sep, String.append("\"\"\n", b)) : A.Ans}

law abnf_clean_input_is_one_field:
  for +sep: U32
  for +s: String
  for h: Clean(sep, s)
  {A.parse_sep(sep, s) == CleanAnswer(s) : A.Ans}

law abnf_separator_makes_two_fields:
  for +sep: U32
  for hl: {U32.is_eq(sep, 10) == False{} : Bool}
  for hc: {U32.is_eq(sep, 13) == False{} : Bool}
  for +a: String
  for +b: String
  for ha: Clean(sep, a)
  for hb: Clean(sep, b)
  {A.parse_sep(sep, String.append(String.append(a, SCon{Chr{sep}, SNil{}}), b))
    == A.Parsed{Con{Con{a, Con{b, Nil{}}}, Nil{}}} : A.Ans}

law abnf_quoted_field_is_its_content:
  for +sep: U32
  for +hq: {U32.is_eq(sep, 34) == False{} : Bool}
  for +s: String
  for h: NoQuote(s)
  {A.parse_sep(sep, String.append(String.append("\"", s), "\""))
    == A.Parsed{Con{Con{s, Nil{}}, Nil{}}} : A.Ans}

# escaped = DQUOTE *(TEXTDATA / COMMA / CR / LF / 2DQUOTE) DQUOTE: the 2DQUOTE
# alternative is what turns two quotes in the text into one in the field, and
# no other law pins it.
law abnf_doubled_quote_is_one_quote:
  for +sep: U32
  for +hq: {U32.is_eq(sep, 34) == False{} : Bool}
  {A.parse_sep(sep, "\"a\"\"b\"") == A.Parsed{Con{Con{"a\"b", Nil{}}, Nil{}}} : A.Ans}

# field = (escaped / non-escaped): a quoted empty field is a field, so the row
# survives.
#
# The hypothesis is the same one `abnf_quoted_field_is_its_content` needs: with
# the quote as the separator, the two quotes in the input ARE two separators and
# the answer is three empty fields, so the law is false without it. (The
# falsifier's separator set has to contain the quote for that to be tested, and
# it does.)
law abnf_lone_empty_field_keeps_its_row:
  for +sep: U32
  for +hq: {U32.is_eq(sep, 34) == False{} : Bool}
  {A.parse_sep(sep, String.append("\"\"", "\n")) == A.Parsed{Con{Con{"", Nil{}}, Nil{}}} : A.Ans}

# CR is not TEXTDATA, but a CR the line does not end at is content (measured
# against the reference). Stated as one instance, because the general form
# "--appending a CR changes nothing--" is false: after a CR the next CR is
# content, so "\r" and "\r\r" are different inputs.
#
# The two hypotheses are the input's own letters, and they are not optional: the
# law holds for every separator EXCEPT the two that appear in the input, where
# the letter is a separator and the reading is a different one. The falsifier
# found this: the falsifier's separator set has to include letters for a claim
# like this one to be tested where it is false.
law abnf_cr_inside_a_field_is_content:
  for +sep: U32
  for ha: {U32.is_eq(sep, 97) == False{} : Bool}
  for hb: {U32.is_eq(sep, 98) == False{} : Bool}
  {A.parse_sep(sep, "a\rb\r\n") == A.Parsed{Con{Con{"a\rb", Nil{}}, Nil{}}} : A.Ans}
