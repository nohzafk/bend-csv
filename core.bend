import Base

# csv-abnf: RFC 4180 CSV parsing, shaped like the grammar it implements.
#
# The reading is layered, one pass per level of the grammar, and the state is
# the rows: there is no line or column, so nothing in a law has to mention one.
#
# The ABNF this file transcribes (RFC 4180 section 2):
#
#   file        = [header CRLF] record *(CRLF record) [CRLF]
#   header      = name *(COMMA name)
#   name        = field
#   record      = field *(COMMA field)
#   field       = (escaped / non-escaped)
#   escaped     = DQUOTE *(TEXTDATA / COMMA / CR / LF / 2DQUOTE) DQUOTE
#   non-escaped = *TEXTDATA
#   COMMA       = %x2C          CR = %x0D        DQUOTE = %x22
#   LF          = %x0A          CRLF = CR LF
#   TEXTDATA    = %x20-21 / %x23-2B / %x2D-7E
#
# Three refinements of it, each measured against the reference (@std/csv) and
# each what a first guess gets wrong:
#
#   * a blank line is not a record -- `record` as written can be an empty field,
#     so the grammar over-generates here, and the reading drops it;
#   * CR is not TEXTDATA, but a CR the line does not end at is content, so a
#     record ends at LF, at CRLF, or at a CR the input ends on;
#   * a trailing newline adds no record.
#
# The shape, and why it is this shape. bend rejects a self-call unless, reading
# the arguments left to right, one shrinks and every argument before it is
# passed unchanged (Bend's rule for a self-call), and it does not read a helper's result as
# a subterm at all. So no pass can peel a piece with a helper and recurse on
# what the helper left. What is expressible:
#
#   * one walk per level of the grammar, with its input as the first parameter
#     and its position in a mode parameter;
#   * between the levels, a map whose own recursion takes a pattern-bound tail.
#
# Every def below obeys those two rules, so nothing recurses on a computed
# value. Nothing matches a computed value either: the modes are parameters and
# the character kind is a constructor, which is what lets the laws quantify over
# abstract input.

# ---- the answer ----
#
# There is no position here and no reason. Whether an input is a file is the
# grammar's question, and where a defect is would be a policy for a caller to layer on top.
type Ans is Data:
  Parsed{rows: List<&2, List<&2, String>>}
  Rejected{}

# ---- the character, as the grammar sees it ----
#
# The parser never compares a character to a constant, and never matches a
# literal character: the kind is decided once, by these four comparisons, and
# then matched as data.
type K is Data:
  KSep{c: Char}
  KCr{}
  KLf{}
  KQuote{}
  KText{c: Char}

def kind_go(+lf: Bool, +cr: Bool, +sep: Bool, +quote: Bool, +c: Char) -> K:
  match lf:
    case True{}:
      KLf{}
    case False{}:
      match cr:
        case True{}:
          KCr{}
        case False{}:
          match sep:
            case True{}:
              KSep{c}
            case False{}:
              match quote:
                case True{}:
                  KQuote{}
                case False{}:
                  KText{c}

def kind(+sep: U32, +c: Char) -> K:
  kind_go(U32.is_eq(Char.to_u32(c), 10), U32.is_eq(Char.to_u32(c), 13), U32.is_eq(sep, Char.to_u32(c)), U32.is_eq(Char.to_u32(c), 34), c)

type Tok is Data:
  TNil{}
  TCon{k: K, rest: Tok}

def tokens(+sep: U32, +s: String) -> Tok:
  match s:
    case SNil{}:
      TNil{}
    case SCon{c, t}:
      TCon{kind(sep, c), tokens(sep, t)}

# ---- level one: the file is a sequence of records ----
#
# `RRec` is between records, `REsc` is inside an escaped field, `REscQ` is just
# after a quote inside one, and `RCr` holds a CR whose meaning the next token
# decides. The quote modes are the grammar's own positions; the CR mode is the
# reading's, because CRLF is a two-character terminal.
type RPh is Data:
  RRec{}
  REsc{}
  REscQ{}
  RCr{}

# A record's tokens, and a field's tokens, are read in order by the level below,
# so the walk's backwards accumulator is turned around where the piece closes.
# (The outer reverse at the end of a walk only orders the pieces themselves.)
# Tok is a type of its own, not a List, so it needs its own reverse.
def rev_tok(+ts: Tok, +acc: Tok) -> Tok:
  match ts:
    case TNil{}:
      acc
    case TCon{k, t}:
      rev_tok(t, TCon{k, acc})

def whole(+cur: Tok, +done: List<&2, Tok>) -> List<&2, Tok>:
  Con{rev_tok(cur, TNil{}), done}

# A record of no tokens is not a record at all. An empty line arrives here as an
# empty `cur`, and `""` as two quote tokens.
def add_rec(+cur: Tok, +done: List<&2, Tok>) -> List<&2, Tok>:
  match cur:
    case TNil{}:
      done
    case TCon{_, _}:
      whole(cur, done)

def recs(+ts: Tok, +ph: RPh, +cur: Tok, +done: List<&2, Tok>) -> List<&2, Tok>:
  match ts ph:
    case TNil{} RRec{}:
      List.reverse(&2, Tok, add_rec(cur, done))
    case TNil{} REsc{}:
      List.reverse(&2, Tok, add_rec(cur, done))
    case TNil{} REscQ{}:
      List.reverse(&2, Tok, add_rec(cur, done))
    case TNil{} RCr{}:
      List.reverse(&2, Tok, add_rec(cur, done))
    # a record ends: LF, or CRLF, or a CR the input ends on
    case TCon{KLf{}, t} RRec{}:
      recs(t, RRec{}, TNil{}, add_rec(cur, done))
    case TCon{KCr{}, t} RRec{}:
      recs(t, RCr{}, cur, done)
    # inside an escaped field a newline is content (LF, and CR too)
    case TCon{KLf{}, t} REsc{}:
      recs(t, REsc{}, TCon{KLf{}, cur}, done)
    case TCon{KCr{}, t} REsc{}:
      recs(t, REsc{}, TCon{KCr{}, cur}, done)
    case TCon{KSep{c}, t} REsc{}:
      recs(t, REsc{}, TCon{KSep{c}, cur}, done)
    case TCon{KText{c}, t} REsc{}:
      recs(t, REsc{}, TCon{KText{c}, cur}, done)
    case TCon{KQuote{}, t} REsc{}:
      recs(t, REscQ{}, TCon{KQuote{}, cur}, done)
    # just after a quote inside an escaped field: a second quote is the escape,
    # anything else means the field closed and this token is read at the record
    case TCon{KQuote{}, t} REscQ{}:
      recs(t, REsc{}, TCon{KQuote{}, cur}, done)
    case TCon{KLf{}, t} REscQ{}:
      recs(t, RRec{}, TNil{}, add_rec(cur, done))
    case TCon{KCr{}, t} REscQ{}:
      recs(t, RCr{}, cur, done)
    case TCon{KSep{c}, t} REscQ{}:
      recs(t, RRec{}, TCon{KSep{c}, cur}, done)
    case TCon{KText{c}, t} REscQ{}:
      recs(t, RRec{}, TCon{KText{c}, cur}, done)
    # a CR that ends nothing is content, and the token after it is read here
    case TCon{KCr{}, t} RCr{}:
      recs(t, RCr{}, TCon{KCr{}, cur}, done)
    case TCon{KLf{}, t} RCr{}:
      recs(t, RRec{}, TNil{}, add_rec(cur, done))
    case TCon{KQuote{}, t} RCr{}:
      recs(t, REsc{}, TCon{KQuote{}, TCon{KCr{}, cur}}, done)
    case TCon{KSep{c}, t} RCr{}:
      recs(t, RRec{}, TCon{KSep{c}, TCon{KCr{}, cur}}, done)
    case TCon{KText{c}, t} RCr{}:
      recs(t, RRec{}, TCon{KText{c}, TCon{KCr{}, cur}}, done)
    # between fields: a separator, a quote that opens an escaped field, or text
    case TCon{KSep{c}, t} RRec{}:
      recs(t, RRec{}, TCon{KSep{c}, cur}, done)
    case TCon{KQuote{}, t} RRec{}:
      recs(t, REsc{}, TCon{KQuote{}, cur}, done)
    case TCon{KText{c}, t} RRec{}:
      recs(t, RRec{}, TCon{KText{c}, cur}, done)

# ---- level two: a record is a sequence of fields ----
type FPh is Data:
  FOut{}
  FIn{}
  FInQ{}

# Split at the separators that are not inside an escaped field. A field's tokens
# are kept whole, quotes and all: whether they spell a field is level three's
# question, and keeping them makes this walk total.
def fields(+ts: Tok, +ph: FPh, +cur: Tok, +done: List<&2, Tok>) -> List<&2, Tok>:
  match ts ph:
    case TNil{} FOut{}:
      List.reverse(&2, Tok, whole(cur, done))
    case TNil{} FIn{}:
      List.reverse(&2, Tok, whole(cur, done))
    case TNil{} FInQ{}:
      List.reverse(&2, Tok, whole(cur, done))
    case TCon{KSep{c}, t} FOut{}:
      fields(t, FOut{}, TNil{}, whole(cur, done))
    case TCon{KQuote{}, t} FOut{}:
      fields(t, FIn{}, TCon{KQuote{}, cur}, done)
    case TCon{KCr{}, t} FOut{}:
      fields(t, FOut{}, TCon{KCr{}, cur}, done)
    case TCon{KLf{}, t} FOut{}:
      fields(t, FOut{}, TCon{KLf{}, cur}, done)
    case TCon{KText{c}, t} FOut{}:
      fields(t, FOut{}, TCon{KText{c}, cur}, done)
    case TCon{KQuote{}, t} FIn{}:
      fields(t, FInQ{}, TCon{KQuote{}, cur}, done)
    case TCon{KSep{c}, t} FIn{}:
      fields(t, FIn{}, TCon{KSep{c}, cur}, done)
    case TCon{KCr{}, t} FIn{}:
      fields(t, FIn{}, TCon{KCr{}, cur}, done)
    case TCon{KLf{}, t} FIn{}:
      fields(t, FIn{}, TCon{KLf{}, cur}, done)
    case TCon{KText{c}, t} FIn{}:
      fields(t, FIn{}, TCon{KText{c}, cur}, done)
    case TCon{KQuote{}, t} FInQ{}:
      fields(t, FIn{}, TCon{KQuote{}, cur}, done)
    case TCon{KSep{c}, t} FInQ{}:
      fields(t, FOut{}, TNil{}, whole(cur, done))
    case TCon{KCr{}, t} FInQ{}:
      fields(t, FOut{}, TCon{KCr{}, cur}, done)
    case TCon{KLf{}, t} FInQ{}:
      fields(t, FOut{}, TCon{KLf{}, cur}, done)
    case TCon{KText{c}, t} FInQ{}:
      fields(t, FOut{}, TCon{KText{c}, cur}, done)

# ---- level three: a field is escaped or non-escaped ----
#
# The field's text is built in reading order, so no pass has to reverse it.

# non-escaped = *TEXTDATA, and DQUOTE is not TEXTDATA: a quote here is not this
# alternative, which is why the whole input is no file.
def bare(+ts: Tok, +txt: String) -> Maybe<&2, String>:
  match ts:
    case TNil{}:
      Some{txt}
    case TCon{KSep{c}, t}:
      bare(t, String.append(txt, SCon{c, SNil{}}))
    case TCon{KCr{}, t}:
      bare(t, String.append(txt, SCon{Chr{13}, SNil{}}))
    case TCon{KLf{}, t}:
      bare(t, String.append(txt, SCon{Chr{10}, SNil{}}))
    case TCon{KText{c}, t}:
      bare(t, String.append(txt, SCon{c, SNil{}}))
    case TCon{KQuote{}, t}:
      None{}

# escaped = DQUOTE *(TEXTDATA / COMMA / CR / LF / 2DQUOTE) DQUOTE. The opening
# quote is already read when this is called, and `EInQ` means the last token was
# a quote -- which the 2DQUOTE alternative makes ambiguous until the next one:
# a quote followed by another quote is one literal quote, and only a quote the
# field ends at closes it. The two positions are one def because they call each
# other, and mutual recursion is not allowed.
type EPh is Data:
  EIn{}
  EInQ{}

def esc(+ts: Tok, +ph: EPh, +txt: String) -> Maybe<&2, String>:
  match ts ph:
    case TNil{} EIn{}:
      None{}
    case TNil{} EInQ{}:
      Some{txt}
    case TCon{KQuote{}, t} EIn{}:
      esc(t, EInQ{}, txt)
    case TCon{KQuote{}, t} EInQ{}:
      esc(t, EIn{}, String.append(txt, SCon{Chr{34}, SNil{}}))
    case TCon{KSep{c}, t} EIn{}:
      esc(t, EIn{}, String.append(txt, SCon{c, SNil{}}))
    case TCon{KSep{c}, t} EInQ{}:
      None{}
    case TCon{KCr{}, t} EIn{}:
      esc(t, EIn{}, String.append(txt, SCon{Chr{13}, SNil{}}))
    case TCon{KCr{}, t} EInQ{}:
      None{}
    case TCon{KLf{}, t} EIn{}:
      esc(t, EIn{}, String.append(txt, SCon{Chr{10}, SNil{}}))
    case TCon{KLf{}, t} EInQ{}:
      None{}
    case TCon{KText{c}, t} EIn{}:
      esc(t, EIn{}, String.append(txt, SCon{c, SNil{}}))
    case TCon{KText{c}, t} EInQ{}:
      None{}

# field = (escaped / non-escaped): the first token decides which. The first
# token is also the one the walk that follows is called past, so that its
# argument shrinks.
def decode(+ts: Tok) -> Maybe<&2, String>:
  match ts:
    case TNil{}:
      Some{SNil{}}
    case TCon{KQuote{}, t}:
      esc(t, EIn{}, SNil{})
    case TCon{KSep{c}, t}:
      bare(t, SCon{c, SNil{}})
    case TCon{KCr{}, t}:
      bare(t, SCon{Chr{13}, SNil{}})
    case TCon{KLf{}, t}:
      bare(t, SCon{Chr{10}, SNil{}})
    case TCon{KText{c}, t}:
      bare(t, SCon{c, SNil{}})

# ---- the maps between the levels ----
#
# Each of these recurses on a pattern-bound tail and computes nothing before it.

def field_map(+rs: List<&2, Tok>) -> List<&2, List<&2, Tok>>:
  match rs:
    case Nil{}:
      Nil{}
    case Con{r, t}:
      Con{fields(r, FOut{}, TNil{}, Nil{}), field_map(t)}

def text_map(+fs: List<&2, Tok>) -> List<&2, Maybe<&2, String>>:
  match fs:
    case Nil{}:
      Nil{}
    case Con{f, t}:
      Con{decode(f), text_map(t)}

# A row is the fields of one record, in reading order; the first field that is
# not a field makes the row no row. The element's constructor is matched in the
# list pattern, never as a computed value.
def row_of(+vs: List<&2, Maybe<&2, String>>, +acc: List<&2, String>) -> Maybe<&2, List<&2, String>>:
  match vs:
    case Nil{}:
      Some{List.reverse(&2, String, acc)}
    case Con{Some{s}, t}:
      row_of(t, Con{s, acc})
    case Con{None{}, t}:
      None{}

def rows_map(+rss: List<&2, List<&2, Tok>>) -> List<&2, Maybe<&2, List<&2, String>>>:
  match rss:
    case Nil{}:
      Nil{}
    case Con{fs, t}:
      Con{row_of(text_map(fs), Nil{}), rows_map(t)}

def rows(+ms: List<&2, Maybe<&2, List<&2, String>>>, +acc: List<&2, List<&2, String>>) -> Ans:
  match ms:
    case Nil{}:
      Parsed{List.reverse(&2, List<&2, String>, acc)}
    case Con{Some{r}, t}:
      rows(t, Con{r, acc})
    case Con{None{}, t}:
      Rejected{}

# ---- the file ----
def parse_sep(+sep: U32, +s: String) -> Ans:
  rows(rows_map(field_map(recs(tokens(sep, s), RRec{}, TNil{}, Nil{}))), Nil{})

# The comma instance, which is what a caller wants most of the time.
def parse(+s: String) -> Ans:
  parse_sep(44, s)
