import Base
import ./LAWS.bend as Laws
import ./core.bend as A
import ./vendor/bendlib/packages/bend-mathlib/string.bend as MS
import ./vendor/bendlib/packages/bend-mathlib/list.bend as ML

# csv-abnf's proofs. The gate is `bend PROOF.bend`.
#
# Each law of LAWS.bend is filled by a `def Laws.<name>` here: the law's `for`
# binders are the parameters, in order, and the law's statement is the type.
# Nothing is stated twice -- a law that is not filled is reported by the
# checker as open.
#
# The order below is the order the laws are proved in, easiest first, because
# each proof tends to need the previous one's tools.

# ---- abnf_empty_input_is_no_record ----
#
# Nothing to rewrite. The empty input tokenizes to TNil, the record walk closes a
# record of no tokens (which is no record at all), and every map over the empty
# list is the empty list -- so both sides of the law reduce to the same term.
def Laws.abnf_empty_input_is_no_record(sep):
  {==}

# ---- abnf_lone_empty_field_keeps_its_row ----
#
# Two quotes and a newline. The newline is KLf whatever the separator is -- the
# the parser tests LF before the separator -- but a quote is a quote only when the
# separator is not the quote, which is the law's hypothesis.
#
# The goal is the FULLY UNFOLDED form: `A.parse` has already become
# rows/rows_map/field_map/recs, the token list is spelled out, and `U32.is_eq`
# is written `Cmp.is_eq(U32.cmp(..))`. That last one is why the rewrite's term is
# spelled out rather than written `U32.is_eq(sep, 34)`: a rewrite eliminates the
# right-hand side of its own type, so with `hq : {U32.is_eq(sep,34) == False{}}`
# it replaces `Cmp.is_eq(U32.cmp(sep, 34))` with `False{}`.
#
# One rewrite per occurrence: a hole marks exactly one position, so the two
# quotes in the input need two lines, and the second line's goal is the first
# line's result. (A helper lemma about the whole token list works too and is no
# shorter here; it would be the cut if the general laws wanted that lemma.)
def Laws.abnf_lone_empty_field_keeps_its_row(sep, hq):
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, 34)), False{}, hq) : {A.rows(A.rows_map(A.field_map(A.recs(A.TCon{A.kind_go(False{}, False{}, _, True{}, '"'), A.TCon{A.kind_go(False{}, False{}, Cmp.is_eq(U32.cmp(sep, 34)), True{}, '"'), A.TCon{A.KLf{}, A.TNil{}}}}, A.RRec{}, A.TNil{}, []))), []) == A.Parsed{Con{Con{"", Nil{}}, Nil{}}} : A.Ans}
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, 34)), False{}, hq) : {A.rows(A.rows_map(A.field_map(A.recs(A.TCon{A.kind_go(False{}, False{}, False{}, True{}, '"'), A.TCon{A.kind_go(False{}, False{}, _, True{}, '"'), A.TCon{A.KLf{}, A.TNil{}}}}, A.RRec{}, A.TNil{}, []))), []) == A.Parsed{Con{Con{"", Nil{}}, Nil{}}} : A.Ans}
  {==}

# ---- abnf_cr_inside_a_field_is_content ----
#
# A concrete input, with a hypothesis per letter: with the separator `a`, the
# `a` in `a\rb` is a separator and the claim is false. One rewrite per letter,
# the same shape as the law above. The CRs and the LF need no rewrite: their
# kinds are decided before the separator is compared with them.
#
# The token term below is the checker's own output (printed with `?p`), not
# hand-counted: the whole annotation is a term the checker already holds.
def Laws.abnf_cr_inside_a_field_is_content(sep, ha, hb):
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, 97)), False{}, ha) : {A.rows(A.rows_map(A.field_map(A.recs(A.TCon{A.kind_go(False{}, False{}, _, False{}, 'a'), A.TCon{A.KCr{}, A.TCon{A.kind_go(False{}, False{}, Cmp.is_eq(U32.cmp(sep, 98)), False{}, 'b'), A.TCon{A.KCr{}, A.TCon{A.KLf{}, A.TNil{}}}}}}, A.RRec{}, A.TNil{}, []))), []) == A.Parsed{[["a\rb"]]} : A.Ans}
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, 98)), False{}, hb) : {A.rows(A.rows_map(A.field_map(A.recs(A.TCon{A.kind_go(False{}, False{}, False{}, False{}, 'a'), A.TCon{A.KCr{}, A.TCon{A.kind_go(False{}, False{}, _, False{}, 'b'), A.TCon{A.KCr{}, A.TCon{A.KLf{}, A.TNil{}}}}}}, A.RRec{}, A.TNil{}, []))), []) == A.Parsed{[["a\rb"]]} : A.Ans}
  {==}

# ---- the order the rest are proved in ----
#
# One walk lemma per level, an induction over the input with the level's
# accumulator carried -- see `abnf_clean_input_is_one_field` below for the shape.
# What each remaining law needs:
#
#   abnf_trailing_newline_adds_nothing        the record walk, once more for a
#                                             trailing newline
#   abnf_blank_line_adds_nothing              the same, for an empty line
#   abnf_separator_makes_two_fields           the field walk, with a separator
#   abnf_quoted_field_is_its_content          the escaped walk
#   abnf_doubled_quote_is_one_quote           the escaped walk, doubled quotes
#   abnf_is_csv_lib                           the last one, and the expensive one

# ---- abnf_clean_input_is_one_field ----
#
# One walk lemma per level, each an induction over the input with the level's
# accumulator carried. `Clean` is consumed once, at the tokenizer; past that the
# input is a chain of KText tokens and the modes never move, which is why these
# lemmas are plain inductions and need no mathlib reverse lemma: the reversed
# accumulators are carried explicitly (`push` mirrors `cur`, `rt_push` says what
# rev_tok does to it).
def tx(+s: String, +r: A.Tok) -> A.Tok:
  match s:
    case SNil{}:
      r
    case SCon{c, t}:
      A.TCon{A.KText{c}, tx(t, r)}

def push(+s: String, +cur: A.Tok) -> A.Tok:
  match s:
    case SNil{}:
      cur
    case SCon{c, t}:
      push(t, A.TCon{A.KText{c}, cur})

def tok_clean(+sep: U32, s: String, h: Laws.Clean(sep, s)) -> {A.tokens(sep, s) == tx(s, A.TNil{}) : A.Tok}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, t}:
      (hse, hqu, hcr, hlf, ht) = h
      %Equal.sym(Bool, Cmp.is_eq(U32.cmp(x, 10)), False{}, hlf) : {A.TCon{A.kind_go(_, Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34)), Chr{x}), A.tokens(sep, t)} == A.TCon{A.KText{Chr{x}}, tx(t, A.TNil{})} : A.Tok}
      %Equal.sym(Bool, Cmp.is_eq(U32.cmp(x, 13)), False{}, hcr) : {A.TCon{A.kind_go(False{}, _, Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34)), Chr{x}), A.tokens(sep, t)} == A.TCon{A.KText{Chr{x}}, tx(t, A.TNil{})} : A.Tok}
      %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, x)), False{}, hse) : {A.TCon{A.kind_go(False{}, False{}, _, Cmp.is_eq(U32.cmp(x, 34)), Chr{x}), A.tokens(sep, t)} == A.TCon{A.KText{Chr{x}}, tx(t, A.TNil{})} : A.Tok}
      %Equal.sym(Bool, Cmp.is_eq(U32.cmp(x, 34)), False{}, hqu) : {A.TCon{A.kind_go(False{}, False{}, False{}, _, Chr{x}), A.tokens(sep, t)} == A.TCon{A.KText{Chr{x}}, tx(t, A.TNil{})} : A.Tok}
      %tok_clean(sep, t, ht) : {A.TCon{A.KText{Chr{x}}, A.tokens(sep, t)} == A.TCon{A.KText{Chr{x}}, _} : A.Tok}
      {==}

def recs_tx(+s: String, +cur: A.Tok, +done: List<&2, A.Tok>) -> {A.recs(tx(s, A.TNil{}), A.RRec{}, cur, done) == List.reverse(&2, A.Tok, A.add_rec(push(s, cur), done)) : List<&2, A.Tok>}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      recs_tx(t, A.TCon{A.KText{c}, cur}, done)

def fields_tx(+s: String, +cur: A.Tok, +done: List<&2, A.Tok>) -> {A.fields(tx(s, A.TNil{}), A.FOut{}, cur, done) == List.reverse(&2, A.Tok, A.whole(push(s, cur), done)) : List<&2, A.Tok>}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      fields_tx(t, A.TCon{A.KText{c}, cur}, done)

def rt_push(+s: String, +cur: A.Tok, +acc: A.Tok) -> {A.rev_tok(push(s, cur), acc) == A.rev_tok(cur, tx(s, acc)) : A.Tok}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      rt_push(t, A.TCon{A.KText{c}, cur}, acc)

def add_push(+s: String, +k: A.K, +cur: A.Tok, +done: List<&2, A.Tok>) -> {A.add_rec(push(s, A.TCon{k, cur}), done) == A.whole(push(s, A.TCon{k, cur}), done) : List<&2, A.Tok>}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      add_push(t, A.KText{c}, A.TCon{k, cur}, done)

def bare_tx(+t: String, +txt: String) -> {A.bare(tx(t, A.TNil{}), txt) == Some{String.append(txt, t)} : Maybe<&2, String>}:
  match t:
    case SNil{}:
      %MS.append_nil(txt) : {Some{_} == Some{String.append(txt, SNil{})} : Maybe<&2, String>}
      {==}
    case SCon{c, u}:
      %MS.append_assoc(txt, SCon{c, SNil{}}, u) : {A.bare(tx(u, A.TNil{}), String.append(txt, SCon{c, SNil{}})) == Some{_} : Maybe<&2, String>}
      bare_tx(u, String.append(txt, SCon{c, SNil{}}))

def recs_one(+c: Char, +t: String) -> {A.recs(tx(t, A.TNil{}), A.RRec{}, A.TCon{A.KText{c}, A.TNil{}}, []) == Con{A.TCon{A.KText{c}, tx(t, A.TNil{})}, Nil{}} : List<&2, A.Tok>}:
  %Equal.sym(List<&2, A.Tok>, A.recs(tx(t, A.TNil{}), A.RRec{}, A.TCon{A.KText{c}, A.TNil{}}, []), List.reverse(&2, A.Tok, A.add_rec(push(t, A.TCon{A.KText{c}, A.TNil{}}), [])), recs_tx(t, A.TCon{A.KText{c}, A.TNil{}}, [])) : {_ == Con{A.TCon{A.KText{c}, tx(t, A.TNil{})}, Nil{}} : List<&2, A.Tok>}
  %Equal.sym(List<&2, A.Tok>, A.add_rec(push(t, A.TCon{A.KText{c}, A.TNil{}}), []), A.whole(push(t, A.TCon{A.KText{c}, A.TNil{}}), []), add_push(t, A.KText{c}, A.TNil{}, [])) : {List.reverse(&2, A.Tok, _) == Con{A.TCon{A.KText{c}, tx(t, A.TNil{})}, Nil{}} : List<&2, A.Tok>}
  %Equal.sym(A.Tok, A.rev_tok(push(t, A.TCon{A.KText{c}, A.TNil{}}), A.TNil{}), A.rev_tok(A.TCon{A.KText{c}, A.TNil{}}, tx(t, A.TNil{})), rt_push(t, A.TCon{A.KText{c}, A.TNil{}}, A.TNil{})) : {[_] == [A.TCon{A.KText{c}, tx(t, A.TNil{})}] : List<&2, A.Tok>}
  {==}

def fields_one(+c: Char, +t: String) -> {A.fields(tx(t, A.TNil{}), A.FOut{}, A.TCon{A.KText{c}, A.TNil{}}, []) == Con{A.TCon{A.KText{c}, tx(t, A.TNil{})}, Nil{}} : List<&2, A.Tok>}:
  %Equal.sym(List<&2, A.Tok>, A.fields(tx(t, A.TNil{}), A.FOut{}, A.TCon{A.KText{c}, A.TNil{}}, []), List.reverse(&2, A.Tok, A.whole(push(t, A.TCon{A.KText{c}, A.TNil{}}), [])), fields_tx(t, A.TCon{A.KText{c}, A.TNil{}}, [])) : {_ == Con{A.TCon{A.KText{c}, tx(t, A.TNil{})}, Nil{}} : List<&2, A.Tok>}
  %Equal.sym(A.Tok, A.rev_tok(push(t, A.TCon{A.KText{c}, A.TNil{}}), A.TNil{}), A.rev_tok(A.TCon{A.KText{c}, A.TNil{}}, tx(t, A.TNil{})), rt_push(t, A.TCon{A.KText{c}, A.TNil{}}, A.TNil{})) : {[_] == [A.TCon{A.KText{c}, tx(t, A.TNil{})}] : List<&2, A.Tok>}
  {==}

def one_cons(+c: Char, +t: String) -> {A.rows(A.rows_map(A.field_map(A.recs(tx(SCon{c, t}, A.TNil{}), A.RRec{}, A.TNil{}, []))), []) == A.Parsed{[[SCon{c, t}]]} : A.Ans}:
  %Equal.sym(List<&2, A.Tok>, A.recs(tx(t, A.TNil{}), A.RRec{}, A.TCon{A.KText{c}, A.TNil{}}, []), [A.TCon{A.KText{c}, tx(t, A.TNil{})}], recs_one(c, t)) : {A.rows(A.rows_map(A.field_map(_)), []) == A.Parsed{[[SCon{c, t}]]} : A.Ans}
  %Equal.sym(List<&2, A.Tok>, A.fields(tx(t, A.TNil{}), A.FOut{}, A.TCon{A.KText{c}, A.TNil{}}, []), [A.TCon{A.KText{c}, tx(t, A.TNil{})}], fields_one(c, t)) : {A.rows(A.rows_map([_]), []) == A.Parsed{[[SCon{c, t}]]} : A.Ans}
  %Equal.sym(Maybe<&2, String>, A.bare(tx(t, A.TNil{}), SCon{c, SNil{}}), Some{String.append(SCon{c, SNil{}}, t)}, bare_tx(t, SCon{c, SNil{}})) : {A.rows([A.row_of([_], [])], []) == A.Parsed{[[SCon{c, t}]]} : A.Ans}
  {==}

def Laws.abnf_clean_input_is_one_field(sep, s, h):
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %Equal.sym(A.Tok, A.tokens(sep, SCon{c, t}), tx(SCon{c, t}, A.TNil{}), tok_clean(sep, SCon{c, t}, h)) : {A.rows(A.rows_map(A.field_map(A.recs(_, A.RRec{}, A.TNil{}, []))), []) == Laws.CleanAnswer(SCon{c, t}) : A.Ans}
      one_cons(c, t)

# ---- abnf_separator_makes_two_fields ----
def tok_app(+sep: U32, +a: String, +rest: String, ha: Laws.Clean(sep, a)) -> {A.tokens(sep, String.append(a, rest)) == tx(a, A.tokens(sep, rest)) : A.Tok}:
  match a:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, t}:
      (hse, hqu, hcr, hlf, ht) = ha
      %Equal.sym(Bool, Cmp.is_eq(U32.cmp(x, 10)), False{}, hlf) : {A.TCon{A.kind_go(_, Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34)), Chr{x}), A.tokens(sep, String.append(t, rest))} == A.TCon{A.KText{Chr{x}}, tx(t, A.tokens(sep, rest))} : A.Tok}
      %Equal.sym(Bool, Cmp.is_eq(U32.cmp(x, 13)), False{}, hcr) : {A.TCon{A.kind_go(False{}, _, Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34)), Chr{x}), A.tokens(sep, String.append(t, rest))} == A.TCon{A.KText{Chr{x}}, tx(t, A.tokens(sep, rest))} : A.Tok}
      %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, x)), False{}, hse) : {A.TCon{A.kind_go(False{}, False{}, _, Cmp.is_eq(U32.cmp(x, 34)), Chr{x}), A.tokens(sep, String.append(t, rest))} == A.TCon{A.KText{Chr{x}}, tx(t, A.tokens(sep, rest))} : A.Tok}
      %Equal.sym(Bool, Cmp.is_eq(U32.cmp(x, 34)), False{}, hqu) : {A.TCon{A.kind_go(False{}, False{}, False{}, _, Chr{x}), A.tokens(sep, String.append(t, rest))} == A.TCon{A.KText{Chr{x}}, tx(t, A.tokens(sep, rest))} : A.Tok}
      %tok_app(sep, t, rest, ht) : {A.TCon{A.KText{Chr{x}}, A.tokens(sep, String.append(t, rest))} == A.TCon{A.KText{Chr{x}}, _} : A.Tok}
      {==}

def tok_two(+sep: U32, hl: {U32.is_eq(sep, 10) == False{} : Bool}, hc: {U32.is_eq(sep, 13) == False{} : Bool}, +a: String, +b: String, ha: Laws.Clean(sep, a), hb: Laws.Clean(sep, b)) -> {A.tokens(sep, String.append(String.append(a, SCon{Chr{sep}, SNil{}}), b)) == tx(a, A.TCon{A.KSep{Chr{sep}}, tx(b, A.TNil{})}) : A.Tok}:
  %MS.internal_append_assoc(a, SCon{Chr{sep}, SNil{}}, b) : {A.tokens(sep, _) == tx(a, A.TCon{A.KSep{Chr{sep}}, tx(b, A.TNil{})}) : A.Tok}
  %Equal.sym(A.Tok, A.tokens(sep, String.append(a, SCon{Chr{sep}, b})), tx(a, A.tokens(sep, SCon{Chr{sep}, b})), tok_app(sep, a, SCon{Chr{sep}, b}, ha)) : {_ == tx(a, A.TCon{A.KSep{Chr{sep}}, tx(b, A.TNil{})}) : A.Tok}
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, 10)), False{}, hl) : {tx(a, A.TCon{A.kind_go(_, Cmp.is_eq(U32.cmp(sep, 13)), Cmp.is_eq(U32.cmp(sep, sep)), Cmp.is_eq(U32.cmp(sep, 34)), Chr{sep}), A.tokens(sep, b)}) == tx(a, A.TCon{A.KSep{Chr{sep}}, tx(b, A.TNil{})}) : A.Tok}
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, 13)), False{}, hc) : {tx(a, A.TCon{A.kind_go(False{}, _, Cmp.is_eq(U32.cmp(sep, sep)), Cmp.is_eq(U32.cmp(sep, 34)), Chr{sep}), A.tokens(sep, b)}) == tx(a, A.TCon{A.KSep{Chr{sep}}, tx(b, A.TNil{})}) : A.Tok}
  %MS.internal_u32_cmp_refl(sep) : {tx(a, A.TCon{A.kind_go(False{}, False{}, Cmp.is_eq(_), Cmp.is_eq(U32.cmp(sep, 34)), Chr{sep}), A.tokens(sep, b)}) == tx(a, A.TCon{A.KSep{Chr{sep}}, tx(b, A.TNil{})}) : A.Tok}
  %Equal.sym(A.Tok, A.tokens(sep, b), tx(b, A.TNil{}), tok_clean(sep, b, hb)) : {tx(a, A.TCon{A.KSep{Chr{sep}}, _}) == tx(a, A.TCon{A.KSep{Chr{sep}}, tx(b, A.TNil{})}) : A.Tok}
  {==}

def recs_sep(+s: String, +c: Char, +b: String, +cur: A.Tok, +done: List<&2, A.Tok>) -> {A.recs(tx(s, A.TCon{A.KSep{c}, tx(b, A.TNil{})}), A.RRec{}, cur, done) == List.reverse(&2, A.Tok, A.add_rec(push(b, A.TCon{A.KSep{c}, push(s, cur)}), done)) : List<&2, A.Tok>}:
  match s:
    case SNil{}:
      recs_tx(b, A.TCon{A.KSep{c}, cur}, done)
    case SCon{d, t}:
      recs_sep(t, c, b, A.TCon{A.KText{d}, cur}, done)

def fields_sep(+s: String, +c: Char, +b: String, +cur: A.Tok, +done: List<&2, A.Tok>) -> {A.fields(tx(s, A.TCon{A.KSep{c}, tx(b, A.TNil{})}), A.FOut{}, cur, done) == List.reverse(&2, A.Tok, A.whole(push(b, A.TNil{}), A.whole(push(s, cur), done))) : List<&2, A.Tok>}:
  match s:
    case SNil{}:
      fields_tx(b, A.TNil{}, A.whole(cur, done))
    case SCon{d, t}:
      fields_sep(t, c, b, A.TCon{A.KText{d}, cur}, done)

def dec_tx(+s: String) -> {A.decode(tx(s, A.TNil{})) == Some{s} : Maybe<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %Equal.sym(Maybe<&2, String>, A.bare(tx(t, A.TNil{}), SCon{c, SNil{}}), Some{String.append(SCon{c, SNil{}}, t)}, bare_tx(t, SCon{c, SNil{}})) : {_ == Some{SCon{c, t}} : Maybe<&2, String>}
      {==}

def Laws.abnf_separator_makes_two_fields(sep, hl, hc, a, b, ha, hb):
  %Equal.sym(A.Tok, A.tokens(sep, String.append(String.append(a, SCon{Chr{sep}, SNil{}}), b)), tx(a, A.TCon{A.KSep{Chr{sep}}, tx(b, A.TNil{})}), tok_two(sep, hl, hc, a, b, ha, hb)) : {A.rows(A.rows_map(A.field_map(A.recs(_, A.RRec{}, A.TNil{}, []))), []) == A.Parsed{Con{Con{a, Con{b, Nil{}}}, Nil{}}} : A.Ans}
  %Equal.sym(List<&2, A.Tok>, A.recs(tx(a, A.TCon{A.KSep{Chr{sep}}, tx(b, A.TNil{})}), A.RRec{}, A.TNil{}, []), List.reverse(&2, A.Tok, A.add_rec(push(b, A.TCon{A.KSep{Chr{sep}}, push(a, A.TNil{})}), [])), recs_sep(a, Chr{sep}, b, A.TNil{}, [])) : {A.rows(A.rows_map(A.field_map(_)), []) == A.Parsed{Con{Con{a, Con{b, Nil{}}}, Nil{}}} : A.Ans}
  %Equal.sym(List<&2, A.Tok>, A.add_rec(push(b, A.TCon{A.KSep{Chr{sep}}, push(a, A.TNil{})}), []), A.whole(push(b, A.TCon{A.KSep{Chr{sep}}, push(a, A.TNil{})}), []), add_push(b, A.KSep{Chr{sep}}, push(a, A.TNil{}), [])) : {A.rows(A.rows_map(A.field_map(List.reverse(&2, A.Tok, _))), []) == A.Parsed{Con{Con{a, Con{b, Nil{}}}, Nil{}}} : A.Ans}
  %Equal.sym(A.Tok, A.rev_tok(push(b, A.TCon{A.KSep{Chr{sep}}, push(a, A.TNil{})}), A.TNil{}), A.rev_tok(A.TCon{A.KSep{Chr{sep}}, push(a, A.TNil{})}, tx(b, A.TNil{})), rt_push(b, A.TCon{A.KSep{Chr{sep}}, push(a, A.TNil{})}, A.TNil{})) : {A.rows([A.row_of(A.text_map(A.fields(_, A.FOut{}, A.TNil{}, [])), [])], []) == A.Parsed{[[a, b]]} : A.Ans}
  %Equal.sym(A.Tok, A.rev_tok(push(a, A.TNil{}), A.TCon{A.KSep{Chr{sep}}, tx(b, A.TNil{})}), tx(a, A.TCon{A.KSep{Chr{sep}}, tx(b, A.TNil{})}), rt_push(a, A.TNil{}, A.TCon{A.KSep{Chr{sep}}, tx(b, A.TNil{})})) : {A.rows([A.row_of(A.text_map(A.fields(_, A.FOut{}, A.TNil{}, [])), [])], []) == A.Parsed{[[a, b]]} : A.Ans}
  %Equal.sym(List<&2, A.Tok>, A.fields(tx(a, A.TCon{A.KSep{Chr{sep}}, tx(b, A.TNil{})}), A.FOut{}, A.TNil{}, []), List.reverse(&2, A.Tok, A.whole(push(b, A.TNil{}), A.whole(push(a, A.TNil{}), []))), fields_sep(a, Chr{sep}, b, A.TNil{}, [])) : {A.rows([A.row_of(A.text_map(_), [])], []) == A.Parsed{[[a, b]]} : A.Ans}





  %Equal.sym(A.Tok, A.rev_tok(push(a, A.TNil{}), A.TNil{}), tx(a, A.TNil{}), rt_push(a, A.TNil{}, A.TNil{})) : {A.rows([A.row_of([A.decode(_), A.decode(A.rev_tok(push(b, A.TNil{}), A.TNil{}))], [])], []) == A.Parsed{[[a, b]]} : A.Ans}
  %Equal.sym(A.Tok, A.rev_tok(push(b, A.TNil{}), A.TNil{}), tx(b, A.TNil{}), rt_push(b, A.TNil{}, A.TNil{})) : {A.rows([A.row_of([A.decode(tx(a, A.TNil{})), A.decode(_)], [])], []) == A.Parsed{[[a, b]]} : A.Ans}
  %Equal.sym(Maybe<&2, String>, A.decode(tx(a, A.TNil{})), Some{a}, dec_tx(a)) : {A.rows([A.row_of([_, A.decode(tx(b, A.TNil{}))], [])], []) == A.Parsed{[[a, b]]} : A.Ans}
  %Equal.sym(Maybe<&2, String>, A.decode(tx(b, A.TNil{})), Some{b}, dec_tx(b)) : {A.rows([A.row_of([Some{a}, _], [])], []) == A.Parsed{[[a, b]]} : A.Ans}
  {==}

# ---- abnf_quoted_field_is_its_content ----
def tk(+sep: U32, +s: String, +r: A.Tok) -> A.Tok:
  match s:
    case SNil{}:
      r
    case SCon{c, t}:
      A.TCon{A.kind(sep, c), tk(sep, t, r)}

def pk(+sep: U32, +s: String, +cur: A.Tok) -> A.Tok:
  match s:
    case SNil{}:
      cur
    case SCon{c, t}:
      pk(sep, t, A.TCon{A.kind(sep, c), cur})

def tok_tk(+sep: U32, +s: String, +r: String) -> {A.tokens(sep, String.append(s, r)) == tk(sep, s, A.tokens(sep, r)) : A.Tok}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %tok_tk(sep, t, r) : {A.TCon{A.kind(sep, c), A.tokens(sep, String.append(t, r))} == A.TCon{A.kind(sep, c), _} : A.Tok}
      {==}

def rt_pk(+sep: U32, +s: String, +cur: A.Tok, +acc: A.Tok) -> {A.rev_tok(pk(sep, s, cur), acc) == A.rev_tok(cur, tk(sep, s, acc)) : A.Tok}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      rt_pk(sep, t, A.TCon{A.kind(sep, c), cur}, acc)

def recs_step(+lf: Bool, +cr: Bool, +sp: Bool, +c: Char, +rest: A.Tok, +cur: A.Tok, +done: List<&2, A.Tok>) -> {A.recs(A.TCon{A.kind_go(lf, cr, sp, False{}, c), rest}, A.REsc{}, cur, done) == A.recs(rest, A.REsc{}, A.TCon{A.kind_go(lf, cr, sp, False{}, c), cur}, done) : List<&2, A.Tok>}:
  match lf:
    case True{}:
      {==}
    case False{}:
      match cr:
        case True{}:
          {==}
        case False{}:
          match sp:
            case True{}:
              {==}
            case False{}:
              {==}

def fields_step(+lf: Bool, +cr: Bool, +sp: Bool, +c: Char, +rest: A.Tok, +cur: A.Tok, +done: List<&2, A.Tok>) -> {A.fields(A.TCon{A.kind_go(lf, cr, sp, False{}, c), rest}, A.FIn{}, cur, done) == A.fields(rest, A.FIn{}, A.TCon{A.kind_go(lf, cr, sp, False{}, c), cur}, done) : List<&2, A.Tok>}:
  match lf:
    case True{}:
      {==}
    case False{}:
      match cr:
        case True{}:
          {==}
        case False{}:
          match sp:
            case True{}:
              {==}
            case False{}:
              {==}

def recs_step2(+lf: Bool, +cr: Bool, +sp: Bool, +q: Bool, +c: Char, +rest: A.Tok, +cur: A.Tok, +done: List<&2, A.Tok>, hq: {q == False{} : Bool}) -> {A.recs(A.TCon{A.kind_go(lf, cr, sp, q, c), rest}, A.REsc{}, cur, done) == A.recs(rest, A.REsc{}, A.TCon{A.kind_go(lf, cr, sp, q, c), cur}, done) : List<&2, A.Tok>}:
  match q:
    case True{}:
      Empty.absurd({A.recs(A.TCon{A.kind_go(lf, cr, sp, True{}, c), rest}, A.REsc{}, cur, done) == A.recs(rest, A.REsc{}, A.TCon{A.kind_go(lf, cr, sp, True{}, c), cur}, done) : List<&2, A.Tok>}, MS.internal_false_ne_true(Equal.sym(Bool, True{}, False{}, hq)))
    case False{}:
      recs_step(lf, cr, sp, c, rest, cur, done)

def recs_esc(+sep: U32, +s: String, h: Laws.NoQuote(s), +R: A.Tok, +cur: A.Tok, +done: List<&2, A.Tok>) -> {A.recs(tk(sep, s, R), A.REsc{}, cur, done) == A.recs(R, A.REsc{}, pk(sep, s, cur), done) : List<&2, A.Tok>}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, t}:
      (hx, ht) = h
      %Equal.sym(List<&2, A.Tok>, A.recs(A.TCon{A.kind_go(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34)), Chr{x}), tk(sep, t, R)}, A.REsc{}, cur, done), A.recs(tk(sep, t, R), A.REsc{}, A.TCon{A.kind_go(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34)), Chr{x}), cur}, done), recs_step2(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34)), Chr{x}, tk(sep, t, R), cur, done, hx)) : {_ == A.recs(R, A.REsc{}, pk(sep, SCon{Chr{x}, t}, cur), done) : List<&2, A.Tok>}
      %Equal.sym(List<&2, A.Tok>, A.recs(tk(sep, t, R), A.REsc{}, A.TCon{A.kind_go(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34)), Chr{x}), cur}, done), A.recs(R, A.REsc{}, pk(sep, t, A.TCon{A.kind_go(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34)), Chr{x}), cur}), done), recs_esc(sep, t, ht, R, A.TCon{A.kind_go(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34)), Chr{x}), cur}, done)) : {_ == A.recs(R, A.REsc{}, pk(sep, t, A.TCon{A.kind_go(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34)), Chr{x}), cur}), done) : List<&2, A.Tok>}
      {==}

def tok_q(+sep: U32, +hq: {U32.is_eq(sep, 34) == False{} : Bool}, +s: String) -> {A.tokens(sep, String.append(String.append("\"", s), "\"")) == A.TCon{A.KQuote{}, tk(sep, s, A.TCon{A.KQuote{}, A.TNil{}})} : A.Tok}:
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, 34)), False{}, hq) : {A.TCon{A.kind_go(False{}, False{}, _, True{}, '"'), A.tokens(sep, String.append(s, "\""))} == A.TCon{A.KQuote{}, tk(sep, s, A.TCon{A.KQuote{}, A.TNil{}})} : A.Tok}
  %Equal.sym(A.Tok, A.tokens(sep, String.append(s, "\"")), tk(sep, s, A.tokens(sep, "\"")), tok_tk(sep, s, "\"")) : {A.TCon{A.KQuote{}, _} == A.TCon{A.KQuote{}, tk(sep, s, A.TCon{A.KQuote{}, A.TNil{}})} : A.Tok}
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, 34)), False{}, hq) : {A.TCon{A.KQuote{}, tk(sep, s, A.TCon{A.kind_go(False{}, False{}, _, True{}, '"'), A.TNil{}})} == A.TCon{A.KQuote{}, tk(sep, s, A.TCon{A.KQuote{}, A.TNil{}})} : A.Tok}
  {==}

def fields_step2(+lf: Bool, +cr: Bool, +sp: Bool, +q: Bool, +c: Char, +rest: A.Tok, +cur: A.Tok, +done: List<&2, A.Tok>, hq: {q == False{} : Bool}) -> {A.fields(A.TCon{A.kind_go(lf, cr, sp, q, c), rest}, A.FIn{}, cur, done) == A.fields(rest, A.FIn{}, A.TCon{A.kind_go(lf, cr, sp, q, c), cur}, done) : List<&2, A.Tok>}:
  match q:
    case True{}:
      Empty.absurd({A.fields(A.TCon{A.kind_go(lf, cr, sp, True{}, c), rest}, A.FIn{}, cur, done) == A.fields(rest, A.FIn{}, A.TCon{A.kind_go(lf, cr, sp, True{}, c), cur}, done) : List<&2, A.Tok>}, MS.internal_false_ne_true(Equal.sym(Bool, True{}, False{}, hq)))
    case False{}:
      fields_step(lf, cr, sp, c, rest, cur, done)

def fields_in(+sep: U32, +s: String, h: Laws.NoQuote(s), +R: A.Tok, +cur: A.Tok, +done: List<&2, A.Tok>) -> {A.fields(tk(sep, s, R), A.FIn{}, cur, done) == A.fields(R, A.FIn{}, pk(sep, s, cur), done) : List<&2, A.Tok>}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, t}:
      (hx, ht) = h
      %Equal.sym(List<&2, A.Tok>, A.fields(A.TCon{A.kind_go(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34)), Chr{x}), tk(sep, t, R)}, A.FIn{}, cur, done), A.fields(tk(sep, t, R), A.FIn{}, A.TCon{A.kind_go(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34)), Chr{x}), cur}, done), fields_step2(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34)), Chr{x}, tk(sep, t, R), cur, done, hx)) : {_ == A.fields(R, A.FIn{}, pk(sep, SCon{Chr{x}, t}, cur), done) : List<&2, A.Tok>}
      %Equal.sym(List<&2, A.Tok>, A.fields(tk(sep, t, R), A.FIn{}, A.TCon{A.kind_go(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34)), Chr{x}), cur}, done), A.fields(R, A.FIn{}, pk(sep, t, A.TCon{A.kind_go(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34)), Chr{x}), cur}), done), fields_in(sep, t, ht, R, A.TCon{A.kind_go(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34)), Chr{x}), cur}, done)) : {_ == A.fields(R, A.FIn{}, pk(sep, SCon{Chr{x}, t}, cur), done) : List<&2, A.Tok>}
      {==}

def esc_step(+lf: Bool, +cr: Bool, +sp: Bool, +x: U32, +rest: A.Tok, +txt: String, e1: {Cmp.is_eq(U32.cmp(x, 10)) == lf : Bool}, e2: {Cmp.is_eq(U32.cmp(x, 13)) == cr : Bool}) -> {A.esc(A.TCon{A.kind_go(lf, cr, sp, False{}, Chr{x}), rest}, A.EIn{}, txt) == A.esc(rest, A.EIn{}, String.append(txt, SCon{Chr{x}, SNil{}})) : Maybe<&2, String>}:
  match lf:
    case True{}:
      %Equal.sym(U32, x, 10, MS.u32_eq_of_is_eq(x, 10, e1)) : {A.esc(rest, A.EIn{}, String.append(txt, SCon{Chr{10}, SNil{}})) == A.esc(rest, A.EIn{}, String.append(txt, SCon{Chr{_}, SNil{}})) : Maybe<&2, String>}
      {==}
    case False{}:
      match cr:
        case True{}:
          %Equal.sym(U32, x, 13, MS.u32_eq_of_is_eq(x, 13, e2)) : {A.esc(rest, A.EIn{}, String.append(txt, SCon{Chr{13}, SNil{}})) == A.esc(rest, A.EIn{}, String.append(txt, SCon{Chr{_}, SNil{}})) : Maybe<&2, String>}
          {==}
        case False{}:
          match sp:
            case True{}:
              {==}
            case False{}:
              {==}

def esc_step2(+lf: Bool, +cr: Bool, +sp: Bool, +q: Bool, +x: U32, +rest: A.Tok, +txt: String, hq: {q == False{} : Bool}) -> {A.esc(A.TCon{A.kind_go(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), sp, q, Chr{x}), rest}, A.EIn{}, txt) == A.esc(rest, A.EIn{}, String.append(txt, SCon{Chr{x}, SNil{}})) : Maybe<&2, String>}:
  match q:
    case True{}:
      Empty.absurd({A.esc(A.TCon{A.kind_go(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), sp, True{}, Chr{x}), rest}, A.EIn{}, txt) == A.esc(rest, A.EIn{}, String.append(txt, SCon{Chr{x}, SNil{}})) : Maybe<&2, String>}, MS.internal_false_ne_true(Equal.sym(Bool, True{}, False{}, hq)))
    case False{}:
      esc_step(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), sp, x, rest, txt, {==}, {==})

def esc_walk(+sep: U32, +s: String, h: Laws.NoQuote(s), +R: A.Tok, +txt: String) -> {A.esc(tk(sep, s, R), A.EIn{}, txt) == A.esc(R, A.EIn{}, String.append(txt, s)) : Maybe<&2, String>}:
  match s:
    case SNil{}:
      %MS.internal_append_nil(txt) : {A.esc(R, A.EIn{}, txt) == A.esc(R, A.EIn{}, _) : Maybe<&2, String>}
      {==}
    case SCon{Chr{+x}, t}:
      (hx, ht) = h
      %Equal.sym(Maybe<&2, String>, A.esc(A.TCon{A.kind_go(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34)), Chr{x}), tk(sep, t, R)}, A.EIn{}, txt), A.esc(tk(sep, t, R), A.EIn{}, String.append(txt, SCon{Chr{x}, SNil{}})), esc_step2(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34)), x, tk(sep, t, R), txt, hx)) : {_ == A.esc(R, A.EIn{}, String.append(txt, SCon{Chr{x}, t})) : Maybe<&2, String>}
      %Equal.sym(Maybe<&2, String>, A.esc(tk(sep, t, R), A.EIn{}, String.append(txt, SCon{Chr{x}, SNil{}})), A.esc(R, A.EIn{}, String.append(String.append(txt, SCon{Chr{x}, SNil{}}), t)), esc_walk(sep, t, ht, R, String.append(txt, SCon{Chr{x}, SNil{}}))) : {_ == A.esc(R, A.EIn{}, String.append(txt, SCon{Chr{x}, t})) : Maybe<&2, String>}
      %MS.internal_append_assoc(txt, SCon{Chr{x}, SNil{}}, t) : {A.esc(R, A.EIn{}, _) == A.esc(R, A.EIn{}, String.append(txt, SCon{Chr{x}, t})) : Maybe<&2, String>}
      {==}

def dup_step(+x: U32, +t: String, +hx: {U32.is_eq(x, 34) == False{} : Bool}, p: Laws.NoQuote(t) & Laws.NoQuote(t)) -> Laws.NoQuote(SCon{Chr{x}, t}) & Laws.NoQuote(SCon{Chr{x}, t}):
  (h1, h2) = p
  ((hx, h1), (hx, h2))

def nq_dup(+s: String, h: Laws.NoQuote(s)) -> Laws.NoQuote(s) & Laws.NoQuote(s):
  match s:
    case SNil{}:
      (Unit{}, Unit{})
    case SCon{Chr{+x}, t}:
      (hx, ht) = h
      dup_step(x, t, hx, nq_dup(t, ht))

def quoted_body(+sep: U32, +hq: {U32.is_eq(sep, 34) == False{} : Bool}, +s: String, h: Laws.NoQuote(s), h2: Laws.NoQuote(s), h3: Laws.NoQuote(s)) -> {A.parse_sep(sep, String.append(String.append("\"", s), "\"")) == A.Parsed{Con{Con{s, Nil{}}, Nil{}}} : A.Ans}:
  %Equal.sym(A.Tok, A.tokens(sep, String.append(String.append("\"", s), "\"")), A.TCon{A.KQuote{}, tk(sep, s, A.TCon{A.KQuote{}, A.TNil{}})}, tok_q(sep, hq, s)) : {A.rows(A.rows_map(A.field_map(A.recs(_, A.RRec{}, A.TNil{}, []))), []) == A.Parsed{Con{Con{s, Nil{}}, Nil{}}} : A.Ans}
  %Equal.sym(List<&2, A.Tok>, A.recs(tk(sep, s, A.TCon{A.KQuote{}, A.TNil{}}), A.REsc{}, A.TCon{A.KQuote{}, A.TNil{}}, []), A.recs(A.TCon{A.KQuote{}, A.TNil{}}, A.REsc{}, pk(sep, s, A.TCon{A.KQuote{}, A.TNil{}}), []), recs_esc(sep, s, h2, A.TCon{A.KQuote{}, A.TNil{}}, A.TCon{A.KQuote{}, A.TNil{}}, [])) : {A.rows(A.rows_map(A.field_map(_)), []) == A.Parsed{Con{Con{s, Nil{}}, Nil{}}} : A.Ans}
  %Equal.sym(A.Tok, A.rev_tok(pk(sep, s, A.TCon{A.KQuote{}, A.TNil{}}), A.TCon{A.KQuote{}, A.TNil{}}), A.rev_tok(A.TCon{A.KQuote{}, A.TNil{}}, tk(sep, s, A.TCon{A.KQuote{}, A.TNil{}})), rt_pk(sep, s, A.TCon{A.KQuote{}, A.TNil{}}, A.TCon{A.KQuote{}, A.TNil{}})) : {A.rows([A.row_of(A.text_map(A.fields(_, A.FOut{}, A.TNil{}, [])), [])], []) == A.Parsed{[[s]]} : A.Ans}
  %Equal.sym(List<&2, A.Tok>, A.fields(tk(sep, s, A.TCon{A.KQuote{}, A.TNil{}}), A.FIn{}, A.TCon{A.KQuote{}, A.TNil{}}, []), A.fields(A.TCon{A.KQuote{}, A.TNil{}}, A.FIn{}, pk(sep, s, A.TCon{A.KQuote{}, A.TNil{}}), []), fields_in(sep, s, h, A.TCon{A.KQuote{}, A.TNil{}}, A.TCon{A.KQuote{}, A.TNil{}}, [])) : {A.rows([A.row_of(A.text_map(_), [])], []) == A.Parsed{[[s]]} : A.Ans}
  %Equal.sym(A.Tok, A.rev_tok(pk(sep, s, A.TCon{A.KQuote{}, A.TNil{}}), A.TCon{A.KQuote{}, A.TNil{}}), A.rev_tok(A.TCon{A.KQuote{}, A.TNil{}}, tk(sep, s, A.TCon{A.KQuote{}, A.TNil{}})), rt_pk(sep, s, A.TCon{A.KQuote{}, A.TNil{}}, A.TCon{A.KQuote{}, A.TNil{}})) : {A.rows([A.row_of([A.decode(_)], [])], []) == A.Parsed{[[s]]} : A.Ans}
  %Equal.sym(Maybe<&2, String>, A.esc(tk(sep, s, A.TCon{A.KQuote{}, A.TNil{}}), A.EIn{}, SNil{}), A.esc(A.TCon{A.KQuote{}, A.TNil{}}, A.EIn{}, String.append(SNil{}, s)), esc_walk(sep, s, h3, A.TCon{A.KQuote{}, A.TNil{}}, SNil{})) : {A.rows([A.row_of([_], [])], []) == A.Parsed{[[s]]} : A.Ans}
  {==}

def quoted_2(+sep: U32, +hq: {U32.is_eq(sep, 34) == False{} : Bool}, +s: String, h: Laws.NoQuote(s), q: Laws.NoQuote(s) & Laws.NoQuote(s)) -> {A.parse_sep(sep, String.append(String.append("\"", s), "\"")) == A.Parsed{Con{Con{s, Nil{}}, Nil{}}} : A.Ans}:
  (h2, h3) = q
  quoted_body(sep, hq, s, h, h2, h3)

def quoted_1(+sep: U32, +hq: {U32.is_eq(sep, 34) == False{} : Bool}, +s: String, p: Laws.NoQuote(s) & Laws.NoQuote(s)) -> {A.parse_sep(sep, String.append(String.append("\"", s), "\"")) == A.Parsed{Con{Con{s, Nil{}}, Nil{}}} : A.Ans}:
  (h, h2) = p
  quoted_2(sep, hq, s, h, nq_dup(s, h2))

def Laws.abnf_quoted_field_is_its_content(sep, hq, s, h):
  quoted_1(sep, hq, s, nq_dup(s, h))

# ---- abnf_doubled_quote_is_one_quote ----
def dq_bool(+p: Bool, +sa: Bool, +sb: Bool, hp: {p == False{} : Bool}) -> {A.decode(A.TCon{A.kind_go(False{}, False{}, p, True{}, '"'), A.TCon{A.kind_go(False{}, False{}, sa, False{}, 'a'), A.TCon{A.kind_go(False{}, False{}, p, True{}, '"'), A.TCon{A.kind_go(False{}, False{}, p, True{}, '"'), A.TCon{A.kind_go(False{}, False{}, sb, False{}, 'b'), A.TCon{A.kind_go(False{}, False{}, p, True{}, '"'), A.TNil{}}}}}}}) == Some{"a\"b"} : Maybe<&2, String>}:
  match p:
    case True{}:
      Empty.absurd({A.decode(A.TCon{A.kind_go(False{}, False{}, True{}, True{}, '"'), A.TCon{A.kind_go(False{}, False{}, sa, False{}, 'a'), A.TCon{A.kind_go(False{}, False{}, True{}, True{}, '"'), A.TCon{A.kind_go(False{}, False{}, True{}, True{}, '"'), A.TCon{A.kind_go(False{}, False{}, sb, False{}, 'b'), A.TCon{A.kind_go(False{}, False{}, True{}, True{}, '"'), A.TNil{}}}}}}}) == Some{"a\"b"} : Maybe<&2, String>}, MS.internal_false_ne_true(Equal.sym(Bool, True{}, False{}, hp)))
    case False{}:
      match sa:
        case True{}:
          match sb:
            case True{}:
              {==}
            case False{}:
              {==}
        case False{}:
          match sb:
            case True{}:
              {==}
            case False{}:
              {==}

def Laws.abnf_doubled_quote_is_one_quote(sep, hq):
  dq_bool(Cmp.is_eq(U32.cmp(sep, 34)), Cmp.is_eq(U32.cmp(sep, 97)), Cmp.is_eq(U32.cmp(sep, 98)), hq)

# ---- a newline at a record end ----
#
# Parity lemmas about quote tokens (bnot, par, par_flip, pf_ft, pf_tf), used by
# the proofs of the laws that follow.

# ---- abnf_blank_line_adds_nothing ----
def tapp(+ts: A.Tok, +r: A.Tok) -> A.Tok:
  match ts:
    case A.TNil{}:
      r
    case A.TCon{k, t}:
      A.TCon{k, tapp(t, r)}

def QF(ts: A.Tok) -> Type:
  match ts:
    case A.TNil{}:
      Unit
    case A.TCon{A.KQuote{}, t}:
      Empty
    case A.TCon{A.KSep{c}, t}:
      QF(t)
    case A.TCon{A.KCr{}, t}:
      QF(t)
    case A.TCon{A.KLf{}, t}:
      QF(t)
    case A.TCon{A.KText{c}, t}:
      QF(t)

def isE(+ph: A.RPh) -> Bool:
  match ph:
    case A.RRec{}:
      False{}
    case A.REsc{}:
      True{}
    case A.REscQ{}:
      False{}
    case A.RCr{}:
      False{}

def blank_walk(+ts: A.Tok, h: QF(ts), +R: A.Tok, +ph: A.RPh, hp: {isE(ph) == False{} : Bool}, +cur: A.Tok, +done: List<&2, A.Tok>) -> {A.recs(tapp(ts, A.TCon{A.KLf{}, A.TCon{A.KLf{}, R}}), ph, cur, done) == A.recs(tapp(ts, A.TCon{A.KLf{}, R}), ph, cur, done) : List<&2, A.Tok>}:
  match ts ph:
    case A.TNil{} A.RRec{}:
      {==}
    case A.TNil{} A.REsc{}:
      Empty.absurd({A.recs(tapp(A.TNil{}, A.TCon{A.KLf{}, A.TCon{A.KLf{}, R}}), A.REsc{}, cur, done) == A.recs(tapp(A.TNil{}, A.TCon{A.KLf{}, R}), A.REsc{}, cur, done) : List<&2, A.Tok>}, MS.internal_false_ne_true(Equal.sym(Bool, True{}, False{}, hp)))
    case A.TNil{} A.REscQ{}:
      {==}
    case A.TNil{} A.RCr{}:
      {==}
    case A.TCon{A.KSep{c}, t} A.RRec{}:
      blank_walk(t, h, R, A.RRec{}, {==}, A.TCon{A.KSep{c}, cur}, done)
    case A.TCon{A.KCr{}, t} A.RRec{}:
      blank_walk(t, h, R, A.RCr{}, {==}, cur, done)
    case A.TCon{A.KLf{}, t} A.RRec{}:
      blank_walk(t, h, R, A.RRec{}, {==}, A.TNil{}, A.add_rec(cur, done))
    case A.TCon{A.KText{c}, t} A.RRec{}:
      blank_walk(t, h, R, A.RRec{}, {==}, A.TCon{A.KText{c}, cur}, done)
    case A.TCon{A.KQuote{}, t} A.RRec{}:
      Empty.absurd({A.recs(tapp(A.TCon{A.KQuote{}, t}, A.TCon{A.KLf{}, A.TCon{A.KLf{}, R}}), A.RRec{}, cur, done) == A.recs(tapp(A.TCon{A.KQuote{}, t}, A.TCon{A.KLf{}, R}), A.RRec{}, cur, done) : List<&2, A.Tok>}, h)
    case A.TCon{A.KSep{c}, t} A.REsc{}:
      Empty.absurd({A.recs(tapp(A.TCon{A.KSep{c}, t}, A.TCon{A.KLf{}, A.TCon{A.KLf{}, R}}), A.REsc{}, cur, done) == A.recs(tapp(A.TCon{A.KSep{c}, t}, A.TCon{A.KLf{}, R}), A.REsc{}, cur, done) : List<&2, A.Tok>}, MS.internal_false_ne_true(Equal.sym(Bool, True{}, False{}, hp)))
    case A.TCon{A.KCr{}, t} A.REsc{}:
      Empty.absurd({A.recs(tapp(A.TCon{A.KCr{}, t}, A.TCon{A.KLf{}, A.TCon{A.KLf{}, R}}), A.REsc{}, cur, done) == A.recs(tapp(A.TCon{A.KCr{}, t}, A.TCon{A.KLf{}, R}), A.REsc{}, cur, done) : List<&2, A.Tok>}, MS.internal_false_ne_true(Equal.sym(Bool, True{}, False{}, hp)))
    case A.TCon{A.KLf{}, t} A.REsc{}:
      Empty.absurd({A.recs(tapp(A.TCon{A.KLf{}, t}, A.TCon{A.KLf{}, A.TCon{A.KLf{}, R}}), A.REsc{}, cur, done) == A.recs(tapp(A.TCon{A.KLf{}, t}, A.TCon{A.KLf{}, R}), A.REsc{}, cur, done) : List<&2, A.Tok>}, MS.internal_false_ne_true(Equal.sym(Bool, True{}, False{}, hp)))
    case A.TCon{A.KText{c}, t} A.REsc{}:
      Empty.absurd({A.recs(tapp(A.TCon{A.KText{c}, t}, A.TCon{A.KLf{}, A.TCon{A.KLf{}, R}}), A.REsc{}, cur, done) == A.recs(tapp(A.TCon{A.KText{c}, t}, A.TCon{A.KLf{}, R}), A.REsc{}, cur, done) : List<&2, A.Tok>}, MS.internal_false_ne_true(Equal.sym(Bool, True{}, False{}, hp)))
    case A.TCon{A.KQuote{}, t} A.REsc{}:
      Empty.absurd({A.recs(tapp(A.TCon{A.KQuote{}, t}, A.TCon{A.KLf{}, A.TCon{A.KLf{}, R}}), A.REsc{}, cur, done) == A.recs(tapp(A.TCon{A.KQuote{}, t}, A.TCon{A.KLf{}, R}), A.REsc{}, cur, done) : List<&2, A.Tok>}, MS.internal_false_ne_true(Equal.sym(Bool, True{}, False{}, hp)))
    case A.TCon{A.KSep{c}, t} A.REscQ{}:
      blank_walk(t, h, R, A.RRec{}, {==}, A.TCon{A.KSep{c}, cur}, done)
    case A.TCon{A.KCr{}, t} A.REscQ{}:
      blank_walk(t, h, R, A.RCr{}, {==}, cur, done)
    case A.TCon{A.KLf{}, t} A.REscQ{}:
      blank_walk(t, h, R, A.RRec{}, {==}, A.TNil{}, A.add_rec(cur, done))
    case A.TCon{A.KText{c}, t} A.REscQ{}:
      blank_walk(t, h, R, A.RRec{}, {==}, A.TCon{A.KText{c}, cur}, done)
    case A.TCon{A.KQuote{}, t} A.REscQ{}:
      Empty.absurd({A.recs(tapp(A.TCon{A.KQuote{}, t}, A.TCon{A.KLf{}, A.TCon{A.KLf{}, R}}), A.REscQ{}, cur, done) == A.recs(tapp(A.TCon{A.KQuote{}, t}, A.TCon{A.KLf{}, R}), A.REscQ{}, cur, done) : List<&2, A.Tok>}, h)
    case A.TCon{A.KSep{c}, t} A.RCr{}:
      blank_walk(t, h, R, A.RRec{}, {==}, A.TCon{A.KSep{c}, A.TCon{A.KCr{}, cur}}, done)
    case A.TCon{A.KCr{}, t} A.RCr{}:
      blank_walk(t, h, R, A.RCr{}, {==}, A.TCon{A.KCr{}, cur}, done)
    case A.TCon{A.KLf{}, t} A.RCr{}:
      blank_walk(t, h, R, A.RRec{}, {==}, A.TNil{}, A.add_rec(cur, done))
    case A.TCon{A.KText{c}, t} A.RCr{}:
      blank_walk(t, h, R, A.RRec{}, {==}, A.TCon{A.KText{c}, A.TCon{A.KCr{}, cur}}, done)
    case A.TCon{A.KQuote{}, t} A.RCr{}:
      Empty.absurd({A.recs(tapp(A.TCon{A.KQuote{}, t}, A.TCon{A.KLf{}, A.TCon{A.KLf{}, R}}), A.RCr{}, cur, done) == A.recs(tapp(A.TCon{A.KQuote{}, t}, A.TCon{A.KLf{}, R}), A.RCr{}, cur, done) : List<&2, A.Tok>}, h)

def qf_step(+lf: Bool, +cr: Bool, +sp: Bool, +c: Char, +t: A.Tok, h: QF(t)) -> QF(A.TCon{A.kind_go(lf, cr, sp, False{}, c), t}):
  match lf:
    case True{}:
      h
    case False{}:
      match cr:
        case True{}:
          h
        case False{}:
          match sp:
            case True{}:
              h
            case False{}:
              h

def qf_kind_go(+lf: Bool, +cr: Bool, +sp: Bool, +q: Bool, +c: Char, +t: A.Tok, hq: {q == False{} : Bool}, h: QF(t)) -> QF(A.TCon{A.kind_go(lf, cr, sp, q, c), t}):
  match q:
    case True{}:
      Empty.absurd(QF(A.TCon{A.kind_go(lf, cr, sp, True{}, c), t}), MS.internal_false_ne_true(Equal.sym(Bool, True{}, False{}, hq)))
    case False{}:
      qf_step(lf, cr, sp, c, t, h)

def nq_qf(+sep: U32, +s: String, h: Laws.NoQuote(s), +R: A.Tok, hr: QF(R)) -> QF(tk(sep, s, R)):
  match s:
    case SNil{}:
      hr
    case SCon{Chr{+x}, t}:
      (hx, ht) = h
      qf_kind_go(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34)), Chr{x}, tk(sep, t, R), hx, nq_qf(sep, t, ht, R, hr))

def tk_tapp(+sep: U32, +s: String, +R: A.Tok) -> {tk(sep, s, R) == tapp(tk(sep, s, A.TNil{}), R) : A.Tok}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %tk_tapp(sep, t, R) : {A.TCon{A.kind(sep, c), tk(sep, t, R)} == A.TCon{A.kind(sep, c), _} : A.Tok}
      {==}

def tok_nl(+sep: U32, +a: String, +r: String) -> {A.tokens(sep, String.append(String.append(a, "\n"), r)) == tk(sep, a, A.TCon{A.KLf{}, A.tokens(sep, r)}) : A.Tok}:
  %MS.internal_append_assoc(a, "\n", r) : {A.tokens(sep, _) == tk(sep, a, A.TCon{A.KLf{}, A.tokens(sep, r)}) : A.Tok}
  %Equal.sym(A.Tok, A.tokens(sep, String.append(a, SCon{Chr{10}, r})), tk(sep, a, A.tokens(sep, SCon{Chr{10}, r})), tok_tk(sep, a, SCon{Chr{10}, r})) : {_ == tk(sep, a, A.TCon{A.KLf{}, A.tokens(sep, r)}) : A.Tok}
  {==}

def tok_nl2(+sep: U32, +a: String, +b: String) -> {A.tokens(sep, String.append(String.append(String.append(a, "\n"), "\n"), b)) == tk(sep, a, A.TCon{A.KLf{}, A.TCon{A.KLf{}, A.tokens(sep, b)}}) : A.Tok}:
  %MS.internal_append_assoc(String.append(a, "\n"), "\n", b) : {A.tokens(sep, _) == tk(sep, a, A.TCon{A.KLf{}, A.TCon{A.KLf{}, A.tokens(sep, b)}}) : A.Tok}
  tok_nl(sep, a, SCon{Chr{10}, b})

def Laws.abnf_blank_line_adds_nothing(sep, a, b, ha, hb):
  %Equal.sym(A.Tok, A.tokens(sep, String.append(String.append(String.append(a, "\n"), "\n"), b)), tk(sep, a, A.TCon{A.KLf{}, A.TCon{A.KLf{}, A.tokens(sep, b)}}), tok_nl2(sep, a, b)) : {A.rows(A.rows_map(A.field_map(A.recs(_, A.RRec{}, A.TNil{}, []))), []) == A.rows(A.rows_map(A.field_map(A.recs(A.tokens(sep, String.append(String.append(a, "\n"), b)), A.RRec{}, A.TNil{}, []))), []) : A.Ans}
  %Equal.sym(A.Tok, A.tokens(sep, String.append(String.append(a, "\n"), b)), tk(sep, a, A.TCon{A.KLf{}, A.tokens(sep, b)}), tok_nl(sep, a, b)) : {A.rows(A.rows_map(A.field_map(A.recs(tk(sep, a, A.TCon{A.KLf{}, A.TCon{A.KLf{}, A.tokens(sep, b)}}), A.RRec{}, A.TNil{}, []))), []) == A.rows(A.rows_map(A.field_map(A.recs(_, A.RRec{}, A.TNil{}, []))), []) : A.Ans}
  %Equal.sym(A.Tok, tk(sep, a, A.TCon{A.KLf{}, A.TCon{A.KLf{}, A.tokens(sep, b)}}), tapp(tk(sep, a, A.TNil{}), A.TCon{A.KLf{}, A.TCon{A.KLf{}, A.tokens(sep, b)}}), tk_tapp(sep, a, A.TCon{A.KLf{}, A.TCon{A.KLf{}, A.tokens(sep, b)}})) : {A.rows(A.rows_map(A.field_map(A.recs(_, A.RRec{}, A.TNil{}, []))), []) == A.rows(A.rows_map(A.field_map(A.recs(tk(sep, a, A.TCon{A.KLf{}, A.tokens(sep, b)}), A.RRec{}, A.TNil{}, []))), []) : A.Ans}
  %Equal.sym(A.Tok, tk(sep, a, A.TCon{A.KLf{}, A.tokens(sep, b)}), tapp(tk(sep, a, A.TNil{}), A.TCon{A.KLf{}, A.tokens(sep, b)}), tk_tapp(sep, a, A.TCon{A.KLf{}, A.tokens(sep, b)})) : {A.rows(A.rows_map(A.field_map(A.recs(tapp(tk(sep, a, A.TNil{}), A.TCon{A.KLf{}, A.TCon{A.KLf{}, A.tokens(sep, b)}}), A.RRec{}, A.TNil{}, []))), []) == A.rows(A.rows_map(A.field_map(A.recs(_, A.RRec{}, A.TNil{}, []))), []) : A.Ans}
  %Equal.sym(List<&2, A.Tok>, A.recs(tapp(tk(sep, a, A.TNil{}), A.TCon{A.KLf{}, A.TCon{A.KLf{}, A.tokens(sep, b)}}), A.RRec{}, A.TNil{}, []), A.recs(tapp(tk(sep, a, A.TNil{}), A.TCon{A.KLf{}, A.tokens(sep, b)}), A.RRec{}, A.TNil{}, []), blank_walk(tk(sep, a, A.TNil{}), nq_qf(sep, a, ha, A.TNil{}, Unit{}), A.tokens(sep, b), A.RRec{}, {==}, A.TNil{}, [])) : {A.rows(A.rows_map(A.field_map(_)), []) == A.rows(A.rows_map(A.field_map(A.recs(tapp(tk(sep, a, A.TNil{}), A.TCon{A.KLf{}, A.tokens(sep, b)}), A.RRec{}, A.TNil{}, []))), []) : A.Ans}
  {==}

# ---- abnf_trailing_newline_adds_nothing ----
# A trailing LF is invisible unless the input ends inside an open quote (mode REsc),
# where it is content. There both sides are Rejected: an odd number of quotes in a
# record can never decode. `par` counts quotes mod 2 (accumulator style).
def bnot(+b: Bool) -> Bool:
  match b:
    case True{}:
      False{}
    case False{}:
      True{}

def par(+ts: A.Tok, +p: Bool) -> Bool:
  match ts:
    case A.TNil{}:
      p
    case A.TCon{A.KQuote{}, t}:
      par(t, bnot(p))
    case A.TCon{A.KSep{c}, t}:
      par(t, p)
    case A.TCon{A.KCr{}, t}:
      par(t, p)
    case A.TCon{A.KLf{}, t}:
      par(t, p)
    case A.TCon{A.KText{c}, t}:
      par(t, p)

def par_flip(+ts: A.Tok, +p: Bool) -> {par(ts, bnot(p)) == bnot(par(ts, p)) : Bool}:
  match ts:
    case A.TNil{}:
      {==}
    case A.TCon{A.KQuote{}, t}:
      par_flip(t, bnot(p))
    case A.TCon{A.KSep{c}, t}:
      par_flip(t, p)
    case A.TCon{A.KCr{}, t}:
      par_flip(t, p)
    case A.TCon{A.KLf{}, t}:
      par_flip(t, p)
    case A.TCon{A.KText{c}, t}:
      par_flip(t, p)

def pf_ft(+c: A.Tok, h: {par(c, False{}) == False{} : Bool}) -> {par(c, True{}) == True{} : Bool}:
  %Equal.sym(Bool, par(c, True{}), bnot(par(c, False{})), par_flip(c, False{})) : {_ == True{} : Bool}
  %Equal.sym(Bool, par(c, False{}), False{}, h) : {bnot(_) == True{} : Bool}
  {==}

def pf_tf(+c: A.Tok, h: {par(c, False{}) == True{} : Bool}) -> {par(c, True{}) == False{} : Bool}:
  %Equal.sym(Bool, par(c, True{}), bnot(par(c, False{})), par_flip(c, False{})) : {_ == False{} : Bool}
  %Equal.sym(Bool, par(c, False{}), True{}, h) : {bnot(_) == False{} : Bool}
  {==}

# -- a rejected row makes the whole answer a rejection --
def nonep(+m: Maybe<&2, List<&2, String>>) -> Bool:
  match m:
    case Some{r}:
      False{}
    case None{}:
      True{}

def anyN(+ms: List<&2, Maybe<&2, List<&2, String>>>) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{Some{r}, t}:
      anyN(t)
    case Con{None{}, t}:
      True{}

def rowsR0(+ms: List<&2, Maybe<&2, List<&2, String>>>, +z: List<&2, List<&2, String>>, h: {anyN(ms) == True{} : Bool}) -> {A.rows(ms, z) == A.Rejected{} : A.Ans}:
  match ms:
    case Nil{}:
      Empty.absurd({A.rows(Nil{}, z) == A.Rejected{} : A.Ans}, MS.internal_false_ne_true(h))
    case Con{Some{r}, t}:
      rowsR0(t, Con{r, z}, h)
    case Con{None{}, t}:
      {==}

def an_l(+m: Maybe<&2, List<&2, String>>, +rest: List<&2, Maybe<&2, List<&2, String>>>, hm: {nonep(m) == True{} : Bool}) -> {anyN(Con{m, rest}) == True{} : Bool}:
  match m:
    case Some{r}:
      Empty.absurd({anyN(Con{Some{r}, rest}) == True{} : Bool}, MS.internal_false_ne_true(hm))
    case None{}:
      {==}

def an_r(+m: Maybe<&2, List<&2, String>>, +rest: List<&2, Maybe<&2, List<&2, String>>>, hr: {anyN(rest) == True{} : Bool}) -> {anyN(Con{m, rest}) == True{} : Bool}:
  match m:
    case Some{r}:
      hr
    case None{}:
      {==}

def badL(+l: List<&2, A.Tok>) -> Bool:
  anyN(A.rows_map(A.field_map(l)))

def bad_cons_l(+r: A.Tok, +rest: List<&2, A.Tok>, hm: {nonep(A.row_of(A.text_map(A.fields(r, A.FOut{}, A.TNil{}, [])), [])) == True{} : Bool}) -> {badL(Con{r, rest}) == True{} : Bool}:
  an_l(A.row_of(A.text_map(A.fields(r, A.FOut{}, A.TNil{}, [])), []), A.rows_map(A.field_map(rest)), hm)

def bad_cons_r(+r: A.Tok, +rest: List<&2, A.Tok>, hr: {badL(rest) == True{} : Bool}) -> {badL(Con{r, rest}) == True{} : Bool}:
  an_r(A.row_of(A.text_map(A.fields(r, A.FOut{}, A.TNil{}, [])), []), A.rows_map(A.field_map(rest)), hr)

def RL(+l: List<&2, A.Tok>, +acc: List<&2, A.Tok>, h: {badL(acc) == True{} : Bool}) -> {A.rows(A.rows_map(A.field_map(List.reverse.go(&2, A.Tok, l, acc))), []) == A.Rejected{} : A.Ans}:
  match l:
    case Nil{}:
      rowsR0(A.rows_map(A.field_map(acc)), [], h)
    case Con{x, t}:
      RL(t, Con{x, acc}, bad_cons_r(x, acc, h))

# -- parity lemmas --
def par_rev(+c: A.Tok, +acc: A.Tok, +p: Bool) -> {par(A.rev_tok(c, acc), p) == par(acc, par(c, p)) : Bool}:
  match c:
    case A.TNil{}:
      {==}
    case A.TCon{A.KQuote{}, t}:
      %Equal.sym(Bool, par(t, bnot(p)), bnot(par(t, p)), par_flip(t, p)) : {par(A.rev_tok(t, A.TCon{A.KQuote{}, acc}), p) == par(acc, _) : Bool}
      par_rev(t, A.TCon{A.KQuote{}, acc}, p)
    case A.TCon{A.KSep{x}, t}:
      par_rev(t, A.TCon{A.KSep{x}, acc}, p)
    case A.TCon{A.KCr{}, t}:
      par_rev(t, A.TCon{A.KCr{}, acc}, p)
    case A.TCon{A.KLf{}, t}:
      par_rev(t, A.TCon{A.KLf{}, acc}, p)
    case A.TCon{A.KText{x}, t}:
      par_rev(t, A.TCon{A.KText{x}, acc}, p)

def bare_odd(+ts: A.Tok, +txt: String, h: {par(ts, False{}) == True{} : Bool}) -> {A.bare(ts, txt) == None{} : Maybe<&2, String>}:
  match ts:
    case A.TNil{}:
      Empty.absurd({A.bare(A.TNil{}, txt) == None{} : Maybe<&2, String>}, MS.internal_false_ne_true(h))
    case A.TCon{A.KQuote{}, t}:
      {==}
    case A.TCon{A.KSep{c}, t}:
      bare_odd(t, String.append(txt, SCon{c, SNil{}}), h)
    case A.TCon{A.KCr{}, t}:
      bare_odd(t, String.append(txt, SCon{Chr{13}, SNil{}}), h)
    case A.TCon{A.KLf{}, t}:
      bare_odd(t, String.append(txt, SCon{Chr{10}, SNil{}}), h)
    case A.TCon{A.KText{c}, t}:
      bare_odd(t, String.append(txt, SCon{c, SNil{}}), h)

def iq(+ph: A.EPh) -> Bool:
  match ph:
    case A.EIn{}:
      True{}
    case A.EInQ{}:
      False{}

def esc_odd(+ts: A.Tok, +ph: A.EPh, +txt: String, h: {par(ts, iq(ph)) == True{} : Bool}) -> {A.esc(ts, ph, txt) == None{} : Maybe<&2, String>}:
  match ts ph:
    case A.TNil{} A.EIn{}:
      {==}
    case A.TNil{} A.EInQ{}:
      Empty.absurd({A.esc(A.TNil{}, A.EInQ{}, txt) == None{} : Maybe<&2, String>}, MS.internal_false_ne_true(h))
    case A.TCon{A.KQuote{}, t} A.EIn{}:
      esc_odd(t, A.EInQ{}, txt, h)
    case A.TCon{A.KQuote{}, t} A.EInQ{}:
      esc_odd(t, A.EIn{}, String.append(txt, SCon{Chr{34}, SNil{}}), h)
    case A.TCon{A.KSep{c}, t} A.EIn{}:
      esc_odd(t, A.EIn{}, String.append(txt, SCon{c, SNil{}}), h)
    case A.TCon{A.KSep{c}, t} A.EInQ{}:
      {==}
    case A.TCon{A.KCr{}, t} A.EIn{}:
      esc_odd(t, A.EIn{}, String.append(txt, SCon{Chr{13}, SNil{}}), h)
    case A.TCon{A.KCr{}, t} A.EInQ{}:
      {==}
    case A.TCon{A.KLf{}, t} A.EIn{}:
      esc_odd(t, A.EIn{}, String.append(txt, SCon{Chr{10}, SNil{}}), h)
    case A.TCon{A.KLf{}, t} A.EInQ{}:
      {==}
    case A.TCon{A.KText{c}, t} A.EIn{}:
      esc_odd(t, A.EIn{}, String.append(txt, SCon{c, SNil{}}), h)
    case A.TCon{A.KText{c}, t} A.EInQ{}:
      {==}

def decode_odd(+c: A.Tok, h: {par(c, False{}) == True{} : Bool}) -> {A.decode(c) == None{} : Maybe<&2, String>}:
  match c:
    case A.TNil{}:
      Empty.absurd({A.decode(A.TNil{}) == None{} : Maybe<&2, String>}, MS.internal_false_ne_true(h))
    case A.TCon{A.KQuote{}, t}:
      esc_odd(t, A.EIn{}, SNil{}, h)
    case A.TCon{A.KSep{x}, t}:
      bare_odd(t, SCon{x, SNil{}}, h)
    case A.TCon{A.KCr{}, t}:
      bare_odd(t, SCon{Chr{13}, SNil{}}, h)
    case A.TCon{A.KLf{}, t}:
      bare_odd(t, SCon{Chr{10}, SNil{}}, h)
    case A.TCon{A.KText{x}, t}:
      bare_odd(t, SCon{x, SNil{}}, h)

def isIn(+ph: A.FPh) -> Bool:
  match ph:
    case A.FOut{}:
      False{}
    case A.FIn{}:
      True{}
    case A.FInQ{}:
      False{}

def anyS(+ms: List<&2, Maybe<&2, String>>) -> Bool:
  match ms:
    case Nil{}:
      False{}
    case Con{Some{r}, t}:
      anyS(t)
    case Con{None{}, t}:
      True{}

def isNoneS(+m: Maybe<&2, String>) -> Bool:
  match m:
    case Some{r}:
      False{}
    case None{}:
      True{}

def row_none(+vs: List<&2, Maybe<&2, String>>, +acc: List<&2, String>, h: {anyS(vs) == True{} : Bool}) -> {nonep(A.row_of(vs, acc)) == True{} : Bool}:
  match vs:
    case Nil{}:
      Empty.absurd({nonep(A.row_of(Nil{}, acc)) == True{} : Bool}, MS.internal_false_ne_true(h))
    case Con{Some{s}, t}:
      row_none(t, Con{s, acc}, h)
    case Con{None{}, t}:
      {==}

def an_s(+m: Maybe<&2, String>, +rest: List<&2, Maybe<&2, String>>, h: {anyS(rest) == True{} : Bool}) -> {anyS(Con{m, rest}) == True{} : Bool}:
  match m:
    case Some{r}:
      h
    case None{}:
      {==}

def an_sl(+m: Maybe<&2, String>, +rest: List<&2, Maybe<&2, String>>, h: {isNoneS(m) == True{} : Bool}) -> {anyS(Con{m, rest}) == True{} : Bool}:
  match m:
    case Some{r}:
      Empty.absurd({anyS(Con{Some{r}, rest}) == True{} : Bool}, MS.internal_false_ne_true(h))
    case None{}:
      {==}

def RLf(+l: List<&2, A.Tok>, +acc: List<&2, A.Tok>, h: {anyS(A.text_map(acc)) == True{} : Bool}) -> {anyS(A.text_map(List.reverse.go(&2, A.Tok, l, acc))) == True{} : Bool}:
  match l:
    case Nil{}:
      h
    case Con{x, t}:
      RLf(t, Con{x, acc}, an_s(A.decode(x), A.text_map(acc), h))

def pq(+cur: A.Tok, +b: Bool, hb: {par(cur, False{}) == b : Bool}) -> {par(A.TCon{A.KQuote{}, cur}, False{}) == bnot(b) : Bool}:
  %Equal.sym(Bool, par(cur, True{}), bnot(par(cur, False{})), par_flip(cur, False{})) : {_ == bnot(b) : Bool}
  %Equal.sym(Bool, par(cur, False{}), b, hb) : {bnot(_) == bnot(b) : Bool}
  {==}

def prw(+cur: A.Tok, hb: {par(cur, False{}) == True{} : Bool}) -> {par(A.rev_tok(cur, A.TNil{}), False{}) == True{} : Bool}:
  %Equal.sym(Bool, par(A.rev_tok(cur, A.TNil{}), False{}), par(cur, False{}), par_rev(cur, A.TNil{}, False{})) : {_ == True{} : Bool}
  hb

def dec_none(+c: A.Tok, h: {par(c, False{}) == True{} : Bool}) -> {isNoneS(A.decode(c)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, String>, A.decode(c), None{}, decode_odd(c, h)) : {isNoneS(_) == True{} : Bool}
  {==}

def FW(+ts: A.Tok, +ph: A.FPh, +cur: A.Tok, +done: List<&2, A.Tok>, hb: {par(cur, False{}) == isIn(ph) : Bool}, ht: {par(ts, isIn(ph)) == True{} : Bool}) -> {anyS(A.text_map(A.fields(ts, ph, cur, done))) == True{} : Bool}:
  match ts ph:
    case A.TNil{} A.FOut{}:
      Empty.absurd({anyS(A.text_map(A.fields(A.TNil{}, A.FOut{}, cur, done))) == True{} : Bool}, MS.internal_false_ne_true(ht))
    case A.TNil{} A.FIn{}:
      RLf(done, Con{A.rev_tok(cur, A.TNil{}), Nil{}}, an_sl(A.decode(A.rev_tok(cur, A.TNil{})), Nil{}, dec_none(A.rev_tok(cur, A.TNil{}), prw(cur, hb))))
    case A.TNil{} A.FInQ{}:
      Empty.absurd({anyS(A.text_map(A.fields(A.TNil{}, A.FInQ{}, cur, done))) == True{} : Bool}, MS.internal_false_ne_true(ht))
    case A.TCon{A.KSep{c}, t} A.FOut{}:
      FW(t, A.FOut{}, A.TNil{}, A.whole(cur, done), {==}, ht)
    case A.TCon{A.KQuote{}, t} A.FOut{}:
      FW(t, A.FIn{}, A.TCon{A.KQuote{}, cur}, done, pq(cur, False{}, hb), ht)
    case A.TCon{A.KCr{}, t} A.FOut{}:
      FW(t, A.FOut{}, A.TCon{A.KCr{}, cur}, done, hb, ht)
    case A.TCon{A.KLf{}, t} A.FOut{}:
      FW(t, A.FOut{}, A.TCon{A.KLf{}, cur}, done, hb, ht)
    case A.TCon{A.KText{c}, t} A.FOut{}:
      FW(t, A.FOut{}, A.TCon{A.KText{c}, cur}, done, hb, ht)
    case A.TCon{A.KQuote{}, t} A.FIn{}:
      FW(t, A.FInQ{}, A.TCon{A.KQuote{}, cur}, done, pq(cur, True{}, hb), ht)
    case A.TCon{A.KSep{c}, t} A.FIn{}:
      FW(t, A.FIn{}, A.TCon{A.KSep{c}, cur}, done, hb, ht)
    case A.TCon{A.KCr{}, t} A.FIn{}:
      FW(t, A.FIn{}, A.TCon{A.KCr{}, cur}, done, hb, ht)
    case A.TCon{A.KLf{}, t} A.FIn{}:
      FW(t, A.FIn{}, A.TCon{A.KLf{}, cur}, done, hb, ht)
    case A.TCon{A.KText{c}, t} A.FIn{}:
      FW(t, A.FIn{}, A.TCon{A.KText{c}, cur}, done, hb, ht)
    case A.TCon{A.KQuote{}, t} A.FInQ{}:
      FW(t, A.FIn{}, A.TCon{A.KQuote{}, cur}, done, pq(cur, False{}, hb), ht)
    case A.TCon{A.KSep{c}, t} A.FInQ{}:
      FW(t, A.FOut{}, A.TNil{}, A.whole(cur, done), {==}, ht)
    case A.TCon{A.KCr{}, t} A.FInQ{}:
      FW(t, A.FOut{}, A.TCon{A.KCr{}, cur}, done, hb, ht)
    case A.TCon{A.KLf{}, t} A.FInQ{}:
      FW(t, A.FOut{}, A.TCon{A.KLf{}, cur}, done, hb, ht)
    case A.TCon{A.KText{c}, t} A.FInQ{}:
      FW(t, A.FOut{}, A.TCon{A.KText{c}, cur}, done, hb, ht)

# -- the end of an open quote: rejected --
def Fin(+l: List<&2, A.Tok>) -> A.Ans:
  A.rows(A.rows_map(A.field_map(l)), [])

def rej_end(+x: A.Tok, +done: List<&2, A.Tok>, h: {par(x, False{}) == True{} : Bool}) -> {Fin(List.reverse(&2, A.Tok, A.whole(x, done))) == A.Rejected{} : A.Ans}:
  RL(done, Con{A.rev_tok(x, A.TNil{}), Nil{}}, bad_cons_l(A.rev_tok(x, A.TNil{}), Nil{}, row_none(A.text_map(A.fields(A.rev_tok(x, A.TNil{}), A.FOut{}, A.TNil{}, [])), [], FW(A.rev_tok(x, A.TNil{}), A.FOut{}, A.TNil{}, [], {==}, prw(x, h)))))

def tr(+a: A.Ans, +b: A.Ans, +c: A.Ans, h1: {a == b : A.Ans}, h2: {c == b : A.Ans}) -> {a == c : A.Ans}:
  %Equal.sym(A.Ans, c, b, h2) : {a == _ : A.Ans}
  h1

def ans_end(+cur: A.Tok, +done: List<&2, A.Tok>, +hp: {par(cur, False{}) == True{} : Bool}) -> {Fin(A.recs(A.TCon{A.KLf{}, A.TNil{}}, A.REsc{}, cur, done)) == Fin(A.recs(A.TNil{}, A.REsc{}, cur, done)) : A.Ans}:
  match cur:
    case A.TNil{}:
      Empty.absurd({Fin(A.recs(A.TCon{A.KLf{}, A.TNil{}}, A.REsc{}, A.TNil{}, done)) == Fin(A.recs(A.TNil{}, A.REsc{}, A.TNil{}, done)) : A.Ans}, MS.internal_false_ne_true(hp))
    case A.TCon{k, t}:
      tr(Fin(A.recs(A.TCon{A.KLf{}, A.TNil{}}, A.REsc{}, cur, done)), A.Rejected{}, Fin(A.recs(A.TNil{}, A.REsc{}, cur, done)), rej_end(A.TCon{A.KLf{}, cur}, done, hp), rej_end(cur, done, hp))

def ans_step(+ts: A.Tok, +ph: A.RPh, +cur: A.Tok, +done: List<&2, A.Tok>, hp: {par(cur, False{}) == isE(ph) : Bool}) -> {Fin(A.recs(tapp(ts, A.TCon{A.KLf{}, A.TNil{}}), ph, cur, done)) == Fin(A.recs(ts, ph, cur, done)) : A.Ans}:
  match ts ph:
    case A.TNil{} A.RRec{}:
      {==}
    case A.TNil{} A.REscQ{}:
      {==}
    case A.TNil{} A.RCr{}:
      {==}
    case A.TNil{} A.REsc{}:
      ans_end(cur, done, hp)
    case A.TCon{A.KSep{c}, t} A.RRec{}:
      ans_step(t, A.RRec{}, A.TCon{A.KSep{c}, cur}, done, hp)
    case A.TCon{A.KCr{}, t} A.RRec{}:
      ans_step(t, A.RCr{}, cur, done, hp)
    case A.TCon{A.KLf{}, t} A.RRec{}:
      ans_step(t, A.RRec{}, A.TNil{}, A.add_rec(cur, done), {==})
    case A.TCon{A.KText{c}, t} A.RRec{}:
      ans_step(t, A.RRec{}, A.TCon{A.KText{c}, cur}, done, hp)
    case A.TCon{A.KQuote{}, t} A.RRec{}:
      ans_step(t, A.REsc{}, A.TCon{A.KQuote{}, cur}, done, pq(cur, False{}, hp))
    case A.TCon{A.KSep{c}, t} A.REsc{}:
      ans_step(t, A.REsc{}, A.TCon{A.KSep{c}, cur}, done, hp)
    case A.TCon{A.KCr{}, t} A.REsc{}:
      ans_step(t, A.REsc{}, A.TCon{A.KCr{}, cur}, done, hp)
    case A.TCon{A.KLf{}, t} A.REsc{}:
      ans_step(t, A.REsc{}, A.TCon{A.KLf{}, cur}, done, hp)
    case A.TCon{A.KText{c}, t} A.REsc{}:
      ans_step(t, A.REsc{}, A.TCon{A.KText{c}, cur}, done, hp)
    case A.TCon{A.KQuote{}, t} A.REsc{}:
      ans_step(t, A.REscQ{}, A.TCon{A.KQuote{}, cur}, done, pq(cur, True{}, hp))
    case A.TCon{A.KQuote{}, t} A.REscQ{}:
      ans_step(t, A.REsc{}, A.TCon{A.KQuote{}, cur}, done, pq(cur, False{}, hp))
    case A.TCon{A.KLf{}, t} A.REscQ{}:
      ans_step(t, A.RRec{}, A.TNil{}, A.add_rec(cur, done), {==})
    case A.TCon{A.KCr{}, t} A.REscQ{}:
      ans_step(t, A.RCr{}, cur, done, hp)
    case A.TCon{A.KSep{c}, t} A.REscQ{}:
      ans_step(t, A.RRec{}, A.TCon{A.KSep{c}, cur}, done, hp)
    case A.TCon{A.KText{c}, t} A.REscQ{}:
      ans_step(t, A.RRec{}, A.TCon{A.KText{c}, cur}, done, hp)
    case A.TCon{A.KCr{}, t} A.RCr{}:
      ans_step(t, A.RCr{}, A.TCon{A.KCr{}, cur}, done, hp)
    case A.TCon{A.KLf{}, t} A.RCr{}:
      ans_step(t, A.RRec{}, A.TNil{}, A.add_rec(cur, done), {==})
    case A.TCon{A.KQuote{}, t} A.RCr{}:
      ans_step(t, A.REsc{}, A.TCon{A.KQuote{}, A.TCon{A.KCr{}, cur}}, done, pq(A.TCon{A.KCr{}, cur}, False{}, hp))
    case A.TCon{A.KSep{c}, t} A.RCr{}:
      ans_step(t, A.RRec{}, A.TCon{A.KSep{c}, A.TCon{A.KCr{}, cur}}, done, hp)
    case A.TCon{A.KText{c}, t} A.RCr{}:
      ans_step(t, A.RRec{}, A.TCon{A.KText{c}, A.TCon{A.KCr{}, cur}}, done, hp)

def tk_nil(+sep: U32, +s: String) -> {A.tokens(sep, s) == tk(sep, s, A.TNil{}) : A.Tok}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      %tk_nil(sep, t) : {A.TCon{A.kind(sep, c), A.tokens(sep, t)} == A.TCon{A.kind(sep, c), _} : A.Tok}
      {==}

def tok_end(+sep: U32, +s: String) -> {A.tokens(sep, String.append(s, "\n")) == tapp(A.tokens(sep, s), A.TCon{A.KLf{}, A.TNil{}}) : A.Tok}:
  %Equal.sym(A.Tok, A.tokens(sep, String.append(s, SCon{Chr{10}, SNil{}})), tk(sep, s, A.tokens(sep, SCon{Chr{10}, SNil{}})), tok_tk(sep, s, SCon{Chr{10}, SNil{}})) : {_ == tapp(A.tokens(sep, s), A.TCon{A.KLf{}, A.TNil{}}) : A.Tok}
  %Equal.sym(A.Tok, tk(sep, s, A.TCon{A.KLf{}, A.TNil{}}), tapp(tk(sep, s, A.TNil{}), A.TCon{A.KLf{}, A.TNil{}}), tk_tapp(sep, s, A.TCon{A.KLf{}, A.TNil{}})) : {_ == tapp(A.tokens(sep, s), A.TCon{A.KLf{}, A.TNil{}}) : A.Tok}
  %Equal.sym(A.Tok, A.tokens(sep, s), tk(sep, s, A.TNil{}), tk_nil(sep, s)) : {tapp(tk(sep, s, A.TNil{}), A.TCon{A.KLf{}, A.TNil{}}) == tapp(_, A.TCon{A.KLf{}, A.TNil{}}) : A.Tok}
  {==}

def Laws.abnf_trailing_newline_adds_nothing(sep, s):
  %Equal.sym(A.Tok, A.tokens(sep, String.append(s, "\n")), tapp(A.tokens(sep, s), A.TCon{A.KLf{}, A.TNil{}}), tok_end(sep, s)) : {A.rows(A.rows_map(A.field_map(A.recs(_, A.RRec{}, A.TNil{}, []))), []) == A.rows(A.rows_map(A.field_map(A.recs(A.tokens(sep, s), A.RRec{}, A.TNil{}, []))), []) : A.Ans}
  ans_step(A.tokens(sep, s), A.RRec{}, A.TNil{}, [], {==})
