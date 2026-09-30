import Base
import ./LAWS.bend as Laws
import ./core.bend as A
import ./vendor/bendlib/packages/bend-mathlib/string.bend as MS
import ./vendor/bendlib/packages/bend-mathlib/list.bend as ML

# csv-abnf's proofs, against the fused core (one walk `go`, no token list).
# The gate is `bend PROOF.bend`.
#
# Each law of LAWS.bend is filled by a `def Laws.<name>` here: the law's `for`
# binders are the parameters, in order, and the law's statement is the type.
# A law that is not filled is reported by the checker as open (a TODO).
#
# The earlier proofs were about the token-list walk and are in git history
# (ba809ca). Every section below starts open.

# ---- abnf_empty_input_is_no_record ----

def Laws.abnf_empty_input_is_no_record(sep):
  {==}

# ---- abnf_lone_empty_field_keeps_its_row ----

def Laws.abnf_lone_empty_field_keeps_its_row(sep, hq):
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, 34)), False{}, hq) : {A.go("\"\"\n", A.MS{}, A.cls_go(False{}, False{}, _, True{}), sep, "", [], []) == A.Parsed{[[""]]} : A.Ans}
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, 34)), False{}, hq) : {A.go("\"\n", A.ME{}, A.cls_go(False{}, False{}, _, True{}), sep, "", [], []) == A.Parsed{[[""]]} : A.Ans}
  {==}

# ---- abnf_cr_inside_a_field_is_content ----

# ---- abnf_clean_input_is_one_field ----
#
# Probe. Clean never leaves mode MB, so `flds` and `rows` ride along unchanged and
# the text accumulator is the only thing the induction touches.
def walk_mb(+sep: U32, +s: String, h: Laws.Clean(sep, s), +txt: String, flds: List<&2, String>, rows: List<&2, List<&2, String>>) -> {A.go(s, A.MB{}, A.cls_of(sep, s), sep, txt, flds, rows) == A.fin(A.MB{}, String.append(txt, s), flds, rows) : A.Ans}:
  match s:
    case SNil{}:
      %MS.append_nil(txt) : {A.fin(A.MB{}, _, flds, rows) == A.fin(A.MB{}, String.append(txt, SNil{}), flds, rows) : A.Ans}
      {==}
    case SCon{Chr{+x}, t}:
      (hse, hqu, hcr, hlf, ht) = h
      %Equal.sym(Bool, Cmp.is_eq(U32.cmp(x, 10)), False{}, hlf) : {A.go(SCon{Chr{x}, t}, A.MB{}, A.cls_go(_, Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34))), sep, txt, flds, rows) == A.fin(A.MB{}, String.append(txt, SCon{Chr{x}, t}), flds, rows) : A.Ans}
      %Equal.sym(Bool, Cmp.is_eq(U32.cmp(x, 13)), False{}, hcr) : {A.go(SCon{Chr{x}, t}, A.MB{}, A.cls_go(False{}, _, Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34))), sep, txt, flds, rows) == A.fin(A.MB{}, String.append(txt, SCon{Chr{x}, t}), flds, rows) : A.Ans}
      %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, x)), False{}, hse) : {A.go(SCon{Chr{x}, t}, A.MB{}, A.cls_go(False{}, False{}, _, Cmp.is_eq(U32.cmp(x, 34))), sep, txt, flds, rows) == A.fin(A.MB{}, String.append(txt, SCon{Chr{x}, t}), flds, rows) : A.Ans}
      %Equal.sym(Bool, Cmp.is_eq(U32.cmp(x, 34)), False{}, hqu) : {A.go(SCon{Chr{x}, t}, A.MB{}, A.cls_go(False{}, False{}, False{}, _), sep, txt, flds, rows) == A.fin(A.MB{}, String.append(txt, SCon{Chr{x}, t}), flds, rows) : A.Ans}
      %MS.append_assoc(txt, SCon{Chr{x}, SNil{}}, t) : {A.go(t, A.MB{}, A.cls_of(sep, t), sep, String.append(txt, SCon{Chr{x}, SNil{}}), flds, rows) == A.fin(A.MB{}, _, flds, rows) : A.Ans}
      walk_mb(sep, t, ht, String.append(txt, SCon{Chr{x}, SNil{}}), flds, rows)

def Laws.abnf_clean_input_is_one_field(sep, s, h):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, t}:
      (hse, hqu, hcr, hlf, ht) = h
      %Equal.sym(Bool, Cmp.is_eq(U32.cmp(x, 10)), False{}, hlf) : {A.go(SCon{Chr{x}, t}, A.MS{}, A.cls_go(_, Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34))), sep, SNil{}, Nil{}, Nil{}) == Laws.CleanAnswer(SCon{Chr{x}, t}) : A.Ans}
      %Equal.sym(Bool, Cmp.is_eq(U32.cmp(x, 13)), False{}, hcr) : {A.go(SCon{Chr{x}, t}, A.MS{}, A.cls_go(False{}, _, Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34))), sep, SNil{}, Nil{}, Nil{}) == Laws.CleanAnswer(SCon{Chr{x}, t}) : A.Ans}
      %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, x)), False{}, hse) : {A.go(SCon{Chr{x}, t}, A.MS{}, A.cls_go(False{}, False{}, _, Cmp.is_eq(U32.cmp(x, 34))), sep, SNil{}, Nil{}, Nil{}) == Laws.CleanAnswer(SCon{Chr{x}, t}) : A.Ans}
      %Equal.sym(Bool, Cmp.is_eq(U32.cmp(x, 34)), False{}, hqu) : {A.go(SCon{Chr{x}, t}, A.MS{}, A.cls_go(False{}, False{}, False{}, _), sep, SNil{}, Nil{}, Nil{}) == Laws.CleanAnswer(SCon{Chr{x}, t}) : A.Ans}
      walk_mb(sep, t, ht, SCon{Chr{x}, SNil{}}, Nil{}, Nil{})

# ---- abnf_separator_makes_two_fields ----

def sep_self(+sep: U32) -> {Cmp.is_eq(U32.cmp(sep, sep)) == True{} : Bool}:
  %Equal.sym(Cmp, U32.cmp(sep, sep), EQ{}, MS.u32_cmp_refl(sep)) : {Cmp.is_eq(_) == True{} : Bool}
  {==}

# class facts: the class of a character, from what is known of it. Proved once,
# used by every walk lemma below.
def cls_text(+sep: U32, +x: U32, t: String, hse: {Cmp.is_eq(U32.cmp(sep, x)) == False{} : Bool}, hqu: {Cmp.is_eq(U32.cmp(x, 34)) == False{} : Bool}, hcr: {Cmp.is_eq(U32.cmp(x, 13)) == False{} : Bool}, hlf: {Cmp.is_eq(U32.cmp(x, 10)) == False{} : Bool}) -> {A.cls_of(sep, SCon{Chr{x}, t}) == A.CText{} : A.CK}:
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(x, 10)), False{}, hlf) : {A.cls_go(_, Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34))) == A.CText{} : A.CK}
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(x, 13)), False{}, hcr) : {A.cls_go(False{}, _, Cmp.is_eq(U32.cmp(sep, x)), Cmp.is_eq(U32.cmp(x, 34))) == A.CText{} : A.CK}
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, x)), False{}, hse) : {A.cls_go(False{}, False{}, _, Cmp.is_eq(U32.cmp(x, 34))) == A.CText{} : A.CK}
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(x, 34)), False{}, hqu) : {A.cls_go(False{}, False{}, False{}, _) == A.CText{} : A.CK}
  {==}

def fin_s(+s: String, +flds: List<&2, String>, +rows: List<&2, List<&2, String>>) -> A.Ans:
  match s:
    case SNil{}:
      A.fin(A.MS{}, SNil{}, flds, rows)
    case SCon{_, _}:
      A.fin(A.MB{}, s, flds, rows)

def walk_ms(+sep: U32, +s: String, h: Laws.Clean(sep, s), flds: List<&2, String>, rows: List<&2, List<&2, String>>) -> {A.go(s, A.MS{}, A.cls_of(sep, s), sep, SNil{}, flds, rows) == fin_s(s, flds, rows) : A.Ans}:
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+x}, t}:
      (hse, hqu, hcr, hlf, ht) = h
      %Equal.sym(A.CK, A.cls_of(sep, SCon{Chr{x}, t}), A.CText{}, cls_text(sep, x, t, hse, hqu, hcr, hlf)) : {A.go(SCon{Chr{x}, t}, A.MS{}, _, sep, SNil{}, flds, rows) == fin_s(SCon{Chr{x}, t}, flds, rows) : A.Ans}
      walk_mb(sep, t, ht, SCon{Chr{x}, SNil{}}, flds, rows)

def cls_sep(+sep: U32, t: String, hl: {Cmp.is_eq(U32.cmp(sep, 10)) == False{} : Bool}, hc: {Cmp.is_eq(U32.cmp(sep, 13)) == False{} : Bool}) -> {A.cls_of(sep, SCon{Chr{sep}, t}) == A.CSep{} : A.CK}:
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, 10)), False{}, hl) : {A.cls_go(_, Cmp.is_eq(U32.cmp(sep, 13)), Cmp.is_eq(U32.cmp(sep, sep)), Cmp.is_eq(U32.cmp(sep, 34))) == A.CSep{} : A.CK}
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, 13)), False{}, hc) : {A.cls_go(False{}, _, Cmp.is_eq(U32.cmp(sep, sep)), Cmp.is_eq(U32.cmp(sep, 34))) == A.CSep{} : A.CK}
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, sep)), True{}, sep_self(sep)) : {A.cls_go(False{}, False{}, _, Cmp.is_eq(U32.cmp(sep, 34))) == A.CSep{} : A.CK}
  {==}

# a clean run in MB, then the separator, then the rest: the run joins the text,
# the separator closes the field, and what follows is read from a field start.
def walk_mb_sep(+sep: U32, hl: {Cmp.is_eq(U32.cmp(sep, 10)) == False{} : Bool}, hc: {Cmp.is_eq(U32.cmp(sep, 13)) == False{} : Bool}, +a: String, ha: Laws.Clean(sep, a), +b: String, hb: Laws.Clean(sep, b), +txt: String, flds: List<&2, String>, rows: List<&2, List<&2, String>>) -> {A.go(String.append(a, SCon{Chr{sep}, b}), A.MB{}, A.cls_of(sep, String.append(a, SCon{Chr{sep}, b})), sep, txt, flds, rows) == fin_s(b, Con{String.append(txt, a), flds}, rows) : A.Ans}:
  match a:
    case SNil{}:
      %Equal.sym(A.CK, A.cls_of(sep, SCon{Chr{sep}, b}), A.CSep{}, cls_sep(sep, b, hl, hc)) : {A.go(SCon{Chr{sep}, b}, A.MB{}, _, sep, txt, flds, rows) == fin_s(b, Con{String.append(txt, SNil{}), flds}, rows) : A.Ans}
      %Equal.sym(String, String.append(txt, SNil{}), txt, MS.append_nil(txt)) : {A.go(b, A.MS{}, A.cls_of(sep, b), sep, SNil{}, Con{txt, flds}, rows) == fin_s(b, Con{_, flds}, rows) : A.Ans}
      walk_ms(sep, b, hb, Con{txt, flds}, rows)
    case SCon{Chr{+x}, t}:
      (hse, hqu, hcr, hlf, ht) = ha
      %Equal.sym(A.CK, A.cls_of(sep, SCon{Chr{x}, String.append(t, SCon{Chr{sep}, b})}), A.CText{}, cls_text(sep, x, String.append(t, SCon{Chr{sep}, b}), hse, hqu, hcr, hlf)) : {A.go(SCon{Chr{x}, String.append(t, SCon{Chr{sep}, b})}, A.MB{}, _, sep, txt, flds, rows) == fin_s(b, Con{String.append(txt, SCon{Chr{x}, t}), flds}, rows) : A.Ans}
      %MS.append_assoc(txt, SCon{Chr{x}, SNil{}}, t) : {A.go(String.append(t, SCon{Chr{sep}, b}), A.MB{}, A.cls_of(sep, String.append(t, SCon{Chr{sep}, b})), sep, String.append(txt, SCon{Chr{x}, SNil{}}), flds, rows) == fin_s(b, Con{_, flds}, rows) : A.Ans}
      walk_mb_sep(sep, hl, hc, t, ht, b, hb, String.append(txt, SCon{Chr{x}, SNil{}}), flds, rows)

def two_fin(+a: String, +b: String) -> {fin_s(b, Con{a, Nil{}}, Nil{}) == A.Parsed{Con{Con{a, Con{b, Nil{}}}, Nil{}}} : A.Ans}:
  match b:
    case SNil{}:
      {==}
    case SCon{_, _}:
      {==}

def two_main(+sep: U32, hl: {Cmp.is_eq(U32.cmp(sep, 10)) == False{} : Bool}, hc: {Cmp.is_eq(U32.cmp(sep, 13)) == False{} : Bool}, +a: String, ha: Laws.Clean(sep, a), +b: String, hb: Laws.Clean(sep, b)) -> {A.parse_sep(sep, String.append(a, SCon{Chr{sep}, b})) == A.Parsed{Con{Con{a, Con{b, Nil{}}}, Nil{}}} : A.Ans}:
  match a:
    case SNil{}:
      %Equal.sym(A.CK, A.cls_of(sep, SCon{Chr{sep}, b}), A.CSep{}, cls_sep(sep, b, hl, hc)) : {A.go(SCon{Chr{sep}, b}, A.MS{}, _, sep, "", [], []) == A.Parsed{[[SNil{}, b]]} : A.Ans}
      %two_fin(SNil{}, b) : {A.go(b, A.MS{}, A.cls_of(sep, b), sep, "", [""], []) == _ : A.Ans}
      walk_ms(sep, b, hb, Con{SNil{}, Nil{}}, Nil{})
    case SCon{Chr{+x}, t}:
      (hse, hqu, hcr, hlf, ht) = ha
      %Equal.sym(A.CK, A.cls_of(sep, SCon{Chr{x}, String.append(t, SCon{Chr{sep}, b})}), A.CText{}, cls_text(sep, x, String.append(t, SCon{Chr{sep}, b}), hse, hqu, hcr, hlf)) : {A.go(SCon{Chr{x}, String.append(t, SCon{Chr{sep}, b})}, A.MS{}, _, sep, "", [], []) == A.Parsed{[[SCon{Chr{x}, t}, b]]} : A.Ans}
      %two_fin(SCon{Chr{x}, t}, b) : {A.go(String.append(t, SCon{Chr{sep}, b}), A.MB{}, A.cls_of(sep, String.append(t, SCon{Chr{sep}, b})), sep, SCon{Chr{x}, SNil{}}, [], []) == _ : A.Ans}
      walk_mb_sep(sep, hl, hc, t, ht, b, hb, SCon{Chr{x}, SNil{}}, Nil{}, Nil{})

def Laws.abnf_separator_makes_two_fields(sep, hl, hc, a, b, ha, hb):
  %Equal.sym(String, String.append(String.append(a, SCon{Chr{sep}, SNil{}}), b), String.append(a, String.append(SCon{Chr{sep}, SNil{}}, b)), MS.append_assoc(a, SCon{Chr{sep}, SNil{}}, b)) : {A.parse_sep(sep, _) == A.Parsed{Con{Con{a, Con{b, Nil{}}}, Nil{}}} : A.Ans}
  two_main(sep, hl, hc, a, ha, b, hb)
