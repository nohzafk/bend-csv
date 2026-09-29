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

# ---- abnf_lone_empty_field_keeps_its_row ----

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

# ---- abnf_quoted_field_is_its_content ----

# ---- abnf_doubled_quote_is_one_quote ----

# ---- abnf_blank_line_adds_nothing ----

# ---- abnf_trailing_newline_adds_nothing ----
