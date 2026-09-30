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

def Laws.abnf_cr_inside_a_field_is_content(sep, ha, hb):
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, 97)), False{}, ha) : {A.go("a\rb\r\n", A.MS{}, A.cls_go(False{}, False{}, _, False{}), sep, "", [], []) == A.Parsed{[["a\rb"]]} : A.Ans}
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, 98)), False{}, hb) : {A.go("b\r\n", A.MBC{}, A.cls_go(False{}, False{}, _, False{}), sep, "a", [], []) == A.Parsed{[["a\rb"]]} : A.Ans}
  {==}

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

# ---- abnf_quoted_field_is_its_content ----
#
# In an escaped field (ME) every non-quote character is content, whatever its class.
def me_step(+b1: Bool, +b2: Bool, +b3: Bool, +x: U32, t: String, +sep: U32, txt: String, flds: List<&2, String>, rows: List<&2, List<&2, String>>, h1: {Cmp.is_eq(U32.cmp(x, 10)) == b1 : Bool}, h2: {Cmp.is_eq(U32.cmp(x, 13)) == b2 : Bool}) -> {A.go(SCon{Chr{x}, t}, A.ME{}, A.cls_go(b1, b2, b3, False{}), sep, txt, flds, rows) == A.go(t, A.ME{}, A.cls_of(sep, t), sep, String.append(txt, SCon{Chr{x}, SNil{}}), flds, rows) : A.Ans}:
  match b1 b2 b3:
    case True{} _ _:
      %Equal.sym(U32, x, 10, MS.u32_eq_of_is_eq(x, 10, h1)) : {A.go(SCon{Chr{x}, t}, A.ME{}, A.cls_go(True{}, b2, b3, False{}), sep, txt, flds, rows) == A.go(t, A.ME{}, A.cls_of(sep, t), sep, String.append(txt, SCon{Chr{_}, SNil{}}), flds, rows) : A.Ans}
      {==}
    case False{} True{} _:
      %Equal.sym(U32, x, 13, MS.u32_eq_of_is_eq(x, 13, h2)) : {A.go(SCon{Chr{x}, t}, A.ME{}, A.cls_go(False{}, True{}, b3, False{}), sep, txt, flds, rows) == A.go(t, A.ME{}, A.cls_of(sep, t), sep, String.append(txt, SCon{Chr{_}, SNil{}}), flds, rows) : A.Ans}
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def walk_me(+sep: U32, hq: {Cmp.is_eq(U32.cmp(sep, 34)) == False{} : Bool}, +s: String, h: Laws.NoQuote(s), +txt: String, +flds: List<&2, String>, +rows: List<&2, List<&2, String>>) -> {A.go(String.append(s, SCon{Chr{34}, SNil{}}), A.ME{}, A.cls_of(sep, String.append(s, SCon{Chr{34}, SNil{}})), sep, txt, flds, rows) == A.fin(A.MQ{}, String.append(txt, s), flds, rows) : A.Ans}:
  match s:
    case SNil{}:
      %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, 34)), False{}, hq) : {A.go(SCon{Chr{34}, SNil{}}, A.ME{}, A.cls_go(False{}, False{}, _, True{}), sep, txt, flds, rows) == A.fin(A.MQ{}, String.append(txt, SNil{}), flds, rows) : A.Ans}
      %Equal.sym(String, String.append(txt, SNil{}), txt, MS.append_nil(txt)) : {A.go(SCon{Chr{34}, SNil{}}, A.ME{}, A.cls_go(False{}, False{}, False{}, True{}), sep, txt, flds, rows) == A.fin(A.MQ{}, _, flds, rows) : A.Ans}
      {==}
    case SCon{Chr{+x}, t}:
      (hqu, ht) = h
      %Equal.sym(Bool, Cmp.is_eq(U32.cmp(x, 34)), False{}, hqu) : {A.go(SCon{Chr{x}, String.append(t, SCon{Chr{34}, SNil{}})}, A.ME{}, A.cls_go(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), _), sep, txt, flds, rows) == A.fin(A.MQ{}, String.append(txt, SCon{Chr{x}, t}), flds, rows) : A.Ans}
      %MS.append_assoc(txt, SCon{Chr{x}, SNil{}}, t) : {A.go(SCon{Chr{x}, String.append(t, SCon{Chr{34}, SNil{}})}, A.ME{}, A.cls_go(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), False{}), sep, txt, flds, rows) == A.fin(A.MQ{}, _, flds, rows) : A.Ans}
      Equal.trans(A.Ans, A.go(SCon{Chr{x}, String.append(t, SCon{Chr{34}, SNil{}})}, A.ME{}, A.cls_go(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), False{}), sep, txt, flds, rows), A.go(String.append(t, SCon{Chr{34}, SNil{}}), A.ME{}, A.cls_of(sep, String.append(t, SCon{Chr{34}, SNil{}})), sep, String.append(txt, SCon{Chr{x}, SNil{}}), flds, rows), A.fin(A.MQ{}, String.append(String.append(txt, SCon{Chr{x}, SNil{}}), t), flds, rows), me_step(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), x, String.append(t, SCon{Chr{34}, SNil{}}), sep, txt, flds, rows, {==}, {==}), walk_me(sep, hq, t, ht, String.append(txt, SCon{Chr{x}, SNil{}}), flds, rows))

def Laws.abnf_quoted_field_is_its_content(sep, hq, s, h):
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, 34)), False{}, hq) : {A.go(SCon{Chr{34}, String.append(s, SCon{Chr{34}, SNil{}})}, A.MS{}, A.cls_go(False{}, False{}, _, True{}), sep, "", [], []) == A.Parsed{[[s]]} : A.Ans}
  walk_me(sep, hq, s, h, SNil{}, Nil{}, Nil{})

# ---- abnf_doubled_quote_is_one_quote ----

def Laws.abnf_doubled_quote_is_one_quote(sep, hq):
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, 34)), False{}, hq) : {A.go("\"a\"\"b\"", A.MS{}, A.cls_go(False{}, False{}, _, True{}), sep, "", [], []) == A.Parsed{[["a\"b"]]} : A.Ans}
  %Equal.sym(A.Ans, A.go("a\"\"b\"", A.ME{}, A.cls_go(False{}, False{}, Cmp.is_eq(U32.cmp(sep, 97)), False{}), sep, "", [], []), A.go("\"\"b\"", A.ME{}, A.cls_of(sep, "\"\"b\""), sep, String.append("", SCon{Chr{97}, SNil{}}), [], []), me_step(False{}, False{}, Cmp.is_eq(U32.cmp(sep, 97)), 97, "\"\"b\"", sep, "", [], [], {==}, {==})) : {_ == A.Parsed{[["a\"b"]]} : A.Ans}
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, 34)), False{}, hq) : {A.go("\"\"b\"", A.ME{}, A.cls_go(False{}, False{}, _, True{}), sep, "a", [], []) == A.Parsed{[["a\"b"]]} : A.Ans}
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, 34)), False{}, hq) : {A.go("\"b\"", A.MQ{}, A.cls_go(False{}, False{}, _, True{}), sep, "a", [], []) == A.Parsed{[["a\"b"]]} : A.Ans}
  %Equal.sym(A.Ans, A.go("b\"", A.ME{}, A.cls_go(False{}, False{}, Cmp.is_eq(U32.cmp(sep, 98)), False{}), sep, "a\"", [], []), A.go("\"", A.ME{}, A.cls_of(sep, "\""), sep, String.append("a\"", SCon{Chr{98}, SNil{}}), [], []), me_step(False{}, False{}, Cmp.is_eq(U32.cmp(sep, 98)), 98, "\"", sep, "a\"", [], [], {==}, {==})) : {_ == A.Parsed{[["a\"b"]]} : A.Ans}
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(sep, 34)), False{}, hq) : {A.go("\"", A.ME{}, A.cls_go(False{}, False{}, _, True{}), sep, "a\"b", [], []) == A.Parsed{[["a\"b"]]} : A.Ans}
  {==}

# ---- abnf_blank_line_adds_nothing ----

# ---- abnf_trailing_newline_adds_nothing ----

# ---- machinery for the trailing-newline and blank-line laws ----
#
# `Stt` is the walk's state (mode and the three accumulators); `stp` is one step of
# `go` as a function on it; `gost` runs `go` on a state; `go_step` says `go` on a
# non-empty string is `gost` on the tail from the stepped state.
type Stt is Data:
  Stt{m: A.FM, txt: String, flds: List<&2, String>, rows: List<&2, List<&2, String>>}

def gost(+t: String, +st: Stt, +sep: U32) -> A.Ans:
  match st:
    case Stt{+m, +txt, +flds, +rows}:
      A.go(t, m, A.cls_of(sep, t), sep, txt, flds, rows)

def rej(+t: String, +sep: U32, txt: String, flds: List<&2, String>, rows: List<&2, List<&2, String>>) -> {A.go(t, A.MBad{}, A.cls_of(sep, t), sep, txt, flds, rows) == A.Rejected{} : A.Ans}:
  match t:
    case SNil{}:
      {==}
    case SCon{_, _}:
      {==}

def stp(+c: Char, +m: A.FM, +k: A.CK, +txt: String, +flds: List<&2, String>, +rows: List<&2, List<&2, String>>) -> Stt:
  match m k:
    case A.MS{} A.CLf{}:
      Stt{A.MS{}, SNil{}, Nil{}, A.close_empty(flds, rows)}
    case A.MS{} A.CCr{}:
      Stt{A.MSC{}, SNil{}, flds, rows}
    case A.MS{} A.CSep{}:
      Stt{A.MS{}, SNil{}, Con{SNil{}, flds}, rows}
    case A.MS{} A.CQuote{}:
      Stt{A.ME{}, SNil{}, flds, rows}
    case A.MS{} A.CText{}:
      Stt{A.MB{}, SCon{c, SNil{}}, flds, rows}
    case A.MB{} A.CLf{}:
      Stt{A.MS{}, SNil{}, Nil{}, A.row(txt, flds, rows)}
    case A.MB{} A.CCr{}:
      Stt{A.MBC{}, txt, flds, rows}
    case A.MB{} A.CSep{}:
      Stt{A.MS{}, SNil{}, Con{txt, flds}, rows}
    case A.MB{} A.CQuote{}:
      Stt{A.MBad{}, txt, flds, rows}
    case A.MB{} A.CText{}:
      Stt{A.MB{}, String.append(txt, SCon{c, SNil{}}), flds, rows}
    case A.ME{} A.CLf{}:
      Stt{A.ME{}, String.append(txt, SCon{Chr{10}, SNil{}}), flds, rows}
    case A.ME{} A.CCr{}:
      Stt{A.ME{}, String.append(txt, SCon{Chr{13}, SNil{}}), flds, rows}
    case A.ME{} A.CSep{}:
      Stt{A.ME{}, String.append(txt, SCon{c, SNil{}}), flds, rows}
    case A.ME{} A.CQuote{}:
      Stt{A.MQ{}, txt, flds, rows}
    case A.ME{} A.CText{}:
      Stt{A.ME{}, String.append(txt, SCon{c, SNil{}}), flds, rows}
    case A.MQ{} A.CLf{}:
      Stt{A.MS{}, SNil{}, Nil{}, A.row(txt, flds, rows)}
    case A.MQ{} A.CCr{}:
      Stt{A.MQC{}, txt, flds, rows}
    case A.MQ{} A.CSep{}:
      Stt{A.MS{}, SNil{}, Con{txt, flds}, rows}
    case A.MQ{} A.CQuote{}:
      Stt{A.ME{}, String.append(txt, SCon{Chr{34}, SNil{}}), flds, rows}
    case A.MQ{} A.CText{}:
      Stt{A.MBad{}, txt, flds, rows}
    case A.MSC{} A.CLf{}:
      Stt{A.MS{}, SNil{}, Nil{}, A.close_empty(flds, rows)}
    case A.MSC{} A.CCr{}:
      Stt{A.MBC{}, SCon{Chr{13}, SNil{}}, flds, rows}
    case A.MSC{} A.CSep{}:
      Stt{A.MS{}, SNil{}, Con{SCon{Chr{13}, SNil{}}, flds}, rows}
    case A.MSC{} A.CQuote{}:
      Stt{A.MBad{}, txt, flds, rows}
    case A.MSC{} A.CText{}:
      Stt{A.MB{}, SCon{Chr{13}, SCon{c, SNil{}}}, flds, rows}
    case A.MBC{} A.CLf{}:
      Stt{A.MS{}, SNil{}, Nil{}, A.row(txt, flds, rows)}
    case A.MBC{} A.CCr{}:
      Stt{A.MBC{}, String.append(txt, SCon{Chr{13}, SNil{}}), flds, rows}
    case A.MBC{} A.CSep{}:
      Stt{A.MS{}, SNil{}, Con{String.append(txt, SCon{Chr{13}, SNil{}}), flds}, rows}
    case A.MBC{} A.CQuote{}:
      Stt{A.MBad{}, txt, flds, rows}
    case A.MBC{} A.CText{}:
      Stt{A.MB{}, String.append(String.append(txt, SCon{Chr{13}, SNil{}}), SCon{c, SNil{}}), flds, rows}
    case A.MQC{} A.CLf{}:
      Stt{A.MS{}, SNil{}, Nil{}, A.row(txt, flds, rows)}
    case A.MQC{} A.CCr{}:
      Stt{A.MBad{}, txt, flds, rows}
    case A.MQC{} A.CSep{}:
      Stt{A.MBad{}, txt, flds, rows}
    case A.MQC{} A.CQuote{}:
      Stt{A.MBad{}, txt, flds, rows}
    case A.MQC{} A.CText{}:
      Stt{A.MBad{}, txt, flds, rows}
    case A.MBad{} A.CLf{}:
      Stt{A.MBad{}, txt, flds, rows}
    case A.MBad{} A.CCr{}:
      Stt{A.MBad{}, txt, flds, rows}
    case A.MBad{} A.CSep{}:
      Stt{A.MBad{}, txt, flds, rows}
    case A.MBad{} A.CQuote{}:
      Stt{A.MBad{}, txt, flds, rows}
    case A.MBad{} A.CText{}:
      Stt{A.MBad{}, txt, flds, rows}

def go_step(+m: A.FM, +k: A.CK, +c: Char, +t: String, +sep: U32, +txt: String, +flds: List<&2, String>, +rows: List<&2, List<&2, String>>) -> {A.go(SCon{c, t}, m, k, sep, txt, flds, rows) == gost(t, stp(c, m, k, txt, flds, rows), sep) : A.Ans}:
  match m k:
    case A.MS{} A.CLf{}:
      {==}
    case A.MS{} A.CCr{}:
      {==}
    case A.MS{} A.CSep{}:
      {==}
    case A.MS{} A.CQuote{}:
      {==}
    case A.MS{} A.CText{}:
      {==}
    case A.MB{} A.CLf{}:
      {==}
    case A.MB{} A.CCr{}:
      {==}
    case A.MB{} A.CSep{}:
      {==}
    case A.MB{} A.CQuote{}:
      Equal.sym(A.Ans, A.go(t, A.MBad{}, A.cls_of(sep, t), sep, txt, flds, rows), A.Rejected{}, rej(t, sep, txt, flds, rows))
    case A.MB{} A.CText{}:
      {==}
    case A.ME{} A.CLf{}:
      {==}
    case A.ME{} A.CCr{}:
      {==}
    case A.ME{} A.CSep{}:
      {==}
    case A.ME{} A.CQuote{}:
      {==}
    case A.ME{} A.CText{}:
      {==}
    case A.MQ{} A.CLf{}:
      {==}
    case A.MQ{} A.CCr{}:
      {==}
    case A.MQ{} A.CSep{}:
      {==}
    case A.MQ{} A.CQuote{}:
      {==}
    case A.MQ{} A.CText{}:
      Equal.sym(A.Ans, A.go(t, A.MBad{}, A.cls_of(sep, t), sep, txt, flds, rows), A.Rejected{}, rej(t, sep, txt, flds, rows))
    case A.MSC{} A.CLf{}:
      {==}
    case A.MSC{} A.CCr{}:
      {==}
    case A.MSC{} A.CSep{}:
      {==}
    case A.MSC{} A.CQuote{}:
      Equal.sym(A.Ans, A.go(t, A.MBad{}, A.cls_of(sep, t), sep, txt, flds, rows), A.Rejected{}, rej(t, sep, txt, flds, rows))
    case A.MSC{} A.CText{}:
      {==}
    case A.MBC{} A.CLf{}:
      {==}
    case A.MBC{} A.CCr{}:
      {==}
    case A.MBC{} A.CSep{}:
      {==}
    case A.MBC{} A.CQuote{}:
      Equal.sym(A.Ans, A.go(t, A.MBad{}, A.cls_of(sep, t), sep, txt, flds, rows), A.Rejected{}, rej(t, sep, txt, flds, rows))
    case A.MBC{} A.CText{}:
      {==}
    case A.MQC{} A.CLf{}:
      {==}
    case A.MQC{} A.CCr{}:
      Equal.sym(A.Ans, A.go(t, A.MBad{}, A.cls_of(sep, t), sep, txt, flds, rows), A.Rejected{}, rej(t, sep, txt, flds, rows))
    case A.MQC{} A.CSep{}:
      Equal.sym(A.Ans, A.go(t, A.MBad{}, A.cls_of(sep, t), sep, txt, flds, rows), A.Rejected{}, rej(t, sep, txt, flds, rows))
    case A.MQC{} A.CQuote{}:
      Equal.sym(A.Ans, A.go(t, A.MBad{}, A.cls_of(sep, t), sep, txt, flds, rows), A.Rejected{}, rej(t, sep, txt, flds, rows))
    case A.MQC{} A.CText{}:
      Equal.sym(A.Ans, A.go(t, A.MBad{}, A.cls_of(sep, t), sep, txt, flds, rows), A.Rejected{}, rej(t, sep, txt, flds, rows))
    case A.MBad{} A.CLf{}:
      Equal.sym(A.Ans, A.go(t, A.MBad{}, A.cls_of(sep, t), sep, txt, flds, rows), A.Rejected{}, rej(t, sep, txt, flds, rows))
    case A.MBad{} A.CCr{}:
      Equal.sym(A.Ans, A.go(t, A.MBad{}, A.cls_of(sep, t), sep, txt, flds, rows), A.Rejected{}, rej(t, sep, txt, flds, rows))
    case A.MBad{} A.CSep{}:
      Equal.sym(A.Ans, A.go(t, A.MBad{}, A.cls_of(sep, t), sep, txt, flds, rows), A.Rejected{}, rej(t, sep, txt, flds, rows))
    case A.MBad{} A.CQuote{}:
      Equal.sym(A.Ans, A.go(t, A.MBad{}, A.cls_of(sep, t), sep, txt, flds, rows), A.Rejected{}, rej(t, sep, txt, flds, rows))
    case A.MBad{} A.CText{}:
      Equal.sym(A.Ans, A.go(t, A.MBad{}, A.cls_of(sep, t), sep, txt, flds, rows), A.Rejected{}, rej(t, sep, txt, flds, rows))

def tn_base(+m: A.FM, +txt: String, +flds: List<&2, String>, +rows: List<&2, List<&2, String>>, +sep: U32) -> {gost(SCon{Chr{10}, SNil{}}, Stt{m, txt, flds, rows}, sep) == gost(SNil{}, Stt{m, txt, flds, rows}, sep) : A.Ans}:
  match m:
    case A.MS{}:
      {==}
    case A.MB{}:
      {==}
    case A.ME{}:
      {==}
    case A.MQ{}:
      {==}
    case A.MSC{}:
      {==}
    case A.MBC{}:
      {==}
    case A.MQC{}:
      {==}
    case A.MBad{}:
      {==}

def tn(+sep: U32, +s: String, +st: Stt) -> {gost(String.append(s, SCon{Chr{10}, SNil{}}), st, sep) == gost(s, st, sep) : A.Ans}:
  match s st:
    case SNil{} Stt{m, txt, flds, rows}:
      tn_base(m, txt, flds, rows, sep)
    case SCon{c, t} Stt{m, txt, flds, rows}:
      Equal.trans(A.Ans, gost(String.append(SCon{c, t}, SCon{Chr{10}, SNil{}}), Stt{m, txt, flds, rows}, sep), gost(String.append(t, SCon{Chr{10}, SNil{}}), stp(c, m, A.cls_of(sep, SCon{c, t}), txt, flds, rows), sep), gost(SCon{c, t}, Stt{m, txt, flds, rows}, sep), go_step(m, A.cls_of(sep, SCon{c, t}), c, String.append(t, SCon{Chr{10}, SNil{}}), sep, txt, flds, rows), Equal.trans(A.Ans, gost(String.append(t, SCon{Chr{10}, SNil{}}), stp(c, m, A.cls_of(sep, SCon{c, t}), txt, flds, rows), sep), gost(t, stp(c, m, A.cls_of(sep, SCon{c, t}), txt, flds, rows), sep), gost(SCon{c, t}, Stt{m, txt, flds, rows}, sep), tn(sep, t, stp(c, m, A.cls_of(sep, SCon{c, t}), txt, flds, rows)), Equal.sym(A.Ans, gost(SCon{c, t}, Stt{m, txt, flds, rows}, sep), gost(t, stp(c, m, A.cls_of(sep, SCon{c, t}), txt, flds, rows), sep), go_step(m, A.cls_of(sep, SCon{c, t}), c, t, sep, txt, flds, rows))))

def Laws.abnf_trailing_newline_adds_nothing(sep, s):
  tn(sep, s, Stt{A.MS{}, SNil{}, Nil{}, Nil{}})

# ---- blank line: machinery ----
#
# NotE(m): the walk is not inside an escaped field. NotQ(k): the class is not a quote.
# A NoQuote run from a non-escaped mode never enters ME, so a blank line after it
# is the same state as the line end before it.
def NotE(+m: A.FM) -> Type:
  match m:
    case A.ME{}:
      Empty
    case _:
      Unit

def NotQ(+k: A.CK) -> Type:
  match k:
    case A.CQuote{}:
      Empty
    case _:
      Unit

def modeof(+st: Stt) -> A.FM:
  match st:
    case Stt{+m, +txt, +flds, +rows}:
      m

def cls_go_nq(+lf: Bool, +cr: Bool, +sb: Bool) -> NotQ(A.cls_go(lf, cr, sb, False{})):
  match lf cr sb:
    case True{} _ _:
      Unit{}
    case False{} True{} _:
      Unit{}
    case False{} False{} True{}:
      Unit{}
    case False{} False{} False{}:
      Unit{}

def cls_notq(+sep: U32, +x: U32, t: String, hqu: {Cmp.is_eq(U32.cmp(x, 34)) == False{} : Bool}) -> NotQ(A.cls_of(sep, SCon{Chr{x}, t})):
  %Equal.sym(Bool, Cmp.is_eq(U32.cmp(x, 34)), False{}, hqu) : NotQ(A.cls_go(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)), _))
  cls_go_nq(Cmp.is_eq(U32.cmp(x, 10)), Cmp.is_eq(U32.cmp(x, 13)), Cmp.is_eq(U32.cmp(sep, x)))

def stp_note(+c: Char, +m: A.FM, +k: A.CK, +txt: String, +flds: List<&2, String>, +rows: List<&2, List<&2, String>>, hm: NotE(m), hk: NotQ(k)) -> NotE(modeof(stp(c, m, k, txt, flds, rows))):
  match m k:
    case A.MS{} A.CLf{}:
      Unit{}
    case A.MS{} A.CCr{}:
      Unit{}
    case A.MS{} A.CSep{}:
      Unit{}
    case A.MS{} A.CQuote{}:
      match hk:
    case A.MS{} A.CText{}:
      Unit{}
    case A.MB{} A.CLf{}:
      Unit{}
    case A.MB{} A.CCr{}:
      Unit{}
    case A.MB{} A.CSep{}:
      Unit{}
    case A.MB{} A.CQuote{}:
      match hk:
    case A.MB{} A.CText{}:
      Unit{}
    case A.ME{} A.CLf{}:
      match hm:
    case A.ME{} A.CCr{}:
      match hm:
    case A.ME{} A.CSep{}:
      match hm:
    case A.ME{} A.CQuote{}:
      match hm:
    case A.ME{} A.CText{}:
      match hm:
    case A.MQ{} A.CLf{}:
      Unit{}
    case A.MQ{} A.CCr{}:
      Unit{}
    case A.MQ{} A.CSep{}:
      Unit{}
    case A.MQ{} A.CQuote{}:
      match hk:
    case A.MQ{} A.CText{}:
      Unit{}
    case A.MSC{} A.CLf{}:
      Unit{}
    case A.MSC{} A.CCr{}:
      Unit{}
    case A.MSC{} A.CSep{}:
      Unit{}
    case A.MSC{} A.CQuote{}:
      match hk:
    case A.MSC{} A.CText{}:
      Unit{}
    case A.MBC{} A.CLf{}:
      Unit{}
    case A.MBC{} A.CCr{}:
      Unit{}
    case A.MBC{} A.CSep{}:
      Unit{}
    case A.MBC{} A.CQuote{}:
      match hk:
    case A.MBC{} A.CText{}:
      Unit{}
    case A.MQC{} A.CLf{}:
      Unit{}
    case A.MQC{} A.CCr{}:
      Unit{}
    case A.MQC{} A.CSep{}:
      Unit{}
    case A.MQC{} A.CQuote{}:
      match hk:
    case A.MQC{} A.CText{}:
      Unit{}
    case A.MBad{} A.CLf{}:
      Unit{}
    case A.MBad{} A.CCr{}:
      Unit{}
    case A.MBad{} A.CSep{}:
      Unit{}
    case A.MBad{} A.CQuote{}:
      match hk:
    case A.MBad{} A.CText{}:
      Unit{}

def stpS(+c: Char, +st: Stt, +k: A.CK) -> Stt:
  match st:
    case Stt{+m, +txt, +flds, +rows}:
      stp(c, m, k, txt, flds, rows)

def stpS_note(+c: Char, +st: Stt, +k: A.CK, hm: NotE(modeof(st)), hk: NotQ(k)) -> NotE(modeof(stpS(c, st, k))):
  match st:
    case Stt{+m, +txt, +flds, +rows}:
      stp_note(c, m, k, txt, flds, rows, hm, hk)

def go_stepS(+c: Char, +t: String, +st: Stt, +sep: U32) -> {gost(SCon{c, t}, st, sep) == gost(t, stpS(c, st, A.cls_of(sep, SCon{c, t})), sep) : A.Ans}:
  match st:
    case Stt{+m, +txt, +flds, +rows}:
      go_step(m, A.cls_of(sep, SCon{c, t}), c, t, sep, txt, flds, rows)

def bl_base2(+m: A.FM, +sep: U32, +txt: String, +flds: List<&2, String>, +rows: List<&2, List<&2, String>>, hm: NotE(m), +b: String) -> {gost(SCon{Chr{10}, SCon{Chr{10}, b}}, Stt{m, txt, flds, rows}, sep) == gost(SCon{Chr{10}, b}, Stt{m, txt, flds, rows}, sep) : A.Ans}:
  match m:
    case A.MS{}:
      {==}
    case A.MB{}:
      {==}
    case A.ME{}:
      match hm:
    case A.MQ{}:
      {==}
    case A.MSC{}:
      {==}
    case A.MBC{}:
      {==}
    case A.MQC{}:
      {==}
    case A.MBad{}:
      {==}

def bl_base(+st: Stt, +sep: U32, hm: NotE(modeof(st)), +b: String) -> {gost(SCon{Chr{10}, SCon{Chr{10}, b}}, st, sep) == gost(SCon{Chr{10}, b}, st, sep) : A.Ans}:
  match st:
    case Stt{+m, +txt, +flds, +rows}:
      bl_base2(m, sep, txt, flds, rows, hm, b)

def bl(+sep: U32, +a: String, ha: Laws.NoQuote(a), +st: Stt, hst: NotE(modeof(st)), +b: String) -> {gost(String.append(a, SCon{Chr{10}, SCon{Chr{10}, b}}), st, sep) == gost(String.append(a, SCon{Chr{10}, b}), st, sep) : A.Ans}:
  match a:
    case SNil{}:
      bl_base(st, sep, hst, b)
    case SCon{Chr{+x}, t}:
      (hqu, ht) = ha
      Equal.trans(A.Ans, gost(String.append(SCon{Chr{x}, t}, SCon{Chr{10}, SCon{Chr{10}, b}}), st, sep), gost(String.append(t, SCon{Chr{10}, SCon{Chr{10}, b}}), stpS(Chr{x}, st, A.cls_of(sep, SCon{Chr{x}, t})), sep), gost(String.append(SCon{Chr{x}, t}, SCon{Chr{10}, b}), st, sep), go_stepS(Chr{x}, String.append(t, SCon{Chr{10}, SCon{Chr{10}, b}}), st, sep), Equal.trans(A.Ans, gost(String.append(t, SCon{Chr{10}, SCon{Chr{10}, b}}), stpS(Chr{x}, st, A.cls_of(sep, SCon{Chr{x}, t})), sep), gost(String.append(t, SCon{Chr{10}, b}), stpS(Chr{x}, st, A.cls_of(sep, SCon{Chr{x}, t})), sep), gost(String.append(SCon{Chr{x}, t}, SCon{Chr{10}, b}), st, sep), bl(sep, t, ht, stpS(Chr{x}, st, A.cls_of(sep, SCon{Chr{x}, t})), stpS_note(Chr{x}, st, A.cls_of(sep, SCon{Chr{x}, t}), hst, cls_notq(sep, x, t, hqu)), b), Equal.sym(A.Ans, gost(String.append(SCon{Chr{x}, t}, SCon{Chr{10}, b}), st, sep), gost(String.append(t, SCon{Chr{10}, b}), stpS(Chr{x}, st, A.cls_of(sep, SCon{Chr{x}, t})), sep), go_stepS(Chr{x}, String.append(t, SCon{Chr{10}, b}), st, sep))))

def Laws.abnf_blank_line_adds_nothing(sep, a, b, ha, hb):
  %MS.append_assoc_sym(String.append(a, SCon{Chr{10}, SNil{}}), SCon{Chr{10}, SNil{}}, b) : {A.parse_sep(sep, _) == A.parse_sep(sep, String.append(String.append(a, SCon{Chr{10}, SNil{}}), b)) : A.Ans}
  %MS.append_assoc_sym(a, SCon{Chr{10}, SNil{}}, b) : {A.parse_sep(sep, String.append(String.append(a, SCon{Chr{10}, SNil{}}), String.append(SCon{Chr{10}, SNil{}}, b))) == A.parse_sep(sep, _) : A.Ans}
  %MS.append_assoc_sym(a, SCon{Chr{10}, SNil{}}, SCon{Chr{10}, b}) : {A.parse_sep(sep, _) == A.parse_sep(sep, String.append(a, SCon{Chr{10}, b})) : A.Ans}
  bl(sep, a, ha, Stt{A.MS{}, SNil{}, Nil{}, Nil{}}, Unit{}, b)
