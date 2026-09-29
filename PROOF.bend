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

# ---- abnf_separator_makes_two_fields ----

# ---- abnf_quoted_field_is_its_content ----

# ---- abnf_doubled_quote_is_one_quote ----

# ---- abnf_blank_line_adds_nothing ----

# ---- abnf_trailing_newline_adds_nothing ----
