/-
  Proved example cases, each closed by `decide`: the parser and
  the comparison are programs, so a claim about two concrete
  texts is a computation the kernel can check.

  The first block is the ordering example chain printed in
  PEP 440, step by step. The second block checks that different
  spellings of one version compare equal. The third block
  checks that valid texts parse and print back in canonical
  form. The fourth block checks that texts the grammar forbids
  are rejected.
-/

import Pep440

namespace Pep440.Examples

open Pep440

/-- Compare two texts: parse both, then compare. -/
def cmpTexts (a b : String) : Option Ordering :=
  (parse a.toList).bind fun x => (parse b.toList).map (compare x)

/-! ## The PEP 440 example chain, step by step -/

theorem chain_1 : cmpTexts "1.0.dev456" "1.0a1" = some Ordering.lt := by
  decide

theorem chain_2 : cmpTexts "1.0a1" "1.0a2.dev456" = some Ordering.lt := by
  decide

theorem chain_3 : cmpTexts "1.0a2.dev456" "1.0a12.dev456" = some Ordering.lt := by
  decide

theorem chain_4 : cmpTexts "1.0a12.dev456" "1.0a12" = some Ordering.lt := by
  decide

theorem chain_5 : cmpTexts "1.0a12" "1.0b1.dev456" = some Ordering.lt := by
  decide

theorem chain_6 : cmpTexts "1.0b1.dev456" "1.0b2" = some Ordering.lt := by
  decide

theorem chain_7 : cmpTexts "1.0b2" "1.0b2.post345.dev456" = some Ordering.lt := by
  decide

theorem chain_8 : cmpTexts "1.0b2.post345.dev456" "1.0b2.post345" =
    some Ordering.lt := by
  decide

theorem chain_9 : cmpTexts "1.0b2.post345" "1.0rc1.dev456" = some Ordering.lt := by
  decide

theorem chain_10 : cmpTexts "1.0rc1.dev456" "1.0rc1" = some Ordering.lt := by
  decide

theorem chain_11 : cmpTexts "1.0rc1" "1.0" = some Ordering.lt := by
  decide

theorem chain_12 : cmpTexts "1.0" "1.0.post456.dev34" = some Ordering.lt := by
  decide

theorem chain_13 : cmpTexts "1.0.post456.dev34" "1.0.post456" =
    some Ordering.lt := by
  decide

theorem chain_14 : cmpTexts "1.0.post456" "1.1.dev1" = some Ordering.lt := by
  decide

/-- The shorter example chain the claim names, step by step:
    a dev release alone, then with a pre-release, then the
    pre-release itself. -/
theorem mini_chain_1 : cmpTexts "1.0.dev1" "1.0a1.dev1" = some Ordering.lt := by
  decide

theorem mini_chain_2 : cmpTexts "1.0a1.dev1" "1.0a1" = some Ordering.lt := by
  decide

theorem mini_chain_3 : cmpTexts "1.0" "1.0.post1.dev1" = some Ordering.lt := by
  decide

theorem mini_chain_4 : cmpTexts "1.0.post1.dev1" "1.0.post1" =
    some Ordering.lt := by
  decide

/-- The ends of the chain, compared directly. -/
theorem chain_ends : cmpTexts "1.0.dev456" "1.1.dev1" = some Ordering.lt := by
  decide

/-- One step of the chain read in the other direction. -/
theorem chain_back : cmpTexts "1.0" "1.0rc1" = some Ordering.gt := by
  decide

/-! ## Different spellings of one version compare equal -/

/-- A release padded with a zero is the same version. -/
theorem eq_release_pad : cmpTexts "1.0" "1.0.0" = some Ordering.eq := by
  decide

/-- The spelling alpha reads as the kind a. -/
theorem eq_alpha_spelling : cmpTexts "1.0a1" "1.0.alpha1" = some Ordering.eq := by
  decide

/-- Leading zeros carry no value. -/
theorem eq_leading_zeros : cmpTexts "1.0a1" "1.0a01" = some Ordering.eq := by
  decide

/-- A leading v is accepted and changes nothing. -/
theorem eq_leading_v : cmpTexts "v1.0" "1.0" = some Ordering.eq := by
  decide

/-- The spelling c reads as the kind rc. -/
theorem eq_c_spelling : cmpTexts "1.0c1" "1.0rc1" = some Ordering.eq := by
  decide

/-- An epoch with a padded release is the same version. -/
theorem eq_epoch_pad : cmpTexts "1!1.0" "1!1.0.0" = some Ordering.eq := by
  decide

/-- The spellings are matched without case. -/
theorem eq_case : cmpTexts "1.0A1" "1.0a1" = some Ordering.eq := by
  decide

/-- The implicit post form, a hyphen and a number, reads as
    the labelled post with that number. -/
theorem eq_implicit_post : cmpTexts "1.0-1" "1.0.post1" = some Ordering.eq := by
  decide

/-! ## Valid texts parse and print back in canonical form -/

theorem reprint_alpha : (parse "1.0.alpha1".toList).map print =
    some "1.0.a1".toList := by decide

theorem reprint_implicit_post : (parse "1.0-1".toList).map print =
    some "1.0.post1".toList := by decide

theorem reprint_v_case : (parse "v2.0RC1".toList).map print =
    some "2.0.rc1".toList := by decide

theorem reprint_chain_member : (parse "1.0b2.post345.dev456".toList).map print =
    some "1.0.b2.post345.dev456".toList := by decide

theorem reprint_epoch : (parse "1!1.0".toList).map print =
    some "1!1.0".toList := by decide

theorem reprint_dev_only : (parse "1.0.dev456".toList).map print =
    some "1.0.dev456".toList := by decide

theorem reprint_post_dev : (parse "1.0.post456.dev34".toList).map print =
    some "1.0.post456.dev34".toList := by decide

theorem reprint_plain : (parse "1.0".toList).map print =
    some "1.0".toList := by decide

theorem reprint_underscore : (parse "1.0_a1".toList).map print =
    some "1.0.a1".toList := by decide

theorem reprint_pre_post_dash : (parse "1.0a1-2".toList).map print =
    some "1.0.a1.post2".toList := by decide

/-! ## Texts the grammar forbids are rejected -/

theorem invalid_empty : parse "".toList = none := by decide

theorem invalid_local : parse "1.0+local".toList = none := by decide

theorem invalid_empty_release_part : parse "1.0..1".toList = none := by decide

theorem invalid_trailing_dot : parse "1.".toList = none := by decide

theorem invalid_leading_dot : parse ".1".toList = none := by decide

theorem invalid_letter_after_pre_number : parse "1.0a1b2".toList = none := by
  decide

theorem invalid_lone_bang : parse "1.0!".toList = none := by decide

theorem invalid_second_bang : parse "1!1.0!2".toList = none := by decide

theorem invalid_trailing_dash : parse "1.0-".toList = none := by decide

theorem invalid_pre_after_post : parse "1.0.post1a1".toList = none := by decide

theorem invalid_post_after_dev : parse "1.0dev1.post1".toList = none := by decide

theorem invalid_underscore_number : parse "1.0_1".toList = none := by decide

theorem invalid_double_dash : parse "1.0--a1".toList = none := by decide

theorem invalid_leading_space : parse " 1.0".toList = none := by decide

theorem invalid_trailing_space : parse "1.0 ".toList = none := by decide

theorem invalid_underscore_in_pre_number : parse "1.0a1_2".toList = none := by
  decide

theorem invalid_letter_prefix : parse "x1.0".toList = none := by decide

theorem invalid_dash_after_post : parse "1.0a1.post1-2".toList = none := by
  decide

end Pep440.Examples
