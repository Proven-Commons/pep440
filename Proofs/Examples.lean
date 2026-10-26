/-
  Proved example cases, each closed by `decide`: the parser and
  the comparison are programs, so a claim about two concrete
  texts is a computation the kernel can check.

  The first block is the ordering example chain printed in
  PEP 440, step by step. The second block checks that different
  spellings of one version compare equal. The third block
  checks that valid texts parse and print back in canonical
  form. The fourth block checks that texts the grammar forbids
  are rejected. A fifth block checks the local part: its
  ordering rules, its canonical reprints, equal spellings of
  one local part, and the local texts the grammar forbids.
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

/-! ## The local part: ordering, reprints, and rejections -/

/-- A version with no local part sorts before the same
    version with one. -/
theorem local_absent_first : cmpTexts "1.0" "1.0+1" = some Ordering.lt := by
  decide

/-- A text segment sorts before a number segment: the PEP's
    words are that a numeric segment always compares as
    greater than a lexicographic one. -/
theorem local_text_below_num : cmpTexts "1.0+abc" "1.0+1" =
    some Ordering.lt := by
  decide

/-- The prefix rule: a local part that is a prefix of another
    sorts first. -/
theorem local_prefix : cmpTexts "1.0+abc" "1.0+abc.1" = some Ordering.lt := by
  decide

/-- Two number segments compare by value. -/
theorem local_num_order : cmpTexts "1.0+1" "1.0+2" = some Ordering.lt := by
  decide

/-- An alphanumeric segment is a text segment, so it too
    sorts before a number segment. -/
theorem local_alnum_below_num : cmpTexts "1.0+a1" "1.0+1" =
    some Ordering.lt := by
  decide

/-- Two text segments compare in character order. -/
theorem local_text_order : cmpTexts "1.0+abc" "1.0+abd" =
    some Ordering.lt := by
  decide

/-- Letter case in a local part carries no value: text
    segments are held lowercase. -/
theorem local_eq_case : cmpTexts "1.0+ABC" "1.0+abc" = some Ordering.eq := by
  decide

/-- The segment separators are one in the value: a hyphen and
    a dot split a local part the same way. -/
theorem local_eq_seps : cmpTexts "1.0+foo-bar" "1.0+foo.bar" =
    some Ordering.eq := by
  decide

/-- Leading zeros in a number segment carry no value. -/
theorem local_eq_zeros : cmpTexts "1.0+007" "1.0+7" = some Ordering.eq := by
  decide

theorem reprint_local_plain : (parse "1.0+local".toList).map print =
    some "1.0+local".toList := by decide

theorem reprint_local_case : (parse "1.0+ABC".toList).map print =
    some "1.0+abc".toList := by decide

theorem reprint_local_seps : (parse "1.0+foo-bar_baz".toList).map print =
    some "1.0+foo.bar.baz".toList := by decide

theorem reprint_local_zeros : (parse "1.0+007".toList).map print =
    some "1.0+7".toList := by decide

theorem reprint_local_after_pre : (parse "1.0a1+ubuntu.1".toList).map print =
    some "1.0.a1+ubuntu.1".toList := by decide

/-- A plus with nothing after it is rejected. -/
theorem invalid_local_empty : parse "1.0+".toList = none := by decide

/-- An empty segment is rejected. -/
theorem invalid_local_empty_segment : parse "1.0+a..b".toList = none := by
  decide

/-- A trailing separator is rejected: it opens a segment
    that is not there. -/
theorem invalid_local_trailing_sep : parse "1.0+a.".toList = none := by
  decide

/-- A separator right after the plus is rejected the same
    way. -/
theorem invalid_local_leading_sep : parse "1.0+.a".toList = none := by
  decide

/-- A second plus inside a local part is rejected. -/
theorem invalid_local_second_plus : parse "1.0+a+b".toList = none := by
  decide

/-- A plus right after the first one is rejected too. -/
theorem invalid_local_double_plus : parse "1.0++a".toList = none := by
  decide

/-- A character outside letters, digits, and the separators
    is rejected. -/
theorem invalid_local_bad_char : parse "1.0+a$b".toList = none := by decide

end Pep440.Examples
