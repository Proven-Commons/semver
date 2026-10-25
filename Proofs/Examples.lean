/-
  Proved example cases, each closed by `decide`: the parser and
  the comparison are programs, so a claim about two concrete
  texts is a computation the kernel can check.

  The first block is the precedence chain from section 11 of the
  specification, step by step. The second block checks that the
  valid example texts from the specification parse and print back
  word for word. The third block checks that texts the grammar
  forbids are rejected.
-/

import Semver

namespace Semver.Examples

open Semver

/-- Compare two texts: parse both, then compare. -/
def cmpTexts (a b : String) : Option Ordering :=
  (parse a.toList).bind fun x => (parse b.toList).map (compare x)

/-! ## The section 11 chain, step by step -/

theorem chain_1 : cmpTexts "1.0.0-alpha" "1.0.0-alpha.1" = some Ordering.lt := by
  decide

theorem chain_2 : cmpTexts "1.0.0-alpha.1" "1.0.0-alpha.beta" = some Ordering.lt := by
  decide

theorem chain_3 : cmpTexts "1.0.0-alpha.beta" "1.0.0-beta" = some Ordering.lt := by
  decide

theorem chain_4 : cmpTexts "1.0.0-beta" "1.0.0-beta.2" = some Ordering.lt := by
  decide

theorem chain_5 : cmpTexts "1.0.0-beta.2" "1.0.0-beta.11" = some Ordering.lt := by
  decide

theorem chain_6 : cmpTexts "1.0.0-beta.11" "1.0.0-rc.1" = some Ordering.lt := by
  decide

theorem chain_7 : cmpTexts "1.0.0-rc.1" "1.0.0" = some Ordering.lt := by
  decide

/-- The ends of the chain, compared directly. -/
theorem chain_ends : cmpTexts "1.0.0-alpha" "1.0.0" = some Ordering.lt := by
  decide

/-- A prerelease is lower than the release, read in the other
    direction as well. -/
theorem chain_back : cmpTexts "1.0.0" "1.0.0-rc.1" = some Ordering.gt := by
  decide

/-- Numbers compare by value, not by text: 11 is above 2. -/
theorem numeric_by_value : cmpTexts "1.0.0-beta.11" "1.0.0-beta.2" =
    some Ordering.gt := by
  decide

/-- The core numbers decide first: a higher patch wins over any
    prerelease question. -/
theorem core_first : cmpTexts "2.1.1" "2.1.0" = some Ordering.gt := by
  decide

/-- Build metadata changes nothing in a comparison of two parsed
    texts. -/
theorem build_ignored : cmpTexts "1.0.0+build.1" "1.0.0+other.2" =
    some Ordering.eq := by
  decide

/-! ## Valid texts from the specification parse and print back -/

theorem valid_alpha : (parse "1.0.0-alpha".toList).map print =
    some "1.0.0-alpha".toList := by decide

theorem valid_alpha_1 : (parse "1.0.0-alpha.1".toList).map print =
    some "1.0.0-alpha.1".toList := by decide

theorem valid_037 : (parse "1.0.0-0.3.7".toList).map print =
    some "1.0.0-0.3.7".toList := by decide

theorem valid_xyz : (parse "1.0.0-x-y-z.-".toList).map print =
    some "1.0.0-x-y-z.-".toList := by decide

theorem valid_build_001 : (parse "1.0.0-alpha+001".toList).map print =
    some "1.0.0-alpha+001".toList := by decide

theorem valid_build_time : (parse "1.0.0+20130313144700".toList).map print =
    some "1.0.0+20130313144700".toList := by decide

theorem valid_build_sha : (parse "1.0.0-beta+exp.sha.5114f85".toList).map print =
    some "1.0.0-beta+exp.sha.5114f85".toList := by decide

theorem valid_plain : (parse "1.0.0".toList).map print =
    some "1.0.0".toList := by decide

/-! ## Texts the grammar forbids are rejected -/

theorem invalid_leading_zero_major : parse "01.2.3".toList = none := by decide

theorem invalid_leading_zero_minor : parse "1.02.3".toList = none := by decide

theorem invalid_leading_zero_pre : parse "1.0.0-01".toList = none := by decide

theorem invalid_empty_pre_id : parse "1.0.0-alpha..1".toList = none := by decide

theorem invalid_empty_pre_and_build : parse "1.0.0-+".toList = none := by decide

theorem invalid_empty_build : parse "1.0.0+".toList = none := by decide

theorem invalid_empty_pre : parse "1.0.0-".toList = none := by decide

theorem invalid_missing_patch : parse "1.0".toList = none := by decide

theorem invalid_extra_part : parse "1.0.0.0".toList = none := by decide

theorem invalid_letter_prefix : parse "v1.2.3".toList = none := by decide

theorem invalid_underscore : parse "1.0.0-alpha_beta".toList = none := by decide

theorem invalid_empty : parse "".toList = none := by decide

theorem invalid_empty_core_part : parse "1..2".toList = none := by decide

end Semver.Examples
