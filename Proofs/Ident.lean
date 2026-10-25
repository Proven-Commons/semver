/-
  Identifiers: `parsePreIdent` and `parseBuildIdent` against the
  grammar's `<pre-release identifier>` and `<build identifier>`.
-/

import Proofs.Numeric
import Proofs.Lists

open SemVer

namespace SemVer.Proofs

theorem all_isIdentChar_iff {cs : List Char} :
    cs.all isIdentChar = true ↔ ∀ d ∈ cs, Spec.IdentChar d := by
  simp [List.all_eq_true, isIdentChar_iff]

/-- `<alphanumeric identifier>`: identifier characters, not all of them
    digits. -/
theorem alnumIdent_iff {cs : List Char} :
    Spec.AlnumIdent cs ↔ (∀ d ∈ cs, Spec.IdentChar d) ∧ ¬ ∀ d ∈ cs, Spec.Digit d := by
  constructor
  · rintro ⟨xs, c, ys, rfl, hc, hxs, hys⟩
    have hc' := (nonDigit_iff c).mp hc
    refine ⟨?_, fun h => hc'.2 (h c (by simp))⟩
    intro d hd
    simp only [List.mem_append, List.mem_cons] at hd
    rcases hd with hd | rfl | hd
    · exact hxs d hd
    · exact hc'.1
    · exact hys d hd
  · rintro ⟨hi, hd⟩
    simp only [Classical.not_forall, exists_prop] at hd
    obtain ⟨c, hc, hnd⟩ := hd
    obtain ⟨xs, ys, rfl⟩ := List.append_of_mem hc
    refine ⟨xs, c, ys, rfl, (nonDigit_iff c).mpr ⟨hi c hc, hnd⟩, ?_, ?_⟩
    · exact fun d hd => hi d (by simp [hd])
    · exact fun d hd => hi d (by simp [hd])

/-- `<build identifier>`: one or more identifier characters. -/
theorem buildIdent_iff {cs : List Char} :
    Spec.BuildIdent cs ↔ cs ≠ [] ∧ ∀ d ∈ cs, Spec.IdentChar d := by
  constructor
  · rintro (h | ⟨hne, hd⟩)
    · refine ⟨?_, (alnumIdent_iff.mp h).1⟩
      obtain ⟨xs, c, ys, rfl, -, -, -⟩ := h
      simp
    · exact ⟨hne, fun d h => digit_identChar (hd d h)⟩
  · rintro ⟨hne, hi⟩
    by_cases hd : ∀ d ∈ cs, Spec.Digit d
    · exact Or.inr ⟨hne, hd⟩
    · exact Or.inl (alnumIdent_iff.mpr ⟨hi, hd⟩)

theorem identChar_of_validIdent {i : Ident} (h : Spec.ValidIdent i) :
    ∀ d ∈ Spec.identChars i, Spec.IdentChar d := by
  cases i with
  | num n => exact fun d hd => digit_identChar (digit_of_mem_toDigits hd)
  | alnum s => exact (alnumIdent_iff.mp h).1

theorem parsePreIdent_eq_some {cs : List Char} {i : Ident} :
    parsePreIdent cs = some i ↔ Spec.ValidIdent i ∧ cs = Spec.identChars i := by
  unfold parsePreIdent
  split
  · rename_i hd
    rw [all_isDigit_iff] at hd
    cases i with
    | num n =>
      simp only [Option.map_eq_some_iff, Ident.num.injEq, exists_eq_right, Spec.ValidIdent,
        true_and, Spec.identChars, Spec.decimal]
      exact parseNumeric_eq_some
    | alnum s =>
      simp only [Option.map_eq_some_iff, reduceCtorEq, and_false, exists_false, false_iff,
        not_and, Spec.ValidIdent, Spec.identChars]
      rintro h rfl
      exact (alnumIdent_iff.mp h).2 hd
  · rename_i hd
    rw [all_isDigit_iff] at hd
    split
    · rename_i hi
      rw [all_isIdentChar_iff] at hi
      cases i with
      | num n =>
        simp only [Option.some.injEq, reduceCtorEq, Spec.ValidIdent, Spec.identChars,
          Spec.decimal, true_and, false_iff]
        rintro rfl
        exact hd (fun d h => digit_of_mem_toDigits h)
      | alnum s =>
        simp only [Option.some.injEq, Ident.alnum.injEq, Spec.ValidIdent, Spec.identChars]
        constructor
        · rintro rfl
          rw [String.toList_ofList]
          exact ⟨alnumIdent_iff.mpr ⟨hi, hd⟩, rfl⟩
        · rintro ⟨-, rfl⟩
          exact String.ofList_toList
    · rename_i hi
      rw [all_isIdentChar_iff] at hi
      simp only [reduceCtorEq, false_iff, not_and]
      rintro hv rfl
      exact hi (identChar_of_validIdent hv)

theorem parseBuildIdent_eq_some {cs : List Char} {s : String} :
    parseBuildIdent cs = some s ↔ Spec.BuildIdent s.toList ∧ cs = s.toList := by
  unfold parseBuildIdent
  split
  · rename_i h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      all_isIdentChar_iff] at h
    simp only [Option.some.injEq]
    constructor
    · rintro rfl
      rw [String.toList_ofList]
      exact ⟨buildIdent_iff.mpr h, rfl⟩
    · rintro ⟨-, rfl⟩
      exact String.ofList_toList
  · rename_i h
    simp only [reduceCtorEq, false_iff, not_and]
    rintro hb rfl
    apply h
    simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff,
      all_isIdentChar_iff]
    exact buildIdent_iff.mp hb

/-! ## Separators inside identifiers -/

theorem not_mem_of_identChar {c : Char} (hc : ¬ Spec.IdentChar c) {cs : List Char}
    (h : ∀ d ∈ cs, Spec.IdentChar d) : c ∉ cs :=
  fun hm => hc (h c hm)

theorem dot_not_mem_identChars {i : Ident} (h : Spec.ValidIdent i) : '.' ∉ Spec.identChars i :=
  not_mem_of_identChar not_identChar_dot (identChar_of_validIdent h)

theorem plus_not_mem_identChars {i : Ident} (h : Spec.ValidIdent i) : '+' ∉ Spec.identChars i :=
  not_mem_of_identChar not_identChar_plus (identChar_of_validIdent h)

theorem dot_not_mem_build {s : String} (h : Spec.BuildIdent s.toList) : '.' ∉ s.toList :=
  not_mem_of_identChar not_identChar_dot (buildIdent_iff.mp h).2

theorem plus_not_mem_build {s : String} (h : Spec.BuildIdent s.toList) : '+' ∉ s.toList :=
  not_mem_of_identChar not_identChar_plus (buildIdent_iff.mp h).2

theorem not_mem_toDigits {c : Char} (hc : ¬ Spec.Digit c) (n : Nat) : c ∉ Nat.toDigits 10 n :=
  fun hm => hc (digit_of_mem_toDigits hm)

end SemVer.Proofs
