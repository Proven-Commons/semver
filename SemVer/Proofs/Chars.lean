/-
  Character classes: the code's `isDigit` and `isIdentChar` against the
  specification's `SemVer.Spec.Digit` and `SemVer.Spec.IdentChar`, and the digit
  characters against their values.
-/

import SemVer
import SemVer.Spec.Defs

open SemVer

namespace SemVer.Proofs

theorem le_iff_toNat {a b : Char} : a ≤ b ↔ a.toNat ≤ b.toNat := by
  rw [Char.le_def, UInt32.le_iff_toNat_le]; rfl

theorem digit_iff (c : Char) : SemVer.Spec.Digit c ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  simp only [SemVer.Spec.Digit, le_iff_toNat]; rfl

theorem positiveDigit_iff (c : Char) : SemVer.Spec.PositiveDigit c ↔ 49 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  simp only [SemVer.Spec.PositiveDigit, le_iff_toNat]; rfl

theorem letter_iff (c : Char) :
    SemVer.Spec.Letter c ↔ (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨ (97 ≤ c.toNat ∧ c.toNat ≤ 122) := by
  simp only [SemVer.Spec.Letter, le_iff_toNat]; rfl

theorem eq_hyphen_iff (c : Char) : c = '-' ↔ c.toNat = 45 := by
  rw [← Char.toNat_inj]; rfl

theorem isDigit_iff (c : Char) : isDigit c = true ↔ SemVer.Spec.Digit c := by
  simp [isDigit, SemVer.Spec.Digit]

theorem isIdentChar_iff (c : Char) : isIdentChar c = true ↔ SemVer.Spec.IdentChar c := by
  simp only [isIdentChar, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    isDigit_iff, SemVer.Spec.IdentChar, SemVer.Spec.NonDigit, SemVer.Spec.Letter, or_assoc]

theorem nonDigit_iff (c : Char) : SemVer.Spec.NonDigit c ↔ SemVer.Spec.IdentChar c ∧ ¬ SemVer.Spec.Digit c := by
  simp only [SemVer.Spec.IdentChar, SemVer.Spec.NonDigit, letter_iff, digit_iff, eq_hyphen_iff]
  omega

theorem positiveDigit_iff_digit (c : Char) :
    SemVer.Spec.PositiveDigit c ↔ SemVer.Spec.Digit c ∧ c ≠ '0' := by
  rw [positiveDigit_iff, digit_iff, Ne, ← Char.toNat_inj]
  show _ ↔ _ ∧ ¬ c.toNat = 48
  omega

theorem digit_identChar {c : Char} (h : SemVer.Spec.Digit c) : SemVer.Spec.IdentChar c := Or.inl h

/-- A digit character is the character for its value. -/
theorem digitChar_toNat {c : Char} (h : SemVer.Spec.Digit c) : Nat.digitChar (c.toNat - 48) = c := by
  rw [digit_iff] at h
  rw [← Char.toNat_inj, Nat.toNat_digitChar_of_lt_ten (by omega)]
  omega

theorem digit_digitChar {n : Nat} (h : n < 10) : SemVer.Spec.Digit (Nat.digitChar n) := by
  rw [digit_iff, Nat.toNat_digitChar_of_lt_ten h]; omega

/-- Characters the separators of the format use are not identifier
    characters. -/
theorem not_identChar_dot : ¬ SemVer.Spec.IdentChar '.' := by decide
theorem not_identChar_plus : ¬ SemVer.Spec.IdentChar '+' := by decide
theorem not_digit_hyphen : ¬ SemVer.Spec.Digit '-' := by decide
theorem not_digit_dot : ¬ SemVer.Spec.Digit '.' := by decide
theorem not_digit_plus : ¬ SemVer.Spec.Digit '+' := by decide

end SemVer.Proofs
