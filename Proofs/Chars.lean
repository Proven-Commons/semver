/-
  Character classes: the code's `isDigit` and `isIdentChar` against the
  specification's `Spec.Digit` and `Spec.IdentChar`, and the digit
  characters against their values.
-/

import SemVer
import Spec.Defs

open SemVer

namespace SemVer.Proofs

theorem le_iff_toNat {a b : Char} : a ≤ b ↔ a.toNat ≤ b.toNat := by
  rw [Char.le_def, UInt32.le_iff_toNat_le]; rfl

theorem digit_iff (c : Char) : Spec.Digit c ↔ 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  simp only [Spec.Digit, le_iff_toNat]; rfl

theorem positiveDigit_iff (c : Char) : Spec.PositiveDigit c ↔ 49 ≤ c.toNat ∧ c.toNat ≤ 57 := by
  simp only [Spec.PositiveDigit, le_iff_toNat]; rfl

theorem letter_iff (c : Char) :
    Spec.Letter c ↔ (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨ (97 ≤ c.toNat ∧ c.toNat ≤ 122) := by
  simp only [Spec.Letter, le_iff_toNat]; rfl

theorem eq_hyphen_iff (c : Char) : c = '-' ↔ c.toNat = 45 := by
  rw [← Char.toNat_inj]; rfl

theorem isDigit_iff (c : Char) : isDigit c = true ↔ Spec.Digit c := by
  simp [isDigit, Spec.Digit]

theorem isIdentChar_iff (c : Char) : isIdentChar c = true ↔ Spec.IdentChar c := by
  simp only [isIdentChar, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    isDigit_iff, Spec.IdentChar, Spec.NonDigit, Spec.Letter, or_assoc]

theorem nonDigit_iff (c : Char) : Spec.NonDigit c ↔ Spec.IdentChar c ∧ ¬ Spec.Digit c := by
  simp only [Spec.IdentChar, Spec.NonDigit, letter_iff, digit_iff, eq_hyphen_iff]
  omega

theorem positiveDigit_iff_digit (c : Char) :
    Spec.PositiveDigit c ↔ Spec.Digit c ∧ c ≠ '0' := by
  rw [positiveDigit_iff, digit_iff, Ne, ← Char.toNat_inj]
  show _ ↔ _ ∧ ¬ c.toNat = 48
  omega

theorem digit_identChar {c : Char} (h : Spec.Digit c) : Spec.IdentChar c := Or.inl h

/-- A digit character is the character for its value. -/
theorem digitChar_toNat {c : Char} (h : Spec.Digit c) : Nat.digitChar (c.toNat - 48) = c := by
  rw [digit_iff] at h
  rw [← Char.toNat_inj, Nat.toNat_digitChar_of_lt_ten (by omega)]
  omega

theorem digit_digitChar {n : Nat} (h : n < 10) : Spec.Digit (Nat.digitChar n) := by
  rw [digit_iff, Nat.toNat_digitChar_of_lt_ten h]; omega

/-- Characters the separators of the format use are not identifier
    characters. -/
theorem not_identChar_dot : ¬ Spec.IdentChar '.' := by decide
theorem not_identChar_plus : ¬ Spec.IdentChar '+' := by decide
theorem not_digit_hyphen : ¬ Spec.Digit '-' := by decide
theorem not_digit_dot : ¬ Spec.Digit '.' := by decide
theorem not_digit_plus : ¬ Spec.Digit '+' := by decide

end SemVer.Proofs
