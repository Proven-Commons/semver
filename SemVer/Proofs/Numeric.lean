/-
  Numbers: `Nat.toDigits 10`, which `SemVer.Spec.decimal` uses, writes exactly
  the numeric identifiers of the grammar, and `parseNumeric` reads them
  back.
-/

import SemVer.Proofs.Chars

open SemVer

namespace SemVer.Proofs

theorem digit_of_mem_toDigits {n : Nat} {c : Char} (h : c ∈ Nat.toDigits 10 n) : SemVer.Spec.Digit c := by
  have := Nat.isDigit_of_mem_toDigits (by decide) (by decide) h
  rw [Char.isDigit_iff_toNat] at this
  exact (digit_iff c).mpr this

/-- A positive number is written with a first digit other than `0`. -/
theorem toDigits_head {n : Nat} (hn : 0 < n) :
    ∃ c rest, Nat.toDigits 10 n = c :: rest ∧ c ≠ '0' := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [Nat.toDigits_eq_ite (by decide)]
    split
    · exact ⟨_, [], rfl, by simp only [ne_eq, Nat.digitChar_eq_zero]; omega⟩
    · obtain ⟨c, rest, h, hc⟩ := ih (n / 10) (by omega) (by omega)
      exact ⟨c, rest ++ _, by rw [h]; rfl, hc⟩

theorem numericIdent_cons {c : Char} {cs : List Char} :
    SemVer.Spec.NumericIdent (c :: cs) ↔ (∀ d ∈ c :: cs, SemVer.Spec.Digit d) ∧ (c ≠ '0' ∨ cs = []) := by
  constructor
  · rintro (h | ⟨c', rest, h, hc, hr⟩)
    · simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨by decide, Or.inr rfl⟩
    · simp only [List.cons.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [positiveDigit_iff_digit] at hc
      exact ⟨List.forall_mem_cons.mpr ⟨hc.1, hr⟩, Or.inl hc.2⟩
  · rintro ⟨hd, h0 | rfl⟩
    · rw [List.forall_mem_cons] at hd
      exact Or.inr ⟨c, cs, rfl, (positiveDigit_iff_digit c).mpr ⟨hd.1, h0⟩, hd.2⟩
    · by_cases hc : c = '0'
      · exact Or.inl (by rw [hc])
      · exact Or.inr ⟨c, [], rfl, (positiveDigit_iff_digit c).mpr ⟨hd c (by simp), hc⟩,
          by simp⟩

theorem numericIdent_toDigits (n : Nat) : SemVer.Spec.NumericIdent (Nat.toDigits 10 n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact Or.inl rfl
  · obtain ⟨c, rest, h, hc⟩ := toDigits_head hn
    rw [h, numericIdent_cons]
    exact ⟨fun d hd => digit_of_mem_toDigits (h ▸ hd), Or.inl hc⟩

theorem numericIdent_ne_nil {cs : List Char} (h : SemVer.Spec.NumericIdent cs) : cs ≠ [] := by
  rcases h with rfl | ⟨c, rest, rfl, _, _⟩ <;> simp

theorem numericIdent_digits {cs : List Char} (h : SemVer.Spec.NumericIdent cs) : ∀ d ∈ cs, SemVer.Spec.Digit d := by
  rcases h with rfl | ⟨c, rest, rfl, hc, hr⟩
  · decide
  · exact List.forall_mem_cons.mpr ⟨⟨by
      have := (positiveDigit_iff c).mp hc
      rw [le_iff_toNat]; exact Nat.le_trans (by decide) this.1, hc.2⟩, hr⟩

/-- Induction from the end of a list. -/
theorem snoc_induction {α : Type} {P : List α → Prop} (nil : P [])
    (snoc : ∀ r x, P r → P (r ++ [x])) (l : List α) : P l := by
  rw [← List.reverse_reverse l]
  induction l.reverse with
  | nil => exact nil
  | cons x t ih => rw [List.reverse_cons]; exact snoc _ _ ih

theorem ofDigitChars_ge (cs : List Char) (init : Nat) : init ≤ Nat.ofDigitChars 10 cs init := by
  rw [Nat.ofDigitChars_eq_ofDigitChars_zero]
  have : 0 < 10 ^ cs.length := Nat.pow_pos_iff.mpr (Or.inl (by decide))
  have : init ≤ 10 ^ cs.length * init := Nat.le_mul_of_pos_left init this
  omega

/-- Digits with a first digit other than `0` are how their value is
    written. -/
theorem toDigits_ofDigitChars_cons {c : Char} {rest : List Char} (hc : SemVer.Spec.PositiveDigit c)
    (hr : ∀ d ∈ rest, SemVer.Spec.Digit d) :
    Nat.toDigits 10 (Nat.ofDigitChars 10 (c :: rest) 0) = c :: rest := by
  have hc' := (positiveDigit_iff c).mp hc
  induction rest using snoc_induction with
  | nil =>
    rw [Nat.ofDigitChars_cons, Nat.ofDigitChars_nil, show '0'.toNat = 48 from rfl,
      Nat.mul_zero, Nat.zero_add, Nat.toDigits_of_lt_base (by omega),
      digitChar_toNat ((positiveDigit_iff_digit c).mp hc).1]
  | snoc r x ih =>
    have hx := hr x (by simp)
    have ih := ih (fun d hd => hr d (by simp [hd]))
    have hpos : 0 < Nat.ofDigitChars 10 (c :: r) 0 := by
      rw [Nat.ofDigitChars_cons]
      have := ofDigitChars_ge r (10 * 0 + (c.toNat - '0'.toNat))
      have : '0'.toNat = 48 := rfl
      omega
    have hx' := (digit_iff x).mp hx
    rw [← List.cons_append, Nat.ofDigitChars_append, Nat.ofDigitChars_cons, Nat.ofDigitChars_nil,
      ← Nat.toDigits_append_toDigits (by decide) hpos (by show x.toNat - 48 < 10; omega), ih,
      Nat.toDigits_of_lt_base (by show x.toNat - 48 < 10; omega)]
    show _ ++ [Nat.digitChar (x.toNat - 48)] = _
    rw [digitChar_toNat hx]

theorem toDigits_ofDigitChars {cs : List Char} (h : SemVer.Spec.NumericIdent cs) :
    Nat.toDigits 10 (Nat.ofDigitChars 10 cs 0) = cs := by
  rcases h with rfl | ⟨c, rest, rfl, hc, hr⟩
  · decide
  · exact toDigits_ofDigitChars_cons hc hr

theorem numericIdent_iff {cs : List Char} :
    SemVer.Spec.NumericIdent cs ↔ ∃ n, cs = Nat.toDigits 10 n :=
  ⟨fun h => ⟨_, (toDigits_ofDigitChars h).symm⟩, fun ⟨n, h⟩ => h ▸ numericIdent_toDigits n⟩

theorem all_isDigit_iff {cs : List Char} : cs.all isDigit = true ↔ ∀ d ∈ cs, SemVer.Spec.Digit d := by
  simp [List.all_eq_true, isDigit_iff]

theorem parseNumeric_eq_some {cs : List Char} {n : Nat} :
    parseNumeric cs = some n ↔ cs = Nat.toDigits 10 n := by
  cases cs with
  | nil => simp [parseNumeric, (Nat.toDigits_ne_nil).symm]
  | cons c cs =>
    have key : ((c :: cs).all isDigit && (c != '0' || cs.isEmpty)) = true ↔
        SemVer.Spec.NumericIdent (c :: cs) := by
      rw [numericIdent_cons, Bool.and_eq_true, all_isDigit_iff, Bool.or_eq_true, bne_iff_ne,
        List.isEmpty_iff]
    rw [parseNumeric]
    split
    · rename_i h
      have hn := key.mp h
      simp only [Option.some.injEq]
      constructor
      · rintro rfl; exact (toDigits_ofDigitChars hn).symm
      · intro h; rw [h, Nat.ofDigitChars_ten_toDigits]
    · rename_i h
      simp only [reduceCtorEq, false_iff]
      intro he
      exact h (key.mpr (he ▸ numericIdent_toDigits n))

theorem parseNumeric_toDigits (n : Nat) : parseNumeric (Nat.toDigits 10 n) = some n :=
  parseNumeric_eq_some.mpr rfl

end SemVer.Proofs
