/-
  Precedence: `Version.compare` against `Spec.precedence`, and the laws
  that make it an order: swapping the sides swaps the answer, it is
  transitive, and `.eq` means the same numbers and pre-release
  identifiers.
-/

import Proofs.Chars

open SemVer

namespace SemVer.Proofs

/-! ## Against the specification -/

theorem compare_nat (a b : Nat) : compare a b = Spec.numOrder a b := by
  unfold Spec.numOrder
  split
  · exact Nat.compare_eq_lt.mpr ‹_›
  · split
    · exact Nat.compare_eq_gt.mpr ‹_›
    · exact Nat.compare_eq_eq.mpr (by omega)

theorem compareAscii_eq : ∀ a b : List Char, compareAscii a b = Spec.asciiOrder a b
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [compareAscii, Spec.asciiOrder, compare_nat, Spec.numOrder, compareAscii_eq xs ys]
    split
    · rfl
    · split
      · rfl
      · rfl

theorem identCompare_eq (a b : Ident) : a.compare b = Spec.identOrder a b := by
  cases a <;> cases b <;> simp [Ident.compare, Spec.identOrder, compare_nat, compareAscii_eq]

theorem compareIdents_eq : ∀ a b : List Ident, compareIdents a b = Spec.preOrder a b
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [compareIdents, Spec.preOrder, identCompare_eq, compareIdents_eq xs ys]
    cases Spec.identOrder x y <;> rfl

theorem then_numOrder (a b : Nat) (r : Ordering) :
    (compare a b).then r = if a ≠ b then Spec.numOrder a b else r := by
  split
  · rename_i h
    have : compare a b ≠ .eq := fun e => h (Nat.compare_eq_eq.mp e)
    rw [compare_nat] at this ⊢
    revert this
    cases Spec.numOrder a b <;> simp
  · rename_i h
    rw [Nat.compare_eq_eq.mpr (Classical.not_not.mp h)]
    rfl

theorem versionCompare_eq (a b : Version) : a.compare b = Spec.precedence a b := by
  simp only [Version.compare, Spec.precedence, then_numOrder]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · cases ha : a.pre <;> cases hb : b.pre <;>
          simp [comparePre, compareIdents_eq]

/-! ## Orders in which `.eq` means equal -/

/-- `o` orders `α`: swapping the sides swaps the answer, `.lt` is
    transitive, and `.eq` means the two are equal. -/
structure LawfulOrder {α : Type} (o : α → α → Ordering) : Prop where
  eq_iff : ∀ a b, o a b = .eq ↔ a = b
  swap : ∀ a b, (o a b).swap = o b a
  lt_trans : ∀ a b c, o a b = .lt → o b c = .lt → o a c = .lt

theorem LawfulOrder.le_trans {α : Type} {o : α → α → Ordering} (h : LawfulOrder o)
    {a b c : α} (hab : o a b ≠ .gt) (hbc : o b c ≠ .gt) : o a c ≠ .gt := by
  cases e1 : o a b
  · cases e2 : o b c
    · rw [h.lt_trans a b c e1 e2]; decide
    · rw [← (h.eq_iff b c).mp e2, e1]; decide
    · exact absurd e2 hbc
  · rw [(h.eq_iff a b).mp e1]; exact hbc
  · exact absurd e1 hab

theorem lawful_nat : LawfulOrder (fun a b : Nat => compare a b) where
  eq_iff _ _ := Nat.compare_eq_eq
  swap a b := Nat.compare_swap a b
  lt_trans _ _ _ h1 h2 := Nat.compare_eq_lt.mpr
    (Nat.lt_trans (Nat.compare_eq_lt.mp h1) (Nat.compare_eq_lt.mp h2))

theorem lawful_char : LawfulOrder (fun a b : Char => compare a.toNat b.toNat) where
  eq_iff a b := by simp only [Nat.compare_eq_eq, Char.toNat_inj]
  swap a b := Nat.compare_swap _ _
  lt_trans _ _ _ h1 h2 := Nat.compare_eq_lt.mpr
    (Nat.lt_trans (Nat.compare_eq_lt.mp h1) (Nat.compare_eq_lt.mp h2))

/-- Lists by the first element that differs; a list before any longer
    list it starts. -/
def listOrder {α : Type} (o : α → α → Ordering) : List α → List α → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (o a b).then (listOrder o as bs)

theorem lawful_list {α : Type} {o : α → α → Ordering} (h : LawfulOrder o) :
    LawfulOrder (listOrder o) where
  eq_iff := by
    intro as bs
    induction as generalizing bs with
    | nil => cases bs <;> simp [listOrder]
    | cons a as ih =>
      cases bs with
      | nil => simp [listOrder]
      | cons b bs => simp [listOrder, h.eq_iff, ih]
  swap := by
    intro as bs
    induction as generalizing bs with
    | nil => cases bs <;> rfl
    | cons a as ih =>
      cases bs with
      | nil => rfl
      | cons b bs => simp [listOrder, Ordering.swap_then, h.swap, ih]
  lt_trans := by
    intro as bs cs
    induction as generalizing bs cs with
    | nil =>
      cases bs <;> cases cs <;> simp [listOrder]
    | cons a as ih =>
      cases bs with
      | nil => simp [listOrder]
      | cons b bs =>
        cases cs with
        | nil => simp [listOrder]
        | cons c cs =>
          simp only [listOrder, Ordering.then_eq_lt]
          rintro (h1 | ⟨h1, h1'⟩) (h2 | ⟨h2, h2'⟩)
          · exact Or.inl (h.lt_trans a b c h1 h2)
          · rw [← (h.eq_iff b c).mp h2]; exact Or.inl h1
          · rw [(h.eq_iff a b).mp h1]; exact Or.inl h2
          · rw [(h.eq_iff a b).mp h1]
            exact Or.inr ⟨h2, ih bs cs h1' h2'⟩

theorem compareAscii_eq_listOrder :
    ∀ a b : List Char, compareAscii a b = listOrder (fun a b : Char => compare a.toNat b.toNat) a b
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [compareAscii, listOrder, compareAscii_eq_listOrder xs ys]

theorem lawful_ascii : LawfulOrder compareAscii := by
  have h := lawful_list lawful_char
  have e : compareAscii = listOrder (fun a b : Char => compare a.toNat b.toNat) :=
    funext fun a => funext fun b => compareAscii_eq_listOrder a b
  rw [e]; exact h

theorem lawful_ident : LawfulOrder Ident.compare where
  eq_iff a b := by
    cases a <;> cases b <;>
      simp [Ident.compare, lawful_ascii.eq_iff, String.toList_inj]
  swap a b := by
    cases a <;> cases b <;> simp [Ident.compare, Nat.compare_swap, lawful_ascii.swap]
  lt_trans a b c := by
    cases a <;> cases b <;> cases c <;> simp only [Ident.compare, reduceCtorEq, imp_self,
      implies_true, false_implies]
    · exact lawful_nat.lt_trans _ _ _
    · exact lawful_ascii.lt_trans _ _ _

theorem compareIdents_eq_listOrder :
    ∀ a b : List Ident, compareIdents a b = listOrder Ident.compare a b
  | [], [] => rfl
  | [], _ :: _ => rfl
  | _ :: _, [] => rfl
  | x :: xs, y :: ys => by
    simp only [compareIdents, listOrder, compareIdents_eq_listOrder xs ys]

theorem lawful_idents : LawfulOrder compareIdents := by
  have e : compareIdents = listOrder Ident.compare :=
    funext fun a => funext fun b => compareIdents_eq_listOrder a b
  rw [e]; exact lawful_list lawful_ident

theorem lawful_pre : LawfulOrder comparePre where
  eq_iff a b := by
    cases a <;> cases b <;> simp [comparePre, lawful_idents.eq_iff]
  swap a b := by
    cases a <;> cases b <;> simp [comparePre, lawful_idents.swap]
  lt_trans a b c := by
    cases a <;> cases b <;> cases c <;> simp only [comparePre, reduceCtorEq, imp_self,
      implies_true, false_implies]
    exact lawful_idents.lt_trans _ _ _

/-- Pairs, by the first part and then the second. -/
def pairOrder {α β : Type} (o₁ : α → α → Ordering) (o₂ : β → β → Ordering) :
    α × β → α × β → Ordering :=
  fun x y => (o₁ x.1 y.1).then (o₂ x.2 y.2)

theorem lawful_pair {α β : Type} {o₁ : α → α → Ordering} {o₂ : β → β → Ordering}
    (h₁ : LawfulOrder o₁) (h₂ : LawfulOrder o₂) : LawfulOrder (pairOrder o₁ o₂) where
  eq_iff x y := by
    simp [pairOrder, h₁.eq_iff, h₂.eq_iff, Prod.ext_iff]
  swap x y := by
    simp [pairOrder, Ordering.swap_then, h₁.swap, h₂.swap]
  lt_trans x y z := by
    simp only [pairOrder, Ordering.then_eq_lt]
    rintro (h1 | ⟨h1, h1'⟩) (h2 | ⟨h2, h2'⟩)
    · exact Or.inl (h₁.lt_trans _ _ _ h1 h2)
    · rw [← (h₁.eq_iff _ _).mp h2]; exact Or.inl h1
    · rw [(h₁.eq_iff _ _).mp h1]; exact Or.inl h2
    · rw [(h₁.eq_iff _ _).mp h1]
      exact Or.inr ⟨h2, h₂.lt_trans _ _ _ h1' h2'⟩

/-- What precedence reads of a version. -/
def key (v : Version) : Nat × Nat × Nat × List Ident := (v.major, v.minor, v.patch, v.pre)

/-- The order on keys. -/
def keyOrder : Nat × Nat × Nat × List Ident → Nat × Nat × Nat × List Ident → Ordering :=
  pairOrder (fun a b : Nat => compare a b)
    (pairOrder (fun a b : Nat => compare a b) (pairOrder (fun a b : Nat => compare a b) comparePre))

theorem lawful_key : LawfulOrder keyOrder :=
  lawful_pair lawful_nat (lawful_pair lawful_nat (lawful_pair lawful_nat lawful_pre))

theorem compare_key (a b : Version) : a.compare b = keyOrder (key a) (key b) := rfl

end SemVer.Proofs
