/-
  The list functions the parser uses: `breakAt`, `parseEach`, and
  `List.splitOn` with `List.intercalate` from Lean core.
-/

import SemVer

open SemVer

namespace SemVer.Proofs

/-- The text after a separator, with the separator, when there is one. -/
def after (sep : Char) : Option (List Char) → List Char
  | none => []
  | some b => sep :: b

theorem breakAt_spec {sep : Char} {cs a : List Char} {r : Option (List Char)}
    (h : breakAt sep cs = (a, r)) : sep ∉ a ∧ cs = a ++ after sep r := by
  induction cs generalizing a r with
  | nil =>
    simp only [breakAt, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [after]
  | cons c cs ih =>
    simp only [breakAt] at h
    split at h
    · rename_i hc
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      subst hc
      simp [after]
    · rename_i hc
      obtain ⟨h1, h2⟩ := ih (a := (breakAt sep cs).1) (r := (breakAt sep cs).2) rfl
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, ?_⟩
      · simp only [List.mem_cons, not_or]
        exact ⟨fun e => hc e.symm, h1⟩
      · rw [List.cons_append]
        exact congrArg (c :: ·) h2

theorem breakAt_append {sep : Char} {a : List Char} (r : Option (List Char)) (h : sep ∉ a) :
    breakAt sep (a ++ after sep r) = (a, r) := by
  induction a with
  | nil => cases r <;> simp [after, breakAt]
  | cons c a ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [List.cons_append, breakAt, Ne.symm h.1, ite_false, ih h.2]

theorem parseEach_cons_eq_some {α : Type} {f : List Char → Option α} {p : List Char}
    {ps : List (List Char)} {ys : List α} :
    parseEach f (p :: ps) = some ys ↔
      ∃ x xs, ys = x :: xs ∧ f p = some x ∧ parseEach f ps = some xs := by
  simp only [parseEach, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq]
  constructor
  · rintro ⟨x, hx, xs, hxs, rfl⟩
    exact ⟨x, xs, rfl, hx, hxs⟩
  · rintro ⟨x, xs, rfl, hx, hxs⟩
    exact ⟨x, hx, xs, hxs, rfl⟩

theorem parseEach_eq_some_iff {α : Type} {f : List Char → Option α} {g : α → List Char}
    {V : α → Prop} (hf : ∀ p x, f p = some x ↔ V x ∧ p = g x) {ps : List (List Char)}
    {ys : List α} : parseEach f ps = some ys ↔ (∀ x ∈ ys, V x) ∧ ps = ys.map g := by
  induction ps generalizing ys with
  | nil => cases ys <;> simp [parseEach]
  | cons p ps ih =>
    rw [parseEach_cons_eq_some]
    cases ys with
    | nil => simp
    | cons y ys =>
      simp only [List.cons.injEq, List.forall_mem_cons, List.map_cons, hf, ih]
      constructor
      · rintro ⟨x, xs, ⟨rfl, rfl⟩, ⟨hy, hp⟩, hys, hps⟩
        exact ⟨⟨hy, hys⟩, hp, hps⟩
      · rintro ⟨⟨hy, hys⟩, hp, hps⟩
        exact ⟨y, ys, ⟨rfl, rfl⟩, ⟨hy, hp⟩, hys, hps⟩

/-- Parsing a list of parts joined by dots. -/
theorem parseDotted_iff {α : Type} {f : List Char → Option α} {g : α → List Char}
    {V : α → Prop} (hf : ∀ p x, f p = some x ↔ V x ∧ p = g x)
    (hdot : ∀ x, V x → '.' ∉ g x) {p : List Char} {xs : List α} :
    parseEach f (p.splitOn '.') = some xs ↔
      xs ≠ [] ∧ (∀ x ∈ xs, V x) ∧ p = ['.'].intercalate (xs.map g) := by
  rw [parseEach_eq_some_iff hf]
  constructor
  · rintro ⟨hv, he⟩
    refine ⟨?_, hv, ?_⟩
    · rintro rfl
      exact List.splitOn_ne_nil _ _ he
    · rw [← he, List.intercalate_splitOn]
  · rintro ⟨hne, hv, rfl⟩
    refine ⟨hv, ?_⟩
    rw [List.splitOn_intercalate]
    · intro l hl
      simp only [List.mem_map] at hl
      obtain ⟨x, hx, rfl⟩ := hl
      exact hdot x (hv x hx)
    · simpa using hne

/-- Every part has the form `g x` for some `x` meeting `V`, so the list
    of parts does too. -/
theorem exists_map_of_forall {α : Type} {g : α → List Char} {V : α → Prop} :
    ∀ {parts : List (List Char)}, (∀ q ∈ parts, ∃ x, V x ∧ q = g x) →
      ∃ xs : List α, (∀ x ∈ xs, V x) ∧ parts = xs.map g
  | [], _ => ⟨[], by simp, rfl⟩
  | q :: qs, h => by
    obtain ⟨x, hx, rfl⟩ := h q (by simp)
    obtain ⟨xs, hxs, rfl⟩ := exists_map_of_forall (parts := qs) (fun q hq => h q (by simp [hq]))
    refine ⟨x :: xs, ?_, rfl⟩
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact hx
    · exact hxs y hy

theorem not_mem_intercalate {c : Char} {ls : List (List Char)} (hc : c ≠ '.')
    (h : ∀ l ∈ ls, c ∉ l) : c ∉ ['.'].intercalate ls := by
  induction ls with
  | nil => simp
  | cons l ls ih =>
    cases ls with
    | nil => simpa using h
    | cons l' ls =>
      rw [List.intercalate_cons_cons]
      intro hm
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with (hm | hm) | hm
      · exact h l (by simp) hm
      · exact hc hm
      · exact ih (fun l hl => h l (by simp_all)) hm

end SemVer.Proofs
