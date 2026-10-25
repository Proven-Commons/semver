/-
  The grammar: a list of characters is a `<valid semver>` exactly when
  it is how some well formed version is written.
-/

import Proofs.Format

open SemVer

namespace SemVer.Proofs

theorem preReleaseIdent_iff {q : List Char} :
    Spec.PreReleaseIdent q ↔ ∃ i, Spec.ValidIdent i ∧ q = Spec.identChars i := by
  constructor
  · rintro (h | h)
    · refine ⟨.alnum (String.ofList q), ?_, ?_⟩
      · simpa [Spec.ValidIdent, String.toList_ofList] using h
      · simp [Spec.identChars, String.toList_ofList]
    · obtain ⟨n, rfl⟩ := numericIdent_iff.mp h
      exact ⟨.num n, trivial, rfl⟩
  · rintro ⟨i, hi, rfl⟩
    cases i with
    | num n => exact Or.inr (numericIdent_toDigits n)
    | alnum s => exact Or.inl hi

theorem buildIdent_iff_exists {q : List Char} :
    Spec.BuildIdent q ↔ ∃ s : String, Spec.BuildIdent s.toList ∧ q = s.toList := by
  constructor
  · intro h
    exact ⟨String.ofList q, by rwa [String.toList_ofList], by rw [String.toList_ofList]⟩
  · rintro ⟨s, hs, rfl⟩
    exact hs

theorem dotSeparated_iff {α : Type} {P : List Char → Prop} {V : α → Prop} {g : α → List Char}
    (hP : ∀ q, P q ↔ ∃ x, V x ∧ q = g x) {p : List Char} :
    Spec.DotSeparated P p ↔
      ∃ xs : List α, xs ≠ [] ∧ (∀ x ∈ xs, V x) ∧ p = ['.'].intercalate (xs.map g) := by
  constructor
  · rintro ⟨parts, hne, hparts, rfl⟩
    obtain ⟨xs, hxs, rfl⟩ := exists_map_of_forall (fun q hq => (hP q).mp (hparts q hq))
    exact ⟨xs, by simpa using hne, hxs, rfl⟩
  · rintro ⟨xs, hne, hxs, rfl⟩
    refine ⟨xs.map g, by simpa using hne, ?_, rfl⟩
    intro q hq
    simp only [List.mem_map] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    exact (hP _).mpr ⟨x, hxs x hx, rfl⟩

theorem dotSeparated_pre_iff {p : List Char} :
    Spec.DotSeparated Spec.PreReleaseIdent p ↔
      ∃ xs : List Ident, xs ≠ [] ∧ (∀ x ∈ xs, Spec.ValidIdent x) ∧
        p = ['.'].intercalate (xs.map Spec.identChars) :=
  dotSeparated_iff (fun _ => preReleaseIdent_iff)

theorem dotSeparated_build_iff {p : List Char} :
    Spec.DotSeparated Spec.BuildIdent p ↔
      ∃ xs : List String, xs ≠ [] ∧ (∀ x ∈ xs, Spec.BuildIdent x.toList) ∧
        p = ['.'].intercalate (xs.map String.toList) :=
  dotSeparated_iff (fun _ => buildIdent_iff_exists)

theorem validSemVer_iff {cs : List Char} :
    Spec.ValidSemVer cs ↔ ∃ v, Spec.Valid v ∧ cs = Spec.render v := by
  constructor
  · rintro ⟨ma, mi, pa, hma, hmi, hpa, h⟩
    obtain ⟨a, rfl⟩ := numericIdent_iff.mp hma
    obtain ⟨b, rfl⟩ := numericIdent_iff.mp hmi
    obtain ⟨c, rfl⟩ := numericIdent_iff.mp hpa
    rcases h with rfl | ⟨pre, hpre, rfl⟩ | ⟨build, hbuild, rfl⟩ | ⟨pre, build, hpre, hbuild, rfl⟩
    · exact ⟨⟨a, b, c, [], []⟩, ⟨by simp, by simp⟩, by simp [Spec.render, Spec.decimal]⟩
    · obtain ⟨xs, hne, hxs, rfl⟩ := dotSeparated_pre_iff.mp hpre
      exact ⟨⟨a, b, c, xs, []⟩, ⟨hxs, by simp⟩, by simp [Spec.render, Spec.decimal, hne]⟩
    · obtain ⟨ys, hne, hys, rfl⟩ := dotSeparated_build_iff.mp hbuild
      exact ⟨⟨a, b, c, [], ys⟩, ⟨by simp, hys⟩, by simp [Spec.render, Spec.decimal, hne]⟩
    · obtain ⟨xs, hne, hxs, rfl⟩ := dotSeparated_pre_iff.mp hpre
      obtain ⟨ys, hne', hys, rfl⟩ := dotSeparated_build_iff.mp hbuild
      exact ⟨⟨a, b, c, xs, ys⟩, ⟨hxs, hys⟩, by simp [Spec.render, Spec.decimal, hne, hne']⟩
  · rintro ⟨⟨a, b, c, pre, build⟩, ⟨hvp, hvb⟩, rfl⟩
    refine ⟨Spec.decimal a, Spec.decimal b, Spec.decimal c, numericIdent_toDigits a,
      numericIdent_toDigits b, numericIdent_toDigits c, ?_⟩
    by_cases hp : pre = [] <;> by_cases hb : build = []
    · subst hp hb
      exact Or.inl (by simp [Spec.render])
    · subst hp
      exact Or.inr (Or.inr (Or.inl ⟨_, dotSeparated_build_iff.mpr ⟨build, hb, hvb, rfl⟩,
        by simp [Spec.render, hb]⟩))
    · subst hb
      exact Or.inr (Or.inl ⟨_, dotSeparated_pre_iff.mpr ⟨pre, hp, hvp, rfl⟩,
        by simp [Spec.render, hp]⟩)
    · exact Or.inr (Or.inr (Or.inr ⟨_, _, dotSeparated_pre_iff.mpr ⟨pre, hp, hvp, rfl⟩,
        dotSeparated_build_iff.mpr ⟨build, hb, hvb, rfl⟩, by simp [Spec.render, hp, hb]⟩))

end SemVer.Proofs
