/-
  Printing and parsing: `Version.print` writes `SemVer.Spec.render`, and
  `parseChars` accepts a list of characters exactly when it is how a
  well formed version is written.
-/

import SemVer.Proofs.Ident

open SemVer

namespace SemVer.Proofs

/-! ## Printing -/

theorem toList_toString (n : Nat) : (toString n).toList = Nat.toDigits 10 n := by
  rw [Nat.toString_eq_repr, Nat.toList_repr]

theorem identPrint_toList (i : Ident) : i.print.toList = SemVer.Spec.identChars i := by
  cases i <;> simp [Ident.print, SemVer.Spec.identChars, SemVer.Spec.decimal]

theorem print_toList (v : Version) : v.print.toList = SemVer.Spec.render v := by
  simp [Version.print, SemVer.Spec.render, SemVer.Spec.core, String.toList_append, SemVer.Spec.decimal]
  split <;> split <;> simp [List.map_map, Function.comp_def, identPrint_toList]

/-! ## The parts of a rendered version -/

/-- The pre-release identifiers as written, if there are any. -/
def prePart (pre : List Ident) : Option (List Char) :=
  if pre = [] then none else some (['.'].intercalate (pre.map SemVer.Spec.identChars))

/-- The build identifiers as written, if there are any. -/
def buildPart (build : List String) : Option (List Char) :=
  if build = [] then none else some (['.'].intercalate (build.map String.toList))

theorem core_eq (a b c : List Char) : SemVer.Spec.core a b c = ['.'].intercalate [a, b, c] := by
  simp [SemVer.Spec.core, List.intercalate_cons_cons]

theorem render_eq (v : Version) :
    SemVer.Spec.render v =
      (SemVer.Spec.core (SemVer.Spec.decimal v.major) (SemVer.Spec.decimal v.minor) (SemVer.Spec.decimal v.patch) ++
        after '-' (prePart v.pre)) ++ after '+' (buildPart v.build) := by
  simp only [SemVer.Spec.render, prePart, buildPart]
  split <;> split <;> simp [after]

theorem dot_not_mem_decimal (n : Nat) : '.' ∉ SemVer.Spec.decimal n := not_mem_toDigits not_digit_dot n
theorem plus_not_mem_decimal (n : Nat) : '+' ∉ SemVer.Spec.decimal n :=
  not_mem_toDigits not_digit_plus n
theorem hyphen_not_mem_decimal (n : Nat) : '-' ∉ SemVer.Spec.decimal n :=
  not_mem_toDigits not_digit_hyphen n

theorem not_mem_core {c : Char} (hc : c ≠ '.') (a b d : Nat)
    (h : ∀ n, c ∉ SemVer.Spec.decimal n) :
    c ∉ SemVer.Spec.core (SemVer.Spec.decimal a) (SemVer.Spec.decimal b) (SemVer.Spec.decimal d) := by
  simp only [SemVer.Spec.core, List.mem_append, List.mem_singleton, not_or]
  exact ⟨⟨⟨⟨h a, hc⟩, h b⟩, hc⟩, h d⟩

theorem plus_not_mem_after_pre {pre : List Ident} (h : ∀ i ∈ pre, SemVer.Spec.ValidIdent i) :
    '+' ∉ after '-' (prePart pre) := by
  unfold prePart
  split
  · simp [after]
  · simp only [after, List.mem_cons, not_or]
    refine ⟨by decide, not_mem_intercalate (by decide) ?_⟩
    intro l hl
    simp only [List.mem_map] at hl
    obtain ⟨i, hi, rfl⟩ := hl
    exact plus_not_mem_identChars (h i hi)

/-! ## Parsing -/

theorem parsePre_iff {p : List Char} {xs : List Ident} :
    parseEach parsePreIdent (p.splitOn '.') = some xs ↔
      xs ≠ [] ∧ (∀ x ∈ xs, SemVer.Spec.ValidIdent x) ∧ p = ['.'].intercalate (xs.map SemVer.Spec.identChars) :=
  parseDotted_iff (fun _ _ => parsePreIdent_eq_some) (fun _ h => dot_not_mem_identChars h)

theorem parseBuild_iff {p : List Char} {xs : List String} :
    parseEach parseBuildIdent (p.splitOn '.') = some xs ↔
      xs ≠ [] ∧ (∀ x ∈ xs, SemVer.Spec.BuildIdent x.toList) ∧
        p = ['.'].intercalate (xs.map String.toList) :=
  parseDotted_iff (fun _ _ => parseBuildIdent_eq_some) (fun _ h => dot_not_mem_build h)

theorem parsePrePart_iff {r : Option (List Char)} {xs : List Ident} :
    parseDotted parsePreIdent r = some xs ↔ (∀ x ∈ xs, SemVer.Spec.ValidIdent x) ∧ r = prePart xs := by
  cases r with
  | none =>
    simp only [parseDotted, Option.some.injEq, prePart]
    constructor
    · rintro rfl; simp
    · rintro ⟨-, h⟩
      split at h
      · rename_i hx; exact hx.symm
      · cases h
  | some p =>
    simp only [parseDotted, parsePre_iff, prePart]
    constructor
    · rintro ⟨hne, hv, rfl⟩
      exact ⟨hv, by simp [hne]⟩
    · rintro ⟨hv, h⟩
      split at h
      · cases h
      · rename_i hne
        simp only [Option.some.injEq] at h
        exact ⟨hne, hv, h⟩

theorem parseBuildPart_iff {r : Option (List Char)} {xs : List String} :
    parseDotted parseBuildIdent r = some xs ↔ (∀ x ∈ xs, SemVer.Spec.BuildIdent x.toList) ∧ r = buildPart xs := by
  cases r with
  | none =>
    simp only [parseDotted, Option.some.injEq, buildPart]
    constructor
    · rintro rfl; simp
    · rintro ⟨-, h⟩
      split at h
      · rename_i hx; exact hx.symm
      · cases h
  | some p =>
    simp only [parseDotted, parseBuild_iff, buildPart]
    constructor
    · rintro ⟨hne, hv, rfl⟩
      exact ⟨hv, by simp [hne]⟩
    · rintro ⟨hv, h⟩
      split at h
      · cases h
      · rename_i hne
        simp only [Option.some.injEq] at h
        exact ⟨hne, hv, h⟩

/-- `parseChars`, with the steps named. -/
theorem parseChars_eq (cs : List Char) :
    parseChars cs =
      match (breakAt '-' (breakAt '+' cs).1).1.splitOn '.' with
      | [a, b, c] => do
        let major ← parseNumeric a
        let minor ← parseNumeric b
        let patch ← parseNumeric c
        let pre ← parseDotted parsePreIdent (breakAt '-' (breakAt '+' cs).1).2
        let build ← parseDotted parseBuildIdent (breakAt '+' cs).2
        pure { major, minor, patch, pre, build }
      | _ => none := by
  unfold parseChars
  rfl

theorem parseChars_eq_some {cs : List Char} {v : Version} :
    parseChars cs = some v ↔ SemVer.Spec.Valid v ∧ cs = SemVer.Spec.render v := by
  rw [parseChars_eq]
  generalize hb : breakAt '+' cs = rb
  obtain ⟨main, bp⟩ := rb
  generalize hp : breakAt '-' main = rp
  obtain ⟨core, pp⟩ := rp
  obtain ⟨hb1, hb2⟩ := breakAt_spec hb
  obtain ⟨hp1, hp2⟩ := breakAt_spec hp
  simp only
  constructor
  · intro h
    split at h
    · rename_i a b c hs
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
        Option.some.injEq] at h
      obtain ⟨major, hma, minor, hmi, patch, hpa, pre, hpre, build, hbuild, rfl⟩ := h
      rw [parseNumeric_eq_some] at hma hmi hpa
      obtain ⟨hvp, rfl⟩ := parsePrePart_iff.mp hpre
      obtain ⟨hvb, rfl⟩ := parseBuildPart_iff.mp hbuild
      refine ⟨⟨hvp, hvb⟩, ?_⟩
      rw [render_eq, hb2, hp2, core_eq]
      have hcore := List.intercalate_splitOn (xs := core) '.'
      rw [hs] at hcore
      rw [← hcore, hma, hmi, hpa]
      rfl
    · cases h
  · rintro ⟨⟨hvp, hvb⟩, rfl⟩
    rw [render_eq] at hb
    rw [breakAt_append _ (by
      simp only [List.mem_append, not_or]
      exact ⟨not_mem_core (by decide) _ _ _ plus_not_mem_decimal, plus_not_mem_after_pre hvp⟩),
      Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl⟩ := hb
    rw [breakAt_append _ (not_mem_core (by decide) _ _ _ hyphen_not_mem_decimal),
      Prod.mk.injEq] at hp
    obtain ⟨rfl, rfl⟩ := hp
    rw [core_eq, List.splitOn_intercalate]
    · rw [(parsePrePart_iff (xs := v.pre)).mpr ⟨hvp, rfl⟩,
        (parseBuildPart_iff (xs := v.build)).mpr ⟨hvb, rfl⟩]
      simp only [SemVer.Spec.decimal, parseNumeric_toDigits, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def]
    · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨dot_not_mem_decimal _, dot_not_mem_decimal _, dot_not_mem_decimal _⟩
    · simp

end SemVer.Proofs
