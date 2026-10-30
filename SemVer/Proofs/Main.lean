/-
  The statements of `SemVer/Spec.lean`, under the same names, from the lemmas
  in the other files of `SemVer/Proofs/`. The test vectors are checked by
  evaluation in the kernel.
-/

import SemVer
import SemVer.Spec.Defs
import SemVer.Proofs.Grammar
import SemVer.Proofs.Order

open SemVer
open SemVer.Proofs

/-! ## Printing -/

theorem SemVer.Spec.print_eq (v : Version) : v.print.toList = SemVer.Spec.render v :=
  print_toList v

/-! ## Parsing -/

theorem SemVer.Spec.parse_iff (s : String) (v : Version) :
    parse s = some v ↔ SemVer.Spec.Valid v ∧ s.toList = SemVer.Spec.render v :=
  parseChars_eq_some

theorem SemVer.Spec.parse_isSome_iff (s : String) :
    (parse s).isSome ↔ SemVer.Spec.ValidSemVer s.toList := by
  rw [validSemVer_iff, Option.isSome_iff_exists]
  exact exists_congr fun v => SemVer.Spec.parse_iff s v

theorem SemVer.Spec.parse_valid (s : String) (v : Version) (h : parse s = some v) :
    SemVer.Spec.Valid v :=
  ((SemVer.Spec.parse_iff s v).mp h).1

theorem SemVer.Spec.parse_print (v : Version) (h : SemVer.Spec.Valid v) : parse v.print = some v :=
  (SemVer.Spec.parse_iff _ _).mpr ⟨h, SemVer.Spec.print_eq v⟩

theorem SemVer.Spec.print_parse (s : String) (v : Version) (h : parse s = some v) :
    v.print = s := by
  obtain ⟨-, hs⟩ := (SemVer.Spec.parse_iff s v).mp h
  apply String.toList_injective
  rw [SemVer.Spec.print_eq, hs]

/-! ## Precedence -/

theorem SemVer.Spec.compare_eq (a b : Version) : a.compare b = SemVer.Spec.precedence a b :=
  versionCompare_eq a b

theorem SemVer.Spec.compare_build (a b : Version) (x y : List String) :
    ({ a with build := x } : Version).compare { b with build := y } = a.compare b :=
  rfl

theorem SemVer.Spec.compare_eq_eq_iff (a b : Version) :
    a.compare b = .eq ↔
      a.major = b.major ∧ a.minor = b.minor ∧ a.patch = b.patch ∧ a.pre = b.pre := by
  rw [compare_key, lawful_key.eq_iff]
  simp [key]

theorem SemVer.Spec.compare_swap (a b : Version) : (a.compare b).swap = b.compare a := by
  rw [compare_key, compare_key, lawful_key.swap]

theorem SemVer.Spec.compare_trans (a b c : Version) (hab : a.compare b ≠ .gt)
    (hbc : b.compare c ≠ .gt) : a.compare c ≠ .gt := by
  rw [compare_key] at hab hbc ⊢
  exact lawful_key.le_trans hab hbc

theorem SemVer.Spec.compare_lt_trans (a b c : Version) (hab : a.compare b = .lt)
    (hbc : b.compare c = .lt) : a.compare c = .lt := by
  rw [compare_key] at hab hbc ⊢
  exact lawful_key.lt_trans _ _ _ hab hbc

/-! ## Test vectors -/

/-- The examples of sections 9 and 10, with the parts they are read
    as. -/
theorem SemVer.Spec.semver_examples :
    parse "1.0.0-alpha" = some ⟨1, 0, 0, [.alnum "alpha"], []⟩ ∧
    parse "1.0.0-alpha.1" = some ⟨1, 0, 0, [.alnum "alpha", .num 1], []⟩ ∧
    parse "1.0.0-0.3.7" = some ⟨1, 0, 0, [.num 0, .num 3, .num 7], []⟩ ∧
    parse "1.0.0-x.7.z.92" = some ⟨1, 0, 0, [.alnum "x", .num 7, .alnum "z", .num 92], []⟩ ∧
    parse "1.0.0-x-y-z.--" = some ⟨1, 0, 0, [.alnum "x-y-z", .alnum "--"], []⟩ ∧
    parse "1.0.0-alpha+001" = some ⟨1, 0, 0, [.alnum "alpha"], ["001"]⟩ ∧
    parse "1.0.0+20130313144700" = some ⟨1, 0, 0, [], ["20130313144700"]⟩ ∧
    parse "1.0.0-beta+exp.sha.5114f85" =
      some ⟨1, 0, 0, [.alnum "beta"], ["exp", "sha", "5114f85"]⟩ ∧
    parse "1.0.0+21AF26D3----117B344092BD" = some ⟨1, 0, 0, [], ["21AF26D3----117B344092BD"]⟩ := by
  decide

/-- The examples of section 11, each list in rising order: every
    version in it has lower precedence than every later one. And two
    versions that differ only in build metadata have the same
    precedence (section 10). -/
theorem SemVer.Spec.precedence_examples :
    ["1.0.0", "2.0.0", "2.1.0", "2.1.1"].Pairwise
      (fun s t => SemVer.Spec.compareStrings s t = some .lt) ∧
    ["1.0.0-alpha", "1.0.0"].Pairwise (fun s t => SemVer.Spec.compareStrings s t = some .lt) ∧
    ["1.0.0-alpha", "1.0.0-alpha.1", "1.0.0-alpha.beta", "1.0.0-beta", "1.0.0-beta.2",
      "1.0.0-beta.11", "1.0.0-rc.1", "1.0.0"].Pairwise
      (fun s t => SemVer.Spec.compareStrings s t = some .lt) ∧
    SemVer.Spec.compareStrings "1.0.0-alpha+001" "1.0.0-alpha" = some .eq ∧
    SemVer.Spec.compareStrings "1.0.0+20130313144700" "1.0.0+21AF26D3----117B344092BD" = some .eq := by
  decide

/-- Strings outside the grammar: leading zeros in numbers, missing or
    extra parts, empty identifiers, characters outside ASCII letters,
    digits and hyphens, and anything before or after the version. -/
theorem SemVer.Spec.reject_vectors :
    parse "01.0.0" = none ∧
    parse "1.02.0" = none ∧
    parse "1.0.00" = none ∧
    parse "1.0.0-01" = none ∧
    parse "1.0" = none ∧
    parse "1.0.0.0" = none ∧
    parse "1.0.0-" = none ∧
    parse "1.0.0+" = none ∧
    parse "1.0.0-alpha..1" = none ∧
    parse "1.0.0-alpha." = none ∧
    parse "1.0.0+build..1" = none ∧
    parse "1.0.0+a+b" = none ∧
    parse "1.0.0-alpha_beta" = none ∧
    parse "1.0.0-alpha.é" = none ∧
    parse "1.0.0-١" = none ∧
    parse "１.0.0" = none ∧
    parse "v1.0.0" = none ∧
    parse "=1.0.0" = none ∧
    parse " 1.0.0" = none ∧
    parse "1.0.0 " = none ∧
    parse "1.0.0\n" = none ∧
    parse "-1.0.0" = none ∧
    parse "1.0.0-+" = none ∧
    parse "" = none := by
  decide

/-- Strings inside the grammar that loose parsers often get wrong: a
    pre-release identifier may have leading zeros when it is not all
    digits, a build identifier may have them always, and a hyphen may
    start an identifier. -/
theorem SemVer.Spec.accept_vectors :
    parse "1.0.0-0a" = some ⟨1, 0, 0, [.alnum "0a"], []⟩ ∧
    parse "1.0.0-0" = some ⟨1, 0, 0, [.num 0], []⟩ ∧
    parse "1.0.0+001" = some ⟨1, 0, 0, [], ["001"]⟩ ∧
    parse "1.0.0--" = some ⟨1, 0, 0, [.alnum "-"], []⟩ ∧
    parse "1.0.0-a-+b-" = some ⟨1, 0, 0, [.alnum "a-"], ["b-"]⟩ ∧
    parse "0.0.0" = some ⟨0, 0, 0, [], []⟩ ∧
    parse "18446744073709551616.0.0" = some ⟨18446744073709551616, 0, 0, [], []⟩ := by
  decide
