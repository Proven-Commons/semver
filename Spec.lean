/-
  The specification as Lean statements: the challenge file.

  A reviewer who did not write this file approves it, and `bar.toml`
  records the hash it had then. The proofs live in `Proofs.lean`, under
  the same names; `lake comparator` checks that each one proves exactly
  the statement written here. The `sorry`s below are expected in this
  file only.

  The definitions the statements use, written from Semantic Versioning
  2.0.0, are in `Spec/Defs.lean`, and the types in `SemVer/Types.lean`.
  Both are part of the specification too.
-/

import SemVer
import Spec.Defs

open SemVer

/-! ## Printing -/

/-- `print` writes a version as `Spec.render` sets out: the numbers in
    decimal, then the pre-release and build parts, each left out when
    empty. -/
theorem Spec.print_eq (v : Version) : v.print.toList = Spec.render v := sorry

/-! ## Parsing -/

/-- `parse` returns `v` exactly when `v` is well formed and the string
    is how `v` is written. So it returns the parts as written, accepts
    no other spelling of them, and rejects every string that is not how
    some well formed version is written. -/
theorem Spec.parse_iff (s : String) (v : Version) :
    parse s = some v ↔ Spec.Valid v ∧ s.toList = Spec.render v := sorry

/-- `parse` accepts exactly the strings of the grammar on semver.org. -/
theorem Spec.parse_isSome_iff (s : String) :
    (parse s).isSome ↔ Spec.ValidSemVer s.toList := sorry

/-- What `parse` returns is well formed. -/
theorem Spec.parse_valid (s : String) (v : Version) (h : parse s = some v) :
    Spec.Valid v := sorry

/-- Round trip: printing a well formed version and parsing the result
    gives it back. -/
theorem Spec.parse_print (v : Version) (h : Spec.Valid v) : parse v.print = some v := sorry

/-- Round trip: parsing a string and printing the result gives the
    string back. -/
theorem Spec.print_parse (s : String) (v : Version) (h : parse s = some v) :
    v.print = s := sorry

/-! ## Precedence -/

/-- `compare` gives the precedence of section 11. -/
theorem Spec.compare_eq (a b : Version) : a.compare b = Spec.precedence a b := sorry

/-- Build identifiers play no part in precedence (11.1): changing them
    on either side changes nothing. -/
theorem Spec.compare_build (a b : Version) (x y : List String) :
    ({ a with build := x } : Version).compare { b with build := y } = a.compare b := sorry

/-- Two versions have the same precedence exactly when they differ in
    build identifiers at most. -/
theorem Spec.compare_eq_eq_iff (a b : Version) :
    a.compare b = .eq ↔
      a.major = b.major ∧ a.minor = b.minor ∧ a.patch = b.patch ∧ a.pre = b.pre := sorry

/-- Swapping the two sides swaps the answer. -/
theorem Spec.compare_swap (a b : Version) : (a.compare b).swap = b.compare a := sorry

/-- Precedence is transitive, so sorting by it is consistent. -/
theorem Spec.compare_trans (a b c : Version) (hab : a.compare b ≠ .gt)
    (hbc : b.compare c ≠ .gt) : a.compare c ≠ .gt := sorry

/-- Strict precedence is transitive too. -/
theorem Spec.compare_lt_trans (a b c : Version) (hab : a.compare b = .lt)
    (hbc : b.compare c = .lt) : a.compare c = .lt := sorry

/-! ## Test vectors -/

/-- The examples of sections 9 and 10, with the parts they are read
    as. -/
theorem Spec.semver_examples :
    parse "1.0.0-alpha" = some ⟨1, 0, 0, [.alnum "alpha"], []⟩ ∧
    parse "1.0.0-alpha.1" = some ⟨1, 0, 0, [.alnum "alpha", .num 1], []⟩ ∧
    parse "1.0.0-0.3.7" = some ⟨1, 0, 0, [.num 0, .num 3, .num 7], []⟩ ∧
    parse "1.0.0-x.7.z.92" = some ⟨1, 0, 0, [.alnum "x", .num 7, .alnum "z", .num 92], []⟩ ∧
    parse "1.0.0-x-y-z.--" = some ⟨1, 0, 0, [.alnum "x-y-z", .alnum "--"], []⟩ ∧
    parse "1.0.0-alpha+001" = some ⟨1, 0, 0, [.alnum "alpha"], ["001"]⟩ ∧
    parse "1.0.0+20130313144700" = some ⟨1, 0, 0, [], ["20130313144700"]⟩ ∧
    parse "1.0.0-beta+exp.sha.5114f85" =
      some ⟨1, 0, 0, [.alnum "beta"], ["exp", "sha", "5114f85"]⟩ ∧
    parse "1.0.0+21AF26D3----117B344092BD" = some ⟨1, 0, 0, [], ["21AF26D3----117B344092BD"]⟩ :=
  sorry

/-- The examples of section 11, each list in rising order: every
    version in it has lower precedence than every later one. And two
    versions that differ only in build metadata have the same
    precedence (section 10). -/
theorem Spec.precedence_examples :
    ["1.0.0", "2.0.0", "2.1.0", "2.1.1"].Pairwise
      (fun s t => Spec.compareStrings s t = some .lt) ∧
    ["1.0.0-alpha", "1.0.0"].Pairwise (fun s t => Spec.compareStrings s t = some .lt) ∧
    ["1.0.0-alpha", "1.0.0-alpha.1", "1.0.0-alpha.beta", "1.0.0-beta", "1.0.0-beta.2",
      "1.0.0-beta.11", "1.0.0-rc.1", "1.0.0"].Pairwise
      (fun s t => Spec.compareStrings s t = some .lt) ∧
    Spec.compareStrings "1.0.0-alpha+001" "1.0.0-alpha" = some .eq ∧
    Spec.compareStrings "1.0.0+20130313144700" "1.0.0+21AF26D3----117B344092BD" = some .eq :=
  sorry

/-- Strings outside the grammar: leading zeros in numbers, missing or
    extra parts, empty identifiers, characters outside ASCII letters,
    digits and hyphens, and anything before or after the version. -/
theorem Spec.reject_vectors :
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
    parse "" = none :=
  sorry

/-- Strings inside the grammar that loose parsers often get wrong: a
    pre-release identifier may have leading zeros when it is not all
    digits, a build identifier may have them always, and a hyphen may
    start an identifier. -/
theorem Spec.accept_vectors :
    parse "1.0.0-0a" = some ⟨1, 0, 0, [.alnum "0a"], []⟩ ∧
    parse "1.0.0-0" = some ⟨1, 0, 0, [.num 0], []⟩ ∧
    parse "1.0.0+001" = some ⟨1, 0, 0, [], ["001"]⟩ ∧
    parse "1.0.0--" = some ⟨1, 0, 0, [.alnum "-"], []⟩ ∧
    parse "1.0.0-a-+b-" = some ⟨1, 0, 0, [.alnum "a-"], ["b-"]⟩ ∧
    parse "0.0.0" = some ⟨0, 0, 0, [], []⟩ ∧
    parse "18446744073709551616.0.0" = some ⟨18446744073709551616, 0, 0, [], []⟩ :=
  sorry
