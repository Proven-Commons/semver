/-
  The definitions the specification uses, written from Semantic
  Versioning 2.0.0 (https://semver.org/spec/v2.0.0.html) independently
  of the code in `SemVer/`. Part of the approved specification, with
  `Spec.lean` and `SemVer/Types.lean`.

  Both the challenge file and the proofs import this file, so each
  statement means the same thing on both sides. The `example`s check
  the definitions against the specification's own examples. A mistake
  in either fails the build.
-/

import SemVer

open SemVer

/-! ## Characters

From the Backus–Naur form grammar on semver.org:

```
<digit> ::= "0" | <positive digit>
<positive digit> ::= "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
<letter> ::= "A" | "B" | ... | "Z" | "a" | "b" | ... | "z"
<non-digit> ::= <letter> | "-"
<identifier character> ::= <digit> | <non-digit>
```
-/

/-- `<digit>`. -/
abbrev Spec.Digit (c : Char) : Prop := '0' ≤ c ∧ c ≤ '9'

/-- `<positive digit>`. -/
abbrev Spec.PositiveDigit (c : Char) : Prop := '1' ≤ c ∧ c ≤ '9'

/-- `<letter>`: ASCII letters only. -/
abbrev Spec.Letter (c : Char) : Prop := ('A' ≤ c ∧ c ≤ 'Z') ∨ ('a' ≤ c ∧ c ≤ 'z')

/-- `<non-digit>`. -/
abbrev Spec.NonDigit (c : Char) : Prop := Spec.Letter c ∨ c = '-'

/-- `<identifier character>`. -/
abbrev Spec.IdentChar (c : Char) : Prop := Spec.Digit c ∨ Spec.NonDigit c

example : "0123456789".toList.all (fun c => decide (Spec.Digit c)) := by decide
example : "123456789".toList.all (fun c => decide (Spec.PositiveDigit c)) := by decide
example : ¬ Spec.PositiveDigit '0' := by decide
example : ("ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz-".toList.all fun c =>
    decide (Spec.NonDigit c)) := by decide
-- The neighbours of each range, and characters people mistake for
-- them, are not identifier characters.
example : ("/:@[`{.+_ \n٣０éα".toList.all fun c => !decide (Spec.IdentChar c)) := by decide

/-! ## The grammar

```
<valid semver> ::= <version core>
                 | <version core> "-" <pre-release>
                 | <version core> "+" <build>
                 | <version core> "-" <pre-release> "+" <build>
<version core> ::= <major> "." <minor> "." <patch>
<major> ::= <numeric identifier>
<minor> ::= <numeric identifier>
<patch> ::= <numeric identifier>
<pre-release> ::= <dot-separated pre-release identifiers>
<dot-separated pre-release identifiers> ::= <pre-release identifier>
    | <pre-release identifier> "." <dot-separated pre-release identifiers>
<build> ::= <dot-separated build identifiers>
<dot-separated build identifiers> ::= <build identifier>
    | <build identifier> "." <dot-separated build identifiers>
<pre-release identifier> ::= <alphanumeric identifier> | <numeric identifier>
<build identifier> ::= <alphanumeric identifier> | <digits>
<alphanumeric identifier> ::= <non-digit>
    | <non-digit> <identifier characters>
    | <identifier characters> <non-digit>
    | <identifier characters> <non-digit> <identifier characters>
<numeric identifier> ::= "0" | <positive digit> | <positive digit> <digits>
<identifier characters> ::= <identifier character>
    | <identifier character> <identifier characters>
<digits> ::= <digit> | <digit> <digits>
```

Each rule below is one of these, over lists of characters.
-/

/-- `<digits>`: one or more digits. -/
def Spec.Digits (cs : List Char) : Prop := cs ≠ [] ∧ ∀ c ∈ cs, Spec.Digit c

/-- `<numeric identifier>`: `0`, or a positive digit followed by any
    number of digits. So no leading zero. -/
def Spec.NumericIdent (cs : List Char) : Prop :=
  cs = ['0'] ∨ ∃ c rest, cs = c :: rest ∧ Spec.PositiveDigit c ∧ ∀ d ∈ rest, Spec.Digit d

/-- `<alphanumeric identifier>`: the four forms of the rule together are
    a non-digit with any identifier characters, possibly none, before
    and after it. -/
def Spec.AlnumIdent (cs : List Char) : Prop :=
  ∃ xs c ys, cs = xs ++ c :: ys ∧ Spec.NonDigit c ∧
    (∀ d ∈ xs, Spec.IdentChar d) ∧ ∀ d ∈ ys, Spec.IdentChar d

/-- `<pre-release identifier>`. -/
def Spec.PreReleaseIdent (cs : List Char) : Prop :=
  Spec.AlnumIdent cs ∨ Spec.NumericIdent cs

/-- `<build identifier>`. -/
def Spec.BuildIdent (cs : List Char) : Prop :=
  Spec.AlnumIdent cs ∨ Spec.Digits cs

/-- `<dot-separated ... identifiers>`: one or more parts, each of them
    meeting `P`, with `.` between each two. -/
def Spec.DotSeparated (P : List Char → Prop) (cs : List Char) : Prop :=
  ∃ parts, parts ≠ [] ∧ (∀ p ∈ parts, P p) ∧ cs = ['.'].intercalate parts

/-- `<version core>`, from its three parts. -/
def Spec.core (major minor patch : List Char) : List Char :=
  major ++ ['.'] ++ minor ++ ['.'] ++ patch

/-- `<valid semver>`: the four forms of the rule. -/
def Spec.ValidSemVer (cs : List Char) : Prop :=
  ∃ major minor patch,
    Spec.NumericIdent major ∧ Spec.NumericIdent minor ∧ Spec.NumericIdent patch ∧
    (cs = Spec.core major minor patch ∨
      (∃ pre, Spec.DotSeparated Spec.PreReleaseIdent pre ∧
        cs = Spec.core major minor patch ++ ['-'] ++ pre) ∨
      (∃ build, Spec.DotSeparated Spec.BuildIdent build ∧
        cs = Spec.core major minor patch ++ ['+'] ++ build) ∨
      (∃ pre build, Spec.DotSeparated Spec.PreReleaseIdent pre ∧
        Spec.DotSeparated Spec.BuildIdent build ∧
        cs = Spec.core major minor patch ++ ['-'] ++ pre ++ ['+'] ++ build))

/-! ## Values -/

/-- A natural number in decimal, as Lean's `Nat.repr` writes it: no
    leading zero, and `0` for zero. -/
def Spec.decimal (n : Nat) : List Char := Nat.toDigits 10 n

example : Spec.decimal 0 = ['0'] := by decide
example : Spec.decimal 7 = ['7'] := by decide
example : Spec.decimal 1985 = "1985".toList := by decide

/-- A pre-release identifier as written. -/
def Spec.identChars : Ident → List Char
  | .num n => Spec.decimal n
  | .alnum s => s.toList

/-- The string a version stands for: the three numbers, the pre-release
    identifiers after `-` and the build identifiers after `+`, each list
    joined by `.` and left out with its sign when it is empty. -/
def Spec.render (v : Version) : List Char :=
  Spec.core (Spec.decimal v.major) (Spec.decimal v.minor) (Spec.decimal v.patch) ++
    (if v.pre = [] then [] else ['-'] ++ ['.'].intercalate (v.pre.map Spec.identChars)) ++
    (if v.build = [] then [] else ['+'] ++ ['.'].intercalate (v.build.map String.toList))

example : Spec.render ⟨1, 0, 0, [.alnum "alpha", .num 1], []⟩ = "1.0.0-alpha.1".toList := by
  decide
example : Spec.render ⟨1, 0, 0, [.alnum "beta"], ["exp", "sha", "5114f85"]⟩ =
    "1.0.0-beta+exp.sha.5114f85".toList := by decide
example : Spec.render ⟨1, 0, 0, [], ["20130313144700"]⟩ = "1.0.0+20130313144700".toList := by
  decide

/-- A pre-release identifier is well formed when, as a number, it is any
    natural number, and otherwise when it is an alphanumeric identifier.
    An `alnum` of digits only is not well formed: those digits are a
    numeric identifier. -/
def Spec.ValidIdent : Ident → Prop
  | .num _ => True
  | .alnum s => Spec.AlnumIdent s.toList

/-- A version is well formed when each of its identifiers is. The three
    numbers may be any natural numbers: SemVer sets no upper limit. -/
def Spec.Valid (v : Version) : Prop :=
  (∀ i ∈ v.pre, Spec.ValidIdent i) ∧ ∀ b ∈ v.build, Spec.BuildIdent b.toList

/-! ## Precedence: section 11

```
1. Precedence MUST be calculated by separating the version into major,
   minor, patch and pre-release identifiers in that order (Build
   metadata does not figure into precedence).
2. Precedence is determined by the first difference when comparing
   each of these identifiers from left to right as follows: Major,
   minor, and patch versions are always compared numerically.
3. When major, minor, and patch are equal, a pre-release version has
   lower precedence than a normal version.
4. Precedence for two pre-release versions with the same major, minor,
   and patch version MUST be determined by comparing each dot separated
   identifier from left to right until a difference is found as
   follows:
   1. Identifiers consisting of only digits are compared numerically.
   2. Identifiers with letters or hyphens are compared lexically in
      ASCII sort order.
   3. Numeric identifiers always have lower precedence than
      non-numeric identifiers.
   4. A larger set of pre-release fields has a higher precedence than
      a smaller set, if all of the preceding identifiers are equal.
```
-/

/-- Two numbers, compared numerically (11.2 and 11.4.1). -/
def Spec.numOrder (a b : Nat) : Ordering :=
  if a < b then .lt else if b < a then .gt else .eq

/-- ASCII sort order (11.4.2): by the code of the first character that
    differs; when one string runs out first, it comes first. -/
def Spec.asciiOrder : List Char → List Char → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    if a.toNat < b.toNat then .lt else if b.toNat < a.toNat then .gt else Spec.asciiOrder as bs

example : Spec.asciiOrder "alpha".toList "beta".toList = .lt := by decide
example : Spec.asciiOrder "Z".toList "a".toList = .lt := by decide
example : Spec.asciiOrder "-".toList "0a".toList = .lt := by decide
example : Spec.asciiOrder "rc".toList "rc1".toList = .lt := by decide

/-- Two pre-release identifiers: 11.4.1 to 11.4.3. -/
def Spec.identOrder : Ident → Ident → Ordering
  | .num a, .num b => Spec.numOrder a b
  | .alnum a, .alnum b => Spec.asciiOrder a.toList b.toList
  | .num _, .alnum _ => .lt
  | .alnum _, .num _ => .gt

/-- Two lists of pre-release identifiers, from left to right until a
    difference is found (11.4); when one list runs out first, all of its
    identifiers being equal to the other's, it comes first (11.4.4). -/
def Spec.preOrder : List Ident → List Ident → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match Spec.identOrder a b with
    | .eq => Spec.preOrder as bs
    | o => o

/-- The precedence of `a` against `b`: `.lt` when `a` has lower
    precedence. Major, minor and patch first (11.2), then a version
    without a pre-release part above one with it (11.3), then the
    pre-release identifiers (11.4). Build identifiers are not read
    (11.1). -/
def Spec.precedence (a b : Version) : Ordering :=
  if a.major ≠ b.major then Spec.numOrder a.major b.major
  else if a.minor ≠ b.minor then Spec.numOrder a.minor b.minor
  else if a.patch ≠ b.patch then Spec.numOrder a.patch b.patch
  else if a.pre = [] ∧ b.pre = [] then .eq
  else if a.pre = [] then .gt
  else if b.pre = [] then .lt
  else Spec.preOrder a.pre b.pre

/-! ## Helpers for the test vectors -/

/-- The precedence of two strings, when both parse. -/
def Spec.compareStrings (s t : String) : Option Ordering := do
  let a ← parse s
  let b ← parse t
  pure (a.compare b)
