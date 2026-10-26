/-
  Reading and writing Semantic Versioning 2.0.0 strings, and the
  precedence of section 11.
-/

import SemVer.Types

namespace SemVer

/-! ## Printing -/

/-- A pre-release identifier as written: a number in decimal, or the
    identifier itself. -/
def Ident.print : Ident → String
  | .num n => toString n
  | .alnum s => s

/-- The version as SemVer 2.0.0 writes it: the three numbers in decimal,
    then `-` and the pre-release identifiers, then `+` and the build
    identifiers, each list joined by `.` and left out when empty. -/
def Version.print (v : Version) : String :=
  toString v.major ++ "." ++ toString v.minor ++ "." ++ toString v.patch ++
    (if v.pre.isEmpty then "" else "-" ++ ".".intercalate (v.pre.map Ident.print)) ++
    (if v.build.isEmpty then "" else "+" ++ ".".intercalate v.build)

/-! ## Parsing -/

/-- `<digit>`: `0` to `9`. -/
def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- `<identifier character>`: an ASCII digit, letter or hyphen. -/
def isIdentChar (c : Char) : Bool :=
  isDigit c || ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') || c == '-'

/-- The characters before the first `sep`, and the characters after it
    when there is one. -/
def breakAt (sep : Char) : List Char → List Char × Option (List Char)
  | [] => ([], none)
  | c :: cs =>
    if c = sep then ([], some cs)
    else
      let r := breakAt sep cs
      (c :: r.1, r.2)

/-- `<numeric identifier>`: `0`, or digits with no leading zero. -/
def parseNumeric : List Char → Option Nat
  | [] => none
  | c :: cs =>
    if (c :: cs).all isDigit && (c != '0' || cs.isEmpty) then
      some (Nat.ofDigitChars 10 (c :: cs) 0)
    else none

/-- `<pre-release identifier>`: a numeric identifier, or an alphanumeric
    one, which has a character other than a digit. -/
def parsePreIdent (cs : List Char) : Option Ident :=
  if cs.all isDigit then (parseNumeric cs).map .num
  else if cs.all isIdentChar then some (.alnum (String.ofList cs))
  else none

/-- `<build identifier>`: one or more identifier characters. Leading
    zeros are allowed here. -/
def parseBuildIdent (cs : List Char) : Option String :=
  if !cs.isEmpty && cs.all isIdentChar then some (String.ofList cs) else none

/-- Applies `f` to each part, and fails if it fails on any. -/
def parseEach (f : List Char → Option α) : List (List Char) → Option (List α)
  | [] => some []
  | p :: ps => do
    let a ← f p
    let as ← parseEach f ps
    pure (a :: as)

/-- The identifiers after a separator, joined by `.`: none when the
    separator is absent, and at least one when it is present. -/
def parseDotted (f : List Char → Option α) : Option (List Char) → Option (List α)
  | none => some []
  | some p => parseEach f (p.splitOn '.')

/-- `<valid semver>`, as a list of characters. -/
def parseChars (cs : List Char) : Option Version :=
  -- `+` appears in no identifier, so the first one starts the build
  -- part; `-` appears in no number, so the first one before it starts
  -- the pre-release part.
  let (main, buildPart) := breakAt '+' cs
  let (core, prePart) := breakAt '-' main
  match core.splitOn '.' with
  | [a, b, c] => do
    let major ← parseNumeric a
    let minor ← parseNumeric b
    let patch ← parseNumeric c
    let pre ← parseDotted parsePreIdent prePart
    let build ← parseDotted parseBuildIdent buildPart
    pure { major, minor, patch, pre, build }
  | _ => none

/-- Reads a Semantic Versioning 2.0.0 string. The whole string must be
    the version: no `v` before it and no space around it. -/
def parse (s : String) : Option Version := parseChars s.toList

/-! ## Precedence -/

/-- Two lists of characters in ASCII order: by the first character that
    differs, and a list before any longer list it starts. -/
def compareAscii : List Char → List Char → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (compare a.toNat b.toNat).then (compareAscii as bs)

/-- Two pre-release identifiers: numbers by value, other identifiers in
    ASCII order, and a number before any other identifier. -/
def Ident.compare : Ident → Ident → Ordering
  | .num a, .num b => Ord.compare a b
  | .num _, .alnum _ => .lt
  | .alnum _, .num _ => .gt
  | .alnum a, .alnum b => compareAscii a.toList b.toList

/-- Two lists of pre-release identifiers: by the first identifier that
    differs, and a list before any longer list it starts. -/
def compareIdents : List Ident → List Ident → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => (a.compare b).then (compareIdents as bs)

/-- The pre-release parts of two versions with the same numbers: a
    version with no pre-release part comes after one with a pre-release
    part. -/
def comparePre : List Ident → List Ident → Ordering
  | [], [] => .eq
  | [], _ :: _ => .gt
  | _ :: _, [] => .lt
  | as, bs => compareIdents as bs

/-- The precedence of section 11: major, minor and patch by value, then
    the pre-release part. Build identifiers play no part. -/
def Version.compare (a b : Version) : Ordering :=
  (Ord.compare a.major b.major).then <|
    (Ord.compare a.minor b.minor).then <|
      (Ord.compare a.patch b.patch).then (comparePre a.pre b.pre)

end SemVer
