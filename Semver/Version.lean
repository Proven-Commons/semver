/-
  The version value type, the well-formedness rules, the printer,
  and the precedence comparison, for Semantic Versioning 2.0.0.

  A version holds three numbers, a list of prerelease identifiers,
  and a list of build metadata identifiers. A prerelease identifier
  is either numeric, held as the number itself, or alphanumeric,
  held as its characters. Build identifiers are held as text,
  because build metadata is never compared and leading zeros in it
  carry meaning as text, not as numbers.
-/

namespace Semver

/-- A prerelease identifier: a number, or a text with at least one
    character that is not a digit. -/
inductive PreId where
  | num (n : Nat)
  | alpha (cs : List Char)
  deriving DecidableEq, Repr

/-- A semantic version. Build identifiers are lists of characters. -/
structure Version where
  major : Nat
  minor : Nat
  patch : Nat
  pre : List PreId
  build : List (List Char)
  deriving DecidableEq, Repr

/-- A digit character, as a proposition. -/
def IsDigit (c : Char) : Prop := 48 ≤ c.toNat ∧ c.toNat ≤ 57

/-- A digit character, as a test. -/
def isDigit (c : Char) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57

/-- The characters an identifier may hold: digits, ASCII letters,
    and the hyphen. -/
def IsIdChar (c : Char) : Prop :=
  IsDigit c ∨ (65 ≤ c.toNat ∧ c.toNat ≤ 90) ∨
    (97 ≤ c.toNat ∧ c.toNat ≤ 122) ∨ c = '-'

/-- The identifier character test. -/
def isIdChar (c : Char) : Bool :=
  isDigit c || (65 ≤ c.toNat && c.toNat ≤ 90) ||
    (97 ≤ c.toNat && c.toNat ≤ 122) || c = '-'

theorem isDigit_iff {c : Char} : isDigit c = true ↔ IsDigit c := by
  simp [isDigit, IsDigit, Bool.and_eq_true]

theorem isIdChar_iff {c : Char} : isIdChar c = true ↔ IsIdChar c := by
  unfold isIdChar IsIdChar
  simp only [isDigit_iff, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro (((h | h) | h) | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
  · rintro (h | (h | (h | h)))
    · exact Or.inl (Or.inl (Or.inl h))
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-- An alphanumeric prerelease identifier is well formed when it is
    not empty, holds only identifier characters, and holds at least
    one character that is not a digit. The last rule is what makes
    the type honest: a text of digits alone is a number here, never
    an alphanumeric identifier, so a printed identifier reads back
    as the same kind. -/
def WFAlpha (cs : List Char) : Prop :=
  cs ≠ [] ∧ (∀ c ∈ cs, IsIdChar c) ∧ (∃ c ∈ cs, ¬ IsDigit c)

/-- A build identifier is well formed when it is not empty and
    holds only identifier characters. Leading zeros are fine. -/
def WFBuildId (cs : List Char) : Prop :=
  cs ≠ [] ∧ ∀ c ∈ cs, IsIdChar c

/-- Well-formedness of one prerelease identifier. A numeric
    identifier needs nothing: a natural number prints with no
    leading zeros by construction. -/
def WFPreId : PreId → Prop
  | .num _ => True
  | .alpha cs => WFAlpha cs

/-- A version is well formed when each prerelease identifier and
    each build identifier is well formed. The three numbers need
    nothing. -/
def WF (v : Version) : Prop :=
  (∀ id ∈ v.pre, WFPreId id) ∧ ∀ b ∈ v.build, WFBuildId b

/-! ## Printing -/

/-- The character for a digit value below 10. Any other value
    gives '0'; the lemmas about this function all ask for a value
    below 10. -/
def digitChar : Nat → Char
  | 0 => '0'
  | 1 => '1'
  | 2 => '2'
  | 3 => '3'
  | 4 => '4'
  | 5 => '5'
  | 6 => '6'
  | 7 => '7'
  | 8 => '8'
  | 9 => '9'
  | _ => '0'

/-- The digits of a number, least significant first, built with
    fuel so the definition is structural. The top level call gives
    one more fuel than the number, which is always enough: each
    step divides by 10. -/
def digitsRevAux : Nat → Nat → List Nat
  | 0, _ => []
  | _ + 1, 0 => []
  | fuel + 1, n + 1 => (n + 1) % 10 :: digitsRevAux fuel ((n + 1) / 10)

/-- The digits of a number, least significant first. The digits of
    0 are the empty list; `printNat` handles 0 on its own. -/
def digitsRev (n : Nat) : List Nat := digitsRevAux (n + 1) n

/-- The printed form of a natural number: decimal digits, no
    leading zeros. -/
def printNat (n : Nat) : List Char :=
  if n = 0 then ['0'] else (digitsRev n).reverse.map digitChar

/-- One prerelease identifier, printed. -/
def printPreId : PreId → List Char
  | .num n => printNat n
  | .alpha cs => cs

/-- A list of printed parts joined by dots. -/
def joinDots : List (List Char) → List Char
  | [] => []
  | [p] => p
  | p :: ps => p ++ '.' :: joinDots ps

/-- The canonical text of a version: the three numbers split by
    dots, then the prerelease part behind a hyphen when there is
    one, then the build part behind a plus sign when there is
    one. -/
def print (v : Version) : List Char :=
  printNat v.major ++ ('.' :: (printNat v.minor ++ ('.' :: (printNat v.patch ++
    (match v.pre, v.build with
     | [], [] => []
     | ids, [] => '-' :: joinDots (ids.map printPreId)
     | [], bs => '+' :: joinDots bs
     | ids, bs => ('-' :: joinDots (ids.map printPreId)) ++
        ('+' :: joinDots bs))))))

/-! ## Precedence, section 11 of the specification -/

/-- Three-way comparison of two numbers. -/
def cmpNat (a b : Nat) : Ordering :=
  if a < b then .lt else if b < a then .gt else .eq

/-- Three-way comparison of two characters, by code point. For
    identifier characters this is ASCII order. -/
def cmpChar (a b : Char) : Ordering :=
  if a.toNat < b.toNat then .lt else if b.toNat < a.toNat then .gt else .eq

/-- Lexicographic comparison of two character lists. When one is
    a prefix of the other, the shorter one is lower. -/
def cmpChars : List Char → List Char → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match cmpChar a b with
    | .eq => cmpChars as bs
    | o => o

/-- Two prerelease identifiers: numbers compare by value, texts
    compare in ASCII order, and a number is lower than a text. -/
def cmpPreId : PreId → PreId → Ordering
  | .num a, .num b => cmpNat a b
  | .num _, .alpha _ => .lt
  | .alpha _, .num _ => .gt
  | .alpha a, .alpha b => cmpChars a b

/-- Two prerelease lists, identifier by identifier. When every
    shared identifier is equal, the shorter list is lower. -/
def cmpPreList : List PreId → List PreId → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs =>
    match cmpPreId a b with
    | .eq => cmpPreList as bs
    | o => o

/-- The prerelease step of section 11: a version with a
    prerelease is lower than the same version without one. -/
def cmpPre : List PreId → List PreId → Ordering
  | [], [] => .eq
  | [], _ :: _ => .gt
  | _ :: _, [] => .lt
  | ids₁, ids₂ => cmpPreList ids₁ ids₂

/-- Precedence, as section 11 of the specification states it:
    major, then minor, then patch, then the prerelease rules.
    Build metadata takes no part. -/
def compare (v w : Version) : Ordering :=
  match cmpNat v.major w.major with
  | .eq =>
    match cmpNat v.minor w.minor with
    | .eq =>
      match cmpNat v.patch w.patch with
      | .eq => cmpPre v.pre w.pre
      | o => o
    | o => o
  | o => o

end Semver
