/-
  What a version is: the values the parser produces and the printer
  takes. Part of the approved specification, with `SemVer/Spec.lean` and
  `SemVer/Spec/Defs.lean`, since every statement is about these types.

  A value holds each part of a Semantic Versioning 2.0.0 string as
  written. Which values are valid is `SemVer.Spec.Valid`, in `SemVer/Spec/Defs.lean`.
-/

namespace SemVer

/-- A pre-release identifier, section 9 of SemVer 2.0.0. -/
inductive Ident where
  /-- A numeric identifier: digits only, read as a number. -/
  | num (n : Nat)
  /-- An alphanumeric identifier: ASCII letters, digits and hyphens,
      with at least one letter or hyphen. -/
  | alnum (s : String)
  deriving DecidableEq, Repr

/-- A version: `major.minor.patch`, then the pre-release identifiers
    after `-`, then the build identifiers after `+`. Either list is
    empty when its part is absent. -/
structure Version where
  major : Nat
  minor : Nat
  patch : Nat
  pre : List Ident
  build : List String
  deriving DecidableEq, Repr

end SemVer
