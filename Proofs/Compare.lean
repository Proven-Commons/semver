/-
  What is proved about precedence: a version compares equal to
  itself, and two versions that agree on the three numbers and
  the prerelease compare equal, whatever their build metadata.
  The second claim is the one the specification makes about build
  metadata: it takes no part in precedence.

  No claim is made here that the comparison is a full order on
  all versions. That would take transitivity and totality proofs,
  which this slice does not attempt.
-/

import Semver

namespace Semver.Proofs

open Semver

theorem cmpNat_self (a : Nat) : cmpNat a a = Ordering.eq := by
  simp [cmpNat]

theorem cmpChar_self (c : Char) : cmpChar c c = Ordering.eq := by
  simp [cmpChar]

theorem cmpChars_self : ∀ (cs : List Char), cmpChars cs cs = Ordering.eq := by
  intro cs
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [cmpChars, cmpChar_self, ih]

theorem cmpPreId_self (id : PreId) : cmpPreId id id = Ordering.eq := by
  cases id with
  | num n => exact cmpNat_self n
  | alpha cs => exact cmpChars_self cs

theorem cmpPreList_self : ∀ (ids : List PreId),
    cmpPreList ids ids = Ordering.eq := by
  intro ids
  induction ids with
  | nil => rfl
  | cons id ids ih => simp [cmpPreList, cmpPreId_self, ih]

theorem cmpPre_self (ids : List PreId) : cmpPre ids ids = Ordering.eq := by
  cases ids with
  | nil => rfl
  | cons id ids => exact cmpPreList_self (id :: ids)

/-- A version compares equal to itself. -/
theorem compare_self (v : Version) : compare v v = Ordering.eq := by
  obtain ⟨M, m, p, pre, build⟩ := v
  simp [compare, cmpNat_self, cmpPre_self]

/-- Two versions that agree on the three numbers and the
    prerelease compare equal. Build metadata is not consulted,
    so it may differ freely. -/
theorem compare_eq_of_fields {v w : Version}
    (hM : v.major = w.major) (hm : v.minor = w.minor)
    (hp : v.patch = w.patch) (hpre : v.pre = w.pre) :
    compare v w = Ordering.eq := by
  obtain ⟨M₁, m₁, p₁, pre₁, b₁⟩ := v
  obtain ⟨M₂, m₂, p₂, pre₂, b₂⟩ := w
  change M₁ = M₂ at hM
  change m₁ = m₂ at hm
  change p₁ = p₂ at hp
  change pre₁ = pre₂ at hpre
  subst hM
  subst hm
  subst hp
  subst hpre
  simp [compare, cmpNat_self, cmpPre_self]

/-- Changing only the build metadata of a version leaves it
    comparing equal to the original. -/
theorem compare_build_irrel (v : Version) (b : List (List Char)) :
    compare v { v with build := b } = Ordering.eq :=
  compare_eq_of_fields rfl rfl rfl rfl

end Semver.Proofs
