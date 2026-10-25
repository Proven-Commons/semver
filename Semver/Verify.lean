/-
  Axiom check for the claims this package makes. Run with:

    lake env lean Semver/Verify.lean

  Every claim should list only the standard axioms (propext,
  Classical.choice, Quot.sound). A line naming sorryAx would mean
  a proof rests on an admitted gap, and the claim is not proved.
-/

import Proofs
import Proofs.Examples

open Semver.Proofs Semver.Examples

#print axioms parse_print
#print axioms compare_self
#print axioms compare_eq_of_fields
#print axioms compare_build_irrel
#print axioms chain_1
#print axioms chain_7
#print axioms valid_xyz
#print axioms invalid_empty_pre_and_build
