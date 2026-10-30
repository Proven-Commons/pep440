/-
  Axiom check for the claims this package makes. Run with:

    lake env lean Pep440/Verify.lean

  Every claim should list only the standard axioms (propext,
  Classical.choice, Quot.sound). A line naming sorryAx would mean
  a proof rests on an admitted gap, and the claim is not proved.
-/

import Pep440.Proofs
import Pep440.Proofs.Examples

open Pep440.Proofs Pep440.Examples

#print axioms parse_print
#print axioms chain_1
#print axioms chain_14
#print axioms eq_alpha_spelling
#print axioms reprint_chain_member
#print axioms local_absent_first
#print axioms local_prefix
#print axioms local_eq_seps
#print axioms invalid_local_empty_segment
