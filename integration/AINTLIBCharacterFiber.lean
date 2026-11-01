module

public import Mathlib
public import HasseWeil.HasseBound

@[expose] public section

/-!
# Square-root fiber count over a finite field

This is the exact character-theoretic input that converts the
affine point count into the character sum. It reuses Mathlib's
quadraticChar_card_sqrts; no Weil/Hasse estimate is needed.
-/

namespace SparseDeletion.AINTLIBBridge

theorem square_fiber_card_eq_character
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hchar : ringChar F ≠ 2) (z : F) :
    (((Finset.univ : Finset F).filter (fun y => y ^ 2 = z)).card : ℤ) =
      1 + quadraticCharFun F z := by
  classical
  have h := quadraticChar_card_sqrts (F := F) hchar z
  simpa [Set.toFinset_ofPred, quadraticChar_apply, add_comm] using h

end SparseDeletion.AINTLIBBridge

#print axioms SparseDeletion.AINTLIBBridge.square_fiber_card_eq_character
