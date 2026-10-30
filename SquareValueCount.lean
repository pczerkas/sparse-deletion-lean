module -- shake: keep-all

public import ImageBoundBridge

@[expose] public section

namespace SparseDeletion

open Finset

attribute [local instance] Classical.propDecidable

section Squares

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The exact number of square values in any finite field of odd
characteristic, including zero. -/
theorem card_square_values_exact (hF : ringChar F ≠ 2) :
    2 * ((Finset.univ : Finset F).filter IsSquare).card =
      Fintype.card F + 1 := by
  have hchar : quadraticCharSum (fun x : F => x) = 0 := by
    simpa only [quadraticCharSum] using (quadraticChar_sum_zero (F := F) hF)
  have hzero : zeroInputCount (fun x : F => x) = 1 := by
    rw [zeroInputCount_eq_card]
    have heq : ((Finset.univ : Finset F).filter (fun x : F => x = 0)) = {0} := by
      ext x
      simp
    rw [heq]
    simp
  have hcount := two_mul_square_count hF (fun x : F => x)
  rw [squareInputCount_eq_card, hchar, hzero] at hcount
  simpa only [add_zero] using (by exact_mod_cast hcount : 
    2 * ((Finset.univ : Finset F).filter IsSquare).card =
      Fintype.card F + 1)

#print axioms card_square_values_exact

end Squares

end SparseDeletion
