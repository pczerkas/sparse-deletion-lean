module

public import Mathlib

@[expose] public section

/-!
# Exact finite Fubini count for affine points

The cardinality of any relation on a finite Cartesian square is
the sum over the first coordinate of fiber cardinalities.
This lemma is purely combinatorial; no elliptic curves or
character bounds enter.
-/

namespace SparseDeletion.AINTLIBBridge

attribute [local instance] Classical.propDecidable

theorem affine_solution_count_eq_fiber_sum
    {K : Type*} [Fintype K] [DecidableEq K]
    (P : K → K → Prop) :
    (((Finset.univ : Finset (K × K)).filter
      (fun (xy : K × K) => P xy.1 xy.2)).card : ℤ) =
      ∑ x : K, (((Finset.univ : Finset K).filter
        (fun y => P x y)).card : ℤ) := by
  classical
  calc
    (((Finset.univ : Finset (K × K)).filter
      (fun (xy : K × K) => P xy.1 xy.2)).card : ℤ) =
        ∑ xy : K × K, if P xy.1 xy.2 then (1 : ℤ) else 0 := by
      simpa using (Finset.sum_boole
        (fun xy : K × K => P xy.1 xy.2)
        (Finset.univ : Finset (K × K))).symm
    _ = ∑ x : K, ∑ y : K, if P x y then (1 : ℤ) else 0 := by
      rw [Fintype.sum_prod_type']
    _ = ∑ x : K, (((Finset.univ : Finset K).filter
        (fun y => P x y)).card : ℤ) := by
      apply Finset.sum_congr rfl
      intro x hx
      simpa using (Finset.sum_boole
        (fun y : K => P x y) (Finset.univ : Finset K))

end SparseDeletion.AINTLIBBridge

#print axioms SparseDeletion.AINTLIBBridge.affine_solution_count_eq_fiber_sum
