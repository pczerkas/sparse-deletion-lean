module -- shake: keep-all

public import QuadraticCharBridge
public import Mathlib.Algebra.Polynomial.Roots

@[expose] public section

namespace SparseDeletion

section CubicRoots
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem polynomial_zero_count_le_natDegree (p : Polynomial F)
    (hp : p ≠ 0) :
    ((Finset.univ : Finset F).filter (fun x => p.eval x = 0)).card ≤
      p.natDegree := by
  classical
  apply Polynomial.card_le_degree_of_subset_roots
  intro x hx
  apply (Polynomial.mem_roots hp).2
  exact (Finset.mem_filter.mp hx).2

theorem zeroInputCount_poly_le_degree (p : Polynomial F) (hp : p ≠ 0) :
    zeroInputCount (fun x => p.eval x) ≤ (p.natDegree : ℤ) := by
  rw [zeroInputCount_eq_card]
  exact_mod_cast polynomial_zero_count_le_natDegree p hp

/-- From a cubic character bound to 3/4 good residues, now with
the <=3 roots verified using polynomial root-counting. -/
theorem cubic_square_card_le_three_quarters
    (hF : ringChar F ≠ 2) (p : Polynomial F)
    (hp : p ≠ 0) (hdegree : p.natDegree ≤ 3)
    (hchar : 2 * quadraticCharSum (fun x => p.eval x) + 6 ≤
      (Fintype.card F : ℤ)) :
    4 * ((Finset.univ : Finset F).filter
      (fun x => IsSquare (p.eval x))).card ≤ 3 * Fintype.card F := by
  have hz : (((Finset.univ : Finset F).filter
      (fun x => p.eval x = 0)).card : ℤ) ≤ 3 := by
    exact_mod_cast (polynomial_zero_count_le_natDegree p hp).trans hdegree
  exact square_card_le_three_quarters hF (fun x => p.eval x) hz hchar

#print axioms polynomial_zero_count_le_natDegree
#print axioms zeroInputCount_poly_le_degree
#print axioms cubic_square_card_le_three_quarters

end CubicRoots
end SparseDeletion
