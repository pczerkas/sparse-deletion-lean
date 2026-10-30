module -- shake: keep-all

public import PolynomialRootsBridge
public import Mathlib.Tactic.ComputeDegree

@[expose] public section

namespace SparseDeletion

open Polynomial

section CubicShape
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def cubicShape (a b c d : F) : Polynomial F :=
  C a * X ^ 3 + C b * X ^ 2 + C c * X + C d

omit [Fintype F] [DecidableEq F] in
theorem cubicShape_natDegree (a b c d : F) (ha : a ≠ 0) :
    (cubicShape a b c d).natDegree = 3 := by
  unfold cubicShape
  compute_degree!

omit [Fintype F] [DecidableEq F] in
theorem cubicShape_ne_zero (a b c d : F) (ha : a ≠ 0) :
    cubicShape a b c d ≠ 0 := by
  intro heq
  have hn := cubicShape_natDegree a b c d ha
  rw [heq] at hn
  norm_num at hn

theorem cubicShape_roots_le_three (a b c d : F) (ha : a ≠ 0) :
    ((Finset.univ : Finset F).filter
      (fun x => (cubicShape a b c d).eval x = 0)).card ≤ 3 := by
  exact (polynomial_zero_count_le_natDegree _ (cubicShape_ne_zero a b c d ha)).trans
    (cubicShape_natDegree a b c d ha).le

theorem cubicShape_three_quarters (hF : ringChar F ≠ 2)
    (a b c d : F) (ha : a ≠ 0)
    (hchi : 2 * quadraticCharSum (fun x => (cubicShape a b c d).eval x) + 6 ≤
      (Fintype.card F : ℤ)) :
    4 * ((Finset.univ : Finset F).filter
      (fun x => IsSquare ((cubicShape a b c d).eval x))).card ≤
      3 * Fintype.card F := by
  apply cubic_square_card_le_three_quarters hF _ (cubicShape_ne_zero a b c d ha)
  · rw [cubicShape_natDegree a b c d ha]
  · exact hchi

#print axioms cubicShape_natDegree
#print axioms cubicShape_ne_zero
#print axioms cubicShape_roots_le_three
#print axioms cubicShape_three_quarters

end CubicShape
end SparseDeletion
