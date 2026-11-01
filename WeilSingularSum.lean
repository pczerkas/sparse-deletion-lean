module -- shake: keep-all

public import WeilSingularPointwise

@[expose] public section

namespace SparseDeletion

open Finset

attribute [local instance] Classical.propDecidable

/-!
# Complete singular cubic quadratic-character sum

For any finite field of characteristic different from two,
a cubic with a double root has character sum equal to
minus the product of two quadratic characters.
This is elementary and requires no Hasse or Weil theorem.
-/

/-- Translation invariance plus nontriviality makes the
quadratic-character sum of a shifted linear factor zero. -/
theorem quadraticCharFun_sum_sub_zero
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (v : F) :
    (∑ x : F, quadraticCharFun F (x - v)) = 0 := by
  have hz : (∑ x : F, quadraticCharFun F x) = 0 := by
    simpa only [quadraticChar_apply] using
      (quadraticChar_sum_zero (F := F) hF)
  calc
    (∑ x : F, quadraticCharFun F (x - v)) =
        (∑ x : F, quadraticCharFun F x) := by
          simpa [Equiv.addRight, sub_eq_add_neg, add_comm] using
            (Equiv.sum_comp (Equiv.addRight (-v)) (quadraticCharFun F))
    _ = 0 := hz

/-- Exact sum of the quadratic character of
a cubic with a double root. -/
theorem quadraticCharFun_double_root_sum
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (a u v : F) :
    (∑ x : F, quadraticCharFun F (a * (x - u)^2 * (x - v))) =
      -(quadraticCharFun F a) * quadraticCharFun F (u - v) := by
  classical
  calc
    (∑ x : F, quadraticCharFun F (a * (x - u)^2 * (x - v))) =
      ∑ x : F, if x = u then (0 : ℤ)
        else quadraticCharFun F a * quadraticCharFun F (x - v) := by
          apply Finset.sum_congr rfl
          intro x _
          exact quadraticCharFun_double_root_pointwise F a u v x
    _ = ∑ x : F, (quadraticCharFun F a * quadraticCharFun F (x - v) -
        if x = u then quadraticCharFun F a * quadraticCharFun F (x - v)
        else (0 : ℤ)) := by
          apply Finset.sum_congr rfl
          intro x _
          split_ifs <;> ring
    _ = (∑ x : F, quadraticCharFun F a * quadraticCharFun F (x - v)) -
        (∑ x : F, if x = u then
          quadraticCharFun F a * quadraticCharFun F (x - v) else (0 : ℤ)) := by
          rw [Finset.sum_sub_distrib]
    _ = quadraticCharFun F a *
        (∑ x : F, quadraticCharFun F (x - v)) -
        quadraticCharFun F a * quadraticCharFun F (u - v) := by
          rw [← Finset.mul_sum, Finset.sum_ite_eq']
          simp
    _ = -(quadraticCharFun F a) * quadraticCharFun F (u - v) := by
          rw [quadraticCharFun_sum_sub_zero F hF v]
          ring

end SparseDeletion
