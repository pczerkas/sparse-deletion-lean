import CubicShape
import SparseDeletion

namespace SparseDeletion

open Polynomial

section FormulaBridge
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem naturalSquareSum_field_cast (x : ℕ) (h6 : (6 : F) ≠ 0) :
    (((naturalSquareSum x : ℤ) : F)) =
      (6 : F)⁻¹ * (x : F) * ((x : F) + 1) * (2 * (x : F) + 1) := by
  have h := congrArg (fun t : ℤ => (t : F)) (naturalSquareSum_cubic x)
  push_cast at h
  calc
    (((naturalSquareSum x : ℤ) : F)) =
      (6 : F)⁻¹ * (6 * (((naturalSquareSum x : ℤ) : F))) := by
        field_simp
    _ = (6 : F)⁻¹ * (x : F) * ((x : F) + 1) *
          (2 * (x : F) + 1) := by
        rw [h]
        ring

theorem cubicShape_eval_nat (x : ℕ) (b : F) (h6 : (6 : F) ≠ 0) :
    (cubicShape (16 * (6 : F)⁻¹) (24 * (6 : F)⁻¹)
      (8 * (6 : F)⁻¹) (8 * b + 1)).eval (x : F) =
      8 * ((((naturalSquareSum x : ℤ) : F)) + b) + 1 := by
  rw [naturalSquareSum_field_cast x h6]
  simp only [cubicShape, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  ring

theorem cubicShape_sum_nonzero (b : F)
    (h6 : (6 : F) ≠ 0) (h16 : (16 : F) ≠ 0) :
    cubicShape (16 * (6 : F)⁻¹) (24 * (6 : F)⁻¹)
       (8 * (6 : F)⁻¹) (8 * b + 1) ≠ 0 := by
  apply cubicShape_ne_zero
  exact mul_ne_zero h16 (inv_ne_zero h6)

theorem cubicShape_sum_roots_le_three (b : F)
    (h6 : (6 : F) ≠ 0) (h16 : (16 : F) ≠ 0) :
    ((Finset.univ : Finset F).filter
      (fun x => (cubicShape (16 * (6 : F)⁻¹) (24 * (6 : F)⁻¹)
        (8 * (6 : F)⁻¹) (8 * b + 1)).eval x = 0)).card ≤ 3 := by
  apply cubicShape_roots_le_three
  exact mul_ne_zero h16 (inv_ne_zero h6)

#print axioms naturalSquareSum_field_cast
#print axioms cubicShape_eval_nat
#print axioms cubicShape_sum_roots_le_three

end FormulaBridge
end SparseDeletion
