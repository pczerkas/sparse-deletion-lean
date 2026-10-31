module -- shake: keep-all

public import QuantitativePolynomial

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-!
# Certified finite quantitative rate without real logarithms

The numeric threshold below makes the choice of sieve depth r explicit.
It is the algebraic part of the real-logarithm optimization; the latter
can be formalized separately without changing the main theorem.
-/

/-- We can always replace the coefficient 6^r by its lower bound 1. -/
private theorem one_le_six_pow (r : ℕ) : 1 ≤ 6 ^ r := by
  exact one_le_pow₀ (by decide : 1 ≤ (6 : ℕ))

/-- Exponential threshold that guarantees the perturbation contribution
is no larger than the main sieve term. -/
theorem quantitative_value_bound_under_polynomial_budget
    (E : Set ℕ) (r N : ℕ)
    (hbudget :
      (448 * (r + 50) ^ 2) ^ r * (countUpTo E N + 1) ≤ N) :
    7 ^ r * countUpTo (hitSet E) N ≤ 2 * 6 ^ r * N := by
  have hterm :
      7 ^ r * (64 * (r + 50) ^ 2) ^ r *
          (countUpTo E N + 1) ≤ N := by
    calc
      7 ^ r * (64 * (r + 50) ^ 2) ^ r *
          (countUpTo E N + 1) =
        (448 * (r + 50) ^ 2) ^ r *
          (countUpTo E N + 1) := by
          rw [← mul_pow]
          have hbase : 7 * (64 * (r + 50) ^ 2) =
              448 * (r + 50) ^ 2 := by ring
          rw [hbase]
      _ ≤ N := hbudget
  have hdominates : N ≤ 6 ^ r * N := by
    calc
      N = 1 * N := by simp
      _ ≤ 6 ^ r * N := Nat.mul_le_mul_right N (one_le_six_pow r)
  have hsieve := quantitative_value_bound_polynomial E r N
  calc
    7 ^ r * countUpTo (hitSet E) N ≤
      6 ^ r * N +
        7 ^ r * (64 * (r + 50) ^ 2) ^ r *
          (countUpTo E N + 1) := hsieve
    _ ≤ 6 ^ r * N + N := Nat.add_le_add_left hterm _
    _ ≤ 6 ^ r * N + 6 ^ r * N := Nat.add_le_add_left hdominates _
    _ = 2 * 6 ^ r * N := by ring

/-- A similar fully explicit finite budget for indices of the surviving
sequence. The assumption on the Nth survivor is inherited unchanged
from IndexTransfer, so this is outside the main theorem's import graph. -/
theorem quantitative_index_bound_under_polynomial_budget
    (E : Set ℕ) (hInf : (Set.ofPred (keptPred E)).Infinite)
    (r N : ℕ) (hNth : keptNth E N < 2 * N + 2)
    (hbudget :
      (448 * (r + 50) ^ 2) ^ r *
          (countUpTo E (2 * N + 2) + 1) ≤ (2 * N + 2)) :
    7 ^ r * countUpTo (indexHitSet E) (N + 1) ≤
      2 * 6 ^ r * (2 * N + 2) := by
  have hterm :
      7 ^ r * (64 * (r + 50) ^ 2) ^ r *
          (countUpTo E (2 * N + 2) + 1) ≤ (2 * N + 2) := by
    calc
      7 ^ r * (64 * (r + 50) ^ 2) ^ r *
          (countUpTo E (2 * N + 2) + 1) =
        (448 * (r + 50) ^ 2) ^ r *
          (countUpTo E (2 * N + 2) + 1) := by
          rw [← mul_pow]
          have hbase : 7 * (64 * (r + 50) ^ 2) =
              448 * (r + 50) ^ 2 := by ring
          rw [hbase]
      _ ≤ 2 * N + 2 := hbudget
  have hdominates : 2 * N + 2 ≤ 6 ^ r * (2 * N + 2) := by
    calc
      2 * N + 2 = 1 * (2 * N + 2) := by simp
      _ ≤ 6 ^ r * (2 * N + 2) :=
        Nat.mul_le_mul_right _ (one_le_six_pow r)
  have hsieve := quantitative_index_bound_polynomial E hInf r N hNth
  calc
    7 ^ r * countUpTo (indexHitSet E) (N + 1) ≤
      6 ^ r * (2 * N + 2) +
        7 ^ r * (64 * (r + 50) ^ 2) ^ r *
          (countUpTo E (2 * N + 2) + 1) := hsieve
    _ ≤ 6 ^ r * (2 * N + 2) + (2 * N + 2) :=
      Nat.add_le_add_left hterm _
    _ ≤ 6 ^ r * (2 * N + 2) + 6 ^ r * (2 * N + 2) :=
      Nat.add_le_add_left hdominates _
    _ = 2 * 6 ^ r * (2 * N + 2) := by ring

end SparseDeletion
