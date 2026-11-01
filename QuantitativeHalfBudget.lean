module -- shake: keep-all

public import QuantitativeConstants

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-!
# Improved polynomial perturbation budget using the smaller prime bound

7 * 16 = 112. The finite budget and its real-frequency translation
are proved separately from the old (7 * 64 = 448) estimates.
-/

private theorem one_le_six_pow_half (r : ℕ) : 1 ≤ 6 ^ r := by
  exact one_le_pow₀ (by decide : 1 ≤ (6 : ℕ))

/-- Exponential threshold that guarantees the perturbation contribution
is no larger than the main sieve term. -/
theorem quantitative_value_bound_under_polynomial_budget_half
    (E : Set ℕ) (r N : ℕ)
    (hbudget :
      (112 * (r + 50) ^ 2) ^ r * (countUpTo E N + 1) ≤ N) :
    7 ^ r * countUpTo (hitSet E) N ≤ 2 * 6 ^ r * N := by
  have hterm :
      7 ^ r * (16 * (r + 50) ^ 2) ^ r *
          (countUpTo E N + 1) ≤ N := by
    calc
      7 ^ r * (16 * (r + 50) ^ 2) ^ r *
          (countUpTo E N + 1) =
        (112 * (r + 50) ^ 2) ^ r *
          (countUpTo E N + 1) := by
          rw [← mul_pow]
          have hbase : 7 * (16 * (r + 50) ^ 2) =
              112 * (r + 50) ^ 2 := by ring
          rw [hbase]
      _ ≤ N := hbudget
  have hdominates : N ≤ 6 ^ r * N := by
    calc
      N = 1 * N := by simp
      _ ≤ 6 ^ r * N := Nat.mul_le_mul_right N (one_le_six_pow_half r)
  have hsieve := quantitative_value_bound_polynomial_16 E r N
  calc
    7 ^ r * countUpTo (hitSet E) N ≤
      6 ^ r * N +
        7 ^ r * (16 * (r + 50) ^ 2) ^ r *
          (countUpTo E N + 1) := hsieve
    _ ≤ 6 ^ r * N + N := Nat.add_le_add_left hterm _
    _ ≤ 6 ^ r * N + 6 ^ r * N := Nat.add_le_add_left hdominates _
    _ = 2 * 6 ^ r * N := by ring

/-- A similar fully explicit finite budget for indices of the surviving
sequence. The assumption on the Nth survivor is inherited unchanged
from IndexTransfer, so this is outside the main theorem's import graph. -/
theorem quantitative_index_bound_under_polynomial_budget_half
    (E : Set ℕ) (hInf : (Set.ofPred (keptPred E)).Infinite)
    (r N : ℕ) (hNth : keptNth E N < 2 * N + 2)
    (hbudget :
      (112 * (r + 50) ^ 2) ^ r *
          (countUpTo E (2 * N + 2) + 1) ≤ (2 * N + 2)) :
    7 ^ r * countUpTo (indexHitSet E) (N + 1) ≤
      2 * 6 ^ r * (2 * N + 2) := by
  have hterm :
      7 ^ r * (16 * (r + 50) ^ 2) ^ r *
          (countUpTo E (2 * N + 2) + 1) ≤ (2 * N + 2) := by
    calc
      7 ^ r * (16 * (r + 50) ^ 2) ^ r *
          (countUpTo E (2 * N + 2) + 1) =
        (112 * (r + 50) ^ 2) ^ r *
          (countUpTo E (2 * N + 2) + 1) := by
          rw [← mul_pow]
          have hbase : 7 * (16 * (r + 50) ^ 2) =
              112 * (r + 50) ^ 2 := by ring
          rw [hbase]
      _ ≤ 2 * N + 2 := hbudget
  have hdominates : 2 * N + 2 ≤ 6 ^ r * (2 * N + 2) := by
    calc
      2 * N + 2 = 1 * (2 * N + 2) := by simp
      _ ≤ 6 ^ r * (2 * N + 2) :=
        Nat.mul_le_mul_right _ (one_le_six_pow_half r)
  have hsieve := quantitative_index_bound_polynomial_16 E hInf r N hNth
  calc
    7 ^ r * countUpTo (indexHitSet E) (N + 1) ≤
      6 ^ r * (2 * N + 2) +
        7 ^ r * (16 * (r + 50) ^ 2) ^ r *
          (countUpTo E (2 * N + 2) + 1) := hsieve
    _ ≤ 6 ^ r * (2 * N + 2) + (2 * N + 2) :=
      Nat.add_le_add_left hterm _
    _ ≤ 6 ^ r * (2 * N + 2) + 6 ^ r * (2 * N + 2) :=
      Nat.add_le_add_left hdominates _
    _ = 2 * 6 ^ r * (2 * N + 2) := by ring


private theorem real_ratio_of_scaled_bound_half
    (a N r : ℕ) (hN : 0 < N)
    (h : 7 ^ r * a ≤ 2 * 6 ^ r * N) :
    (a : ℝ) / (N : ℝ) ≤ 2 * ((6 : ℝ) / 7) ^ r := by
  have hc : (7 : ℝ) ^ r * (a : ℝ) ≤
      2 * (6 : ℝ) ^ r * (N : ℝ) := by
    exact_mod_cast h
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h7 : (0 : ℝ) < (7 : ℝ) ^ r := pow_pos (by norm_num) r
  rw [div_pow]
  apply (div_le_iff₀ hn).2
  calc
    (a : ℝ) ≤
        (2 * (6 : ℝ) ^ r * (N : ℝ)) / (7 : ℝ) ^ r := by
      apply (le_div_iff₀ h7).2
      nlinarith [hc]
    _ = (2 * ((6 : ℝ) ^ r / (7 : ℝ) ^ r)) * (N : ℝ) := by ring

/-- For each explicitly admissible sieve depth r, the *actual relative
frequency* of hits is at most 2*(6/7)^r. -/
theorem quantitative_value_frequency_real_half
    (E : Set ℕ) (N r : ℕ) (hN : 0 < N)
    (hbudget :
      (112 * (r + 50) ^ 2) ^ r * (countUpTo E N + 1) ≤ N) :
    ((countUpTo (hitSet E) N : ℝ) / (N : ℝ)) ≤
        2 * ((6 : ℝ) / 7) ^ r := by
  exact real_ratio_of_scaled_bound_half
    (countUpTo (hitSet E) N) N r hN
    (quantitative_value_bound_under_polynomial_budget_half E r N hbudget)

/-- Retained-sequence frequency normalized by 2N+2.
The value-Nth-survivor condition remains explicit. -/
theorem quantitative_index_frequency_real_half
    (E : Set ℕ) (hInf : (Set.ofPred (keptPred E)).Infinite)
    (N r : ℕ) (hNth : keptNth E N < 2 * N + 2)
    (hbudget :
      (112 * (r + 50) ^ 2) ^ r *
          (countUpTo E (2 * N + 2) + 1) ≤ (2 * N + 2)) :
    ((countUpTo (indexHitSet E) (N + 1) : ℝ) /
        (2 * N + 2 : ℕ)) ≤
      2 * ((6 : ℝ) / 7) ^ r := by
  have hn : 0 < 2 * N + 2 := by omega
  exact real_ratio_of_scaled_bound_half
    (countUpTo (indexHitSet E) (N + 1)) (2 * N + 2) r hn
    (quantitative_index_bound_under_polynomial_budget_half E hInf r N hNth hbudget)


end SparseDeletion
