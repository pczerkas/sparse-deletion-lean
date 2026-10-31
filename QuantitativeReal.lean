module -- shake: keep-all

public import QuantitativeRate

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-!
# Bridge from the integer-valued finite rate to real-density inequalities

No logarithmic optimization occurs in this module. Its goal is to
certificate the *exact real inequality* needed for the subsequent
selection r = floor(log(Q)/(8*log(log(Q)))).
-/

/-- Elementary real translation of the finite integer inequality.
The natural-number proof avoids real analysis; the conclusion is in
the format needed for the asymptotic logarithmic optimization. -/
private theorem real_ratio_of_scaled_bound
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
theorem quantitative_value_frequency_real
    (E : Set ℕ) (N r : ℕ) (hN : 0 < N)
    (hbudget :
      (448 * (r + 50) ^ 2) ^ r * (countUpTo E N + 1) ≤ N) :
    ((countUpTo (hitSet E) N : ℝ) / (N : ℝ)) ≤
        2 * ((6 : ℝ) / 7) ^ r := by
  exact real_ratio_of_scaled_bound
    (countUpTo (hitSet E) N) N r hN
    (quantitative_value_bound_under_polynomial_budget E r N hbudget)

/-- Retained-sequence frequency normalized by 2N+2.
The value-Nth-survivor condition remains explicit. -/
theorem quantitative_index_frequency_real
    (E : Set ℕ) (hInf : (Set.ofPred (keptPred E)).Infinite)
    (N r : ℕ) (hNth : keptNth E N < 2 * N + 2)
    (hbudget :
      (448 * (r + 50) ^ 2) ^ r *
          (countUpTo E (2 * N + 2) + 1) ≤ (2 * N + 2)) :
    ((countUpTo (indexHitSet E) (N + 1) : ℝ) /
        (2 * N + 2 : ℕ)) ≤
      2 * ((6 : ℝ) / 7) ^ r := by
  have hn : 0 < 2 * N + 2 := by omega
  exact real_ratio_of_scaled_bound
    (countUpTo (indexHitSet E) (N + 1)) (2 * N + 2) r hn
    (quantitative_index_bound_under_polynomial_budget E hInf r N hNth hbudget)

end SparseDeletion
