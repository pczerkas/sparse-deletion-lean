module -- shake: keep-all

public import DensityBridge
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open Filter

namespace SparseDeletion

/-- If a uniformly strong cubic sieve exists for every r, the value-indexed
triangular hits of a zero-density deletion have density zero. The sieve
assumption is NOT yet established in general. -/
theorem zeroDensityByValue_of_all_sieves (E : Set ℕ)
    (hE : HasDensityZero E)
    (hsieves : ∀ r : ℕ, ∃ M : ℕ, 0 < M ∧
       ∀ (u : ℕ) (b : ℤ),
          4 ^ r * (cubicCandidates u M b).card ≤ 3 ^ r * M) :
    HasDensityZero (hitSet E) := by
  unfold HasDensityZero
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun N => by
      have hnonneg : 0 ≤
          (countUpTo (hitSet E) N : ℝ) / (N : ℝ) :=
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      exact lt_of_lt_of_le ha hnonneg)
  · intro a ha
    have hgeo : Tendsto (fun r : ℕ => ((3 : ℝ) / 4) ^ r)
        atTop (nhds (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hev : ∀ᶠ r : ℕ in atTop, ((3 : ℝ) / 4) ^ r < a / 2 :=
      hgeo.eventually (eventually_lt_nhds (by linarith))
    obtain ⟨r, hr⟩ := hev.exists
    obtain ⟨M, hM, hsieve⟩ := hsieves r
    let C : ℕ := (3 ^ r * M) / (4 ^ r)
    have hC : ∀ (u : ℕ) (b : ℤ),
        (cubicCandidates u M b).card ≤ C := by
      intro u b
      apply (Nat.le_div_iff_mul_le (pow_pos (by decide) r)).2
      simpa only [C, mul_comm] using hsieve u b
    have hCscaled : 4 ^ r * C ≤ 3 ^ r * M := by
      dsimp [C]
      simpa [mul_comm] using Nat.div_mul_le_self (3 ^ r * M) (4 ^ r)
    have hreal : (4 : ℝ) ^ r * (C : ℝ) ≤
        (3 : ℝ) ^ r * (M : ℝ) := by
      exact_mod_cast hCscaled
    have hposM : (0 : ℝ) < M := by exact_mod_cast hM
    have hpos4 : (0 : ℝ) < (4 : ℝ) ^ r := pow_pos (by norm_num) _
    have hratio : (C : ℝ) / (M : ℝ) ≤ ((3 : ℝ) / 4) ^ r := by
      rw [div_pow]
      apply (div_le_div_iff₀ hposM hpos4).2
      nlinarith [hreal]
    have happrox :=
      eventually_hit_ratio_le E hE M C hM hC (a / 2) (by linarith)
    filter_upwards [happrox] with N hbound
    linarith

end SparseDeletion

#print axioms SparseDeletion.zeroDensityByValue_of_all_sieves
