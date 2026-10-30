module -- shake: keep-all

public import DensityBridge
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open Filter

namespace SparseDeletion

/-- A uniformly contracting family of finite sieves forces zero density of
triangular hits indexed by retained values, for any density-zero deletion.
The arithmetic construction of the modular family is handled separately. -/
theorem zeroDensityByValue_of_uniform_ratio_sieves
    (numer denom : ℕ) (hnum : 0 < numer) (hfrac : numer < denom)
    (E : Set ℕ)
    (hE : HasDensityZero E)
    (hsieves : ∀ r : ℕ, ∃ M : ℕ, 0 < M ∧
       ∀ (u : ℕ) (b : ℤ),
          denom ^ r * (cubicCandidates u M b).card ≤ numer ^ r * M) :
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
    have hdenom_pos : (0 : ℝ) < (denom : ℝ) := by
      exact_mod_cast (lt_trans hnum hfrac)
    have hfracR : (numer : ℝ) < (denom : ℝ) := by
      exact_mod_cast hfrac
    have hratioNonneg : 0 ≤ (numer : ℝ) / (denom : ℝ) :=
      div_nonneg (Nat.cast_nonneg _) hdenom_pos.le
    have hratioLt : (numer : ℝ) / (denom : ℝ) < 1 :=
      (div_lt_one hdenom_pos).2 hfracR
    have hgeo : Tendsto (fun r : ℕ => ((numer : ℝ) / denom) ^ r)
        atTop (nhds (0 : ℝ)) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hratioNonneg hratioLt
    have hev : ∀ᶠ r : ℕ in atTop, ((numer : ℝ) / denom) ^ r < a / 2 :=
      hgeo.eventually (eventually_lt_nhds (by linarith))
    obtain ⟨r, hr⟩ := hev.exists
    obtain ⟨M, hM, hsieve⟩ := hsieves r
    let C : ℕ := (numer ^ r * M) / (denom ^ r)
    have hC : ∀ (u : ℕ) (b : ℤ),
        (cubicCandidates u M b).card ≤ C := by
      intro u b
      apply (Nat.le_div_iff_mul_le (pow_pos (lt_trans hnum hfrac) r)).2
      simpa only [C, mul_comm] using hsieve u b
    have hCscaled : denom ^ r * C ≤ numer ^ r * M := by
      dsimp [C]
      simpa [mul_comm] using Nat.div_mul_le_self (numer ^ r * M) (denom ^ r)
    have hreal : (denom : ℝ) ^ r * (C : ℝ) ≤
        (numer : ℝ) ^ r * (M : ℝ) := by
      exact_mod_cast hCscaled
    have hposM : (0 : ℝ) < M := by exact_mod_cast hM
    have hposDenom : (0 : ℝ) < (denom : ℝ) ^ r := pow_pos hdenom_pos _
    have hratio : (C : ℝ) / (M : ℝ) ≤ ((numer : ℝ) / denom) ^ r := by
      rw [div_pow]
      apply (div_le_div_iff₀ hposM hposDenom).2
      nlinarith [hreal]
    have happrox :=
      eventually_hit_ratio_le E hE M C hM hC (a / 2) (by linarith)
    filter_upwards [happrox] with N hbound
    linarith

end SparseDeletion

#print axioms SparseDeletion.zeroDensityByValue_of_uniform_ratio_sieves
