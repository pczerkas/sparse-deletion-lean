module -- shake: keep-all

public import QuantitativeHalfChoice

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-!
# Improved exponent: log(7/6)/2

Uses the Chebyshev-derived prime bound p_r <= 16*(r+50)^2,
and r = floor(L/(2*log L)) for L=log Q>=2048.
This is an optional extension, not a dependency of the main theorem.
-/

private theorem logarithmic_sieve_contraction_half
    (L : ℝ) (hL : 2048 ≤ L) :
    let r : ℕ := ⌊L / (2 * Real.log L)⌋₊
    2 * ((6 : ℝ) / 7) ^ r ≤
      (7 / 3 : ℝ) * Real.exp
        (-(Real.log ((7 : ℝ) / 6)) * (L / (2 * Real.log L))) := by
  dsimp
  let t : ℝ := L / (2 * Real.log L)
  let r : ℕ := ⌊t⌋₊
  let c : ℝ := Real.log ((7 : ℝ) / 6)
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hfloor : t < (r : ℝ) + 1 := Nat.lt_floor_add_one t
  have hmult : c * t < c * ((r : ℝ) + 1) :=
    mul_lt_mul_of_pos_left hfloor hc
  have harg : -(r : ℝ) * c ≤ c - c * t := by
    nlinarith
  have hinv : ((6 : ℝ) / 7) = ((7 : ℝ) / 6)⁻¹ := by
    norm_num
  have hp : ((6 : ℝ) / 7) ^ r =
      Real.exp (-(r : ℝ) * c) := by
    calc
      ((6 : ℝ) / 7) ^ r =
          Real.exp (Real.log (((6 : ℝ) / 7) ^ r)) :=
        (Real.exp_log (pow_pos (by norm_num) r)).symm
      _ = Real.exp ((r : ℝ) * Real.log ((6 : ℝ) / 7)) := by
        rw [Real.log_pow]
      _ = Real.exp (-(r : ℝ) * c) := by
        rw [hinv, Real.log_inv]
        dsimp [c]
        ring
  have he : (2 : ℝ) * Real.exp (-(r : ℝ) * c) ≤
      2 * Real.exp (c - c * t) := by
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr harg) (by norm_num)
  have heq : (2 : ℝ) * Real.exp (c - c * t) =
      (7 / 3 : ℝ) * Real.exp (-c * t) := by
    dsimp [c]
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 7 / 6)]
    ring_nf
  calc
    2 * ((6 : ℝ) / 7) ^ r =
        2 * Real.exp (-(r : ℝ) * c) := by rw [hp]
    _ ≤ 2 * Real.exp (c - c * t) := he
    _ = (7 / 3 : ℝ) * Real.exp (-c * t) := heq

/-- Fully explicit log/loglog decay for value-index triangular hits.
The ratio Q=N/(e(N)+1) is required to be extremely large solely to
simplify the elementary numerical constants. -/
theorem quantitative_value_loglog_bound_half
    (E : Set ℕ) (N : ℕ) (hN : 0 < N)
    (hQ : 2048 ≤ Real.log ((N : ℝ) / (countUpTo E N + 1))) :
    let L := Real.log ((N : ℝ) / (countUpTo E N + 1))
    ((countUpTo (hitSet E) N : ℝ) / (N : ℝ)) ≤
      (7 / 3 : ℝ) * Real.exp
        (-(Real.log ((7 : ℝ) / 6)) * (L / (2 * Real.log L))) := by
  dsimp
  let L : ℝ := Real.log ((N : ℝ) / (countUpTo E N + 1))
  let r : ℕ := ⌊L / (2 * Real.log L)⌋₊
  have hbudget :
      (112 * (r + 50) ^ 2) ^ r * (countUpTo E N + 1) ≤ N := by
    simpa only [r, L] using quantitative_half_log_choice_budget E N hN hQ
  have hf := quantitative_value_frequency_real_half E N r hN hbudget
  have hlog : 2 * ((6 : ℝ) / 7) ^ r ≤
      (7 / 3 : ℝ) * Real.exp
        (-(Real.log ((7 : ℝ) / 6)) * (L / (2 * Real.log L))) :=
    logarithmic_sieve_contraction_half L hQ
  exact hf.trans hlog

/-- Same rate for the index within the retained sequence. The
standard Nth-survivor bound remains an explicit hypothesis. -/
theorem quantitative_index_loglog_bound_half
    (E : Set ℕ) (hInf : (Set.ofPred (keptPred E)).Infinite)
    (N : ℕ) (hNth : keptNth E N < 2 * N + 2)
    (hQ : 2048 ≤ Real.log
      (((2 * N + 2 : ℕ) : ℝ) /
        (countUpTo E (2 * N + 2) + 1))) :
    let L := Real.log
      (((2 * N + 2 : ℕ) : ℝ) / (countUpTo E (2 * N + 2) + 1))
    ((countUpTo (indexHitSet E) (N + 1) : ℝ) /
        ((2 * N + 2 : ℕ) : ℝ)) ≤
      (7 / 3 : ℝ) * Real.exp
        (-(Real.log ((7 : ℝ) / 6)) * (L / (2 * Real.log L))) := by
  dsimp
  let L : ℝ := Real.log
    (((2 * N + 2 : ℕ) : ℝ) / (countUpTo E (2 * N + 2) + 1))
  let r : ℕ := ⌊L / (2 * Real.log L)⌋₊
  have hN : 0 < 2 * N + 2 := by omega
  have hbudget :
      (112 * (r + 50) ^ 2) ^ r *
        (countUpTo E (2 * N + 2) + 1) ≤ (2 * N + 2) := by
    simpa only [r, L] using
      quantitative_half_log_choice_budget E (2 * N + 2) hN hQ
  have hf := quantitative_index_frequency_real_half E hInf N r hNth hbudget
  have hlog : 2 * ((6 : ℝ) / 7) ^ r ≤
      (7 / 3 : ℝ) * Real.exp
        (-(Real.log ((7 : ℝ) / 6)) * (L / (2 * Real.log L))) :=
    logarithmic_sieve_contraction_half L hQ
  exact hf.trans hlog


end SparseDeletion
