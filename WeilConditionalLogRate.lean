module -- shake: keep-all

public import WeilSingleHypothesis

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-!
# Explicit log/loglog rate conditional on one Weil character-sum hypothesis

Every reduction below is a Lean proof; the only *stated* hypothesis
is the character-sum estimate CubicWeilCharacterUpper, which is not
currently proved in the pinned Mathlib version.
-/

private theorem real_ratio_of_scaled_bound_weil
    (a N r : ℕ) (hN : 0 < N)
    (h : 4 ^ r * a ≤ 2 * 3 ^ r * N) :
    (a : ℝ) / (N : ℝ) ≤ 2 * ((3 : ℝ) / 4) ^ r := by
  have hc : (4 : ℝ) ^ r * (a : ℝ) ≤
      2 * (3 : ℝ) ^ r * (N : ℝ) := by
    exact_mod_cast h
  have hn : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have h4 : (0 : ℝ) < (4 : ℝ) ^ r := pow_pos (by norm_num) r
  rw [div_pow]
  apply (div_le_iff₀ hn).2
  calc
    (a : ℝ) ≤
        (2 * (3 : ℝ) ^ r * (N : ℝ)) / (4 : ℝ) ^ r := by
      apply (le_div_iff₀ h4).2
      nlinarith [hc]
    _ = (2 * ((3 : ℝ) ^ r / (4 : ℝ) ^ r)) * (N : ℝ) := by ring

/-- Under the certified 112-budget, the conditional 3/4 CRT sieve
gives a real-frequency bound 2*(3/4)^r. -/
theorem quantitative_weil_value_frequency_real
    (hWeil : CubicWeilCharacterUpper)
    (E : Set ℕ) (N r : ℕ) (hN : 0 < N)
    (hbudget :
      (112 * (r + 50) ^ 2) ^ r * (countUpTo E N + 1) ≤ N) :
    ((countUpTo (hitSet E) N : ℝ) / (N : ℝ)) ≤
        2 * ((3 : ℝ) / 4) ^ r := by
  have hterm :
      4 ^ r * (16 * (r + 50) ^ 2) ^ r *
          (countUpTo E N + 1) ≤ N := by
    calc
      4 ^ r * (16 * (r + 50) ^ 2) ^ r *
          (countUpTo E N + 1) =
        (64 * (r + 50) ^ 2) ^ r *
          (countUpTo E N + 1) := by
          rw [← mul_pow]
          have hbase : 4 * (16 * (r + 50) ^ 2) =
              64 * (r + 50) ^ 2 := by ring
          rw [hbase]
      _ ≤ (112 * (r + 50) ^ 2) ^ r *
          (countUpTo E N + 1) := by gcongr; omega
      _ ≤ N := hbudget
  have hdom : N ≤ 3 ^ r * N := by
    calc
      N = 1 * N := by simp
      _ ≤ 3 ^ r * N := Nat.mul_le_mul_right N
        (one_le_pow₀ (by decide : 1 ≤ (3 : ℕ)))
  have hb := quantitative_weil_value_bound_of_character_upper hWeil E r N
  have htotal : 4 ^ r * countUpTo (hitSet E) N ≤
      2 * 3 ^ r * N := by
    calc
      4 ^ r * countUpTo (hitSet E) N ≤
        3 ^ r * N +
          4 ^ r * (16 * (r + 50) ^ 2) ^ r *
            (countUpTo E N + 1) := hb
      _ ≤ 3 ^ r * N + N := Nat.add_le_add_left hterm _
      _ ≤ 3 ^ r * N + 3 ^ r * N := Nat.add_le_add_left hdom _
      _ = 2 * 3 ^ r * N := by ring
  exact real_ratio_of_scaled_bound_weil
    (countUpTo (hitSet E) N) N r hN htotal

/-- Conditional real-frequency estimate for surviving sequence indices. -/
theorem quantitative_weil_index_frequency_real
    (hWeil : CubicWeilCharacterUpper)
    (E : Set ℕ) (hInf : (Set.ofPred (keptPred E)).Infinite)
    (N r : ℕ) (hNth : keptNth E N < 2 * N + 2)
    (hbudget :
      (112 * (r + 50) ^ 2) ^ r *
          (countUpTo E (2 * N + 2) + 1) ≤ (2 * N + 2)) :
    ((countUpTo (indexHitSet E) (N + 1) : ℝ) /
        ((2 * N + 2 : ℕ) : ℝ)) ≤
      2 * ((3 : ℝ) / 4) ^ r := by
  have hN : 0 < 2 * N + 2 := by omega
  have hterm :
      4 ^ r * (16 * (r + 50) ^ 2) ^ r *
          (countUpTo E (2 * N + 2) + 1) ≤ (2 * N + 2) := by
    calc
      4 ^ r * (16 * (r + 50) ^ 2) ^ r *
          (countUpTo E (2 * N + 2) + 1) =
        (64 * (r + 50) ^ 2) ^ r *
          (countUpTo E (2 * N + 2) + 1) := by
          rw [← mul_pow]
          have hbase : 4 * (16 * (r + 50) ^ 2) =
              64 * (r + 50) ^ 2 := by ring
          rw [hbase]
      _ ≤ (112 * (r + 50) ^ 2) ^ r *
          (countUpTo E (2 * N + 2) + 1) := by gcongr; omega
      _ ≤ 2 * N + 2 := hbudget
  have hdom : 2 * N + 2 ≤ 3 ^ r * (2 * N + 2) := by
    calc
      2 * N + 2 = 1 * (2 * N + 2) := by simp
      _ ≤ 3 ^ r * (2 * N + 2) := Nat.mul_le_mul_right _
        (one_le_pow₀ (by decide : 1 ≤ (3 : ℕ)))
  have hb := quantitative_weil_index_bound_of_character_upper hWeil
    E hInf r N hNth
  have htotal :
      4 ^ r * countUpTo (indexHitSet E) (N + 1) ≤
        2 * 3 ^ r * (2 * N + 2) := by
    calc
      4 ^ r * countUpTo (indexHitSet E) (N + 1) ≤
        3 ^ r * (2 * N + 2) +
          4 ^ r * (16 * (r + 50) ^ 2) ^ r *
            (countUpTo E (2 * N + 2) + 1) := hb
      _ ≤ 3 ^ r * (2 * N + 2) + (2 * N + 2) :=
        Nat.add_le_add_left hterm _
      _ ≤ 3 ^ r * (2 * N + 2) + 3 ^ r * (2 * N + 2) :=
        Nat.add_le_add_left hdom _
      _ = 2 * 3 ^ r * (2 * N + 2) := by ring
  exact real_ratio_of_scaled_bound_weil
    (countUpTo (indexHitSet E) (N + 1)) (2 * N + 2) r hN htotal

private theorem logarithmic_sieve_contraction_weil
    (L : ℝ) (hL : 2048 ≤ L) :
    let r : ℕ := ⌊L / (2 * Real.log L)⌋₊
    2 * ((3 : ℝ) / 4) ^ r ≤
      (8 / 3 : ℝ) * Real.exp
        (-(Real.log ((4 : ℝ) / 3)) * (L / (2 * Real.log L))) := by
  dsimp
  let t : ℝ := L / (2 * Real.log L)
  let r : ℕ := ⌊t⌋₊
  let c : ℝ := Real.log ((4 : ℝ) / 3)
  have hc : 0 < c := Real.log_pos (by norm_num)
  have hfloor : t < (r : ℝ) + 1 := Nat.lt_floor_add_one t
  have hmult : c * t < c * ((r : ℝ) + 1) :=
    mul_lt_mul_of_pos_left hfloor hc
  have harg : -(r : ℝ) * c ≤ c - c * t := by
    nlinarith
  have hinv : ((3 : ℝ) / 4) = ((4 : ℝ) / 3)⁻¹ := by
    norm_num
  have hp : ((3 : ℝ) / 4) ^ r =
      Real.exp (-(r : ℝ) * c) := by
    calc
      ((3 : ℝ) / 4) ^ r =
          Real.exp (Real.log (((3 : ℝ) / 4) ^ r)) :=
        (Real.exp_log (pow_pos (by norm_num) r)).symm
      _ = Real.exp ((r : ℝ) * Real.log ((3 : ℝ) / 4)) := by
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
      (8 / 3 : ℝ) * Real.exp (-c * t) := by
    dsimp [c]
    rw [sub_eq_add_neg, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3)]
    ring_nf
  calc
    2 * ((3 : ℝ) / 4) ^ r =
        2 * Real.exp (-(r : ℝ) * c) := by rw [hp]
    _ ≤ 2 * Real.exp (c - c * t) := he
    _ = (8 / 3 : ℝ) * Real.exp (-c * t) := heq

/-- Fully explicit log/loglog decay for value-index triangular hits.
The ratio Q=N/(e(N)+1) is required to be extremely large solely to
simplify the elementary numerical constants. -/
theorem quantitative_weil_value_loglog_bound
    (hWeil : CubicWeilCharacterUpper)
    (E : Set ℕ) (N : ℕ) (hN : 0 < N)
    (hQ : 2048 ≤ Real.log ((N : ℝ) / (countUpTo E N + 1))) :
    let L := Real.log ((N : ℝ) / (countUpTo E N + 1))
    ((countUpTo (hitSet E) N : ℝ) / (N : ℝ)) ≤
      (8 / 3 : ℝ) * Real.exp
        (-(Real.log ((4 : ℝ) / 3)) * (L / (2 * Real.log L))) := by
  dsimp
  let L : ℝ := Real.log ((N : ℝ) / (countUpTo E N + 1))
  let r : ℕ := ⌊L / (2 * Real.log L)⌋₊
  have hbudget :
      (112 * (r + 50) ^ 2) ^ r * (countUpTo E N + 1) ≤ N := by
    simpa only [r, L] using quantitative_half_log_choice_budget E N hN hQ
  have hf := quantitative_weil_value_frequency_real hWeil E N r hN hbudget
  have hlog : 2 * ((3 : ℝ) / 4) ^ r ≤
      (8 / 3 : ℝ) * Real.exp
        (-(Real.log ((4 : ℝ) / 3)) * (L / (2 * Real.log L))) :=
    logarithmic_sieve_contraction_weil L hQ
  exact hf.trans hlog

/-- Same rate for the index within the retained sequence. The
standard Nth-survivor bound remains an explicit hypothesis. -/
theorem quantitative_weil_index_loglog_bound
    (hWeil : CubicWeilCharacterUpper)
    (E : Set ℕ) (hInf : (Set.ofPred (keptPred E)).Infinite)
    (N : ℕ) (hNth : keptNth E N < 2 * N + 2)
    (hQ : 2048 ≤ Real.log
      (((2 * N + 2 : ℕ) : ℝ) /
        (countUpTo E (2 * N + 2) + 1))) :
    let L := Real.log
      (((2 * N + 2 : ℕ) : ℝ) / (countUpTo E (2 * N + 2) + 1))
    ((countUpTo (indexHitSet E) (N + 1) : ℝ) /
        ((2 * N + 2 : ℕ) : ℝ)) ≤
      (8 / 3 : ℝ) * Real.exp
        (-(Real.log ((4 : ℝ) / 3)) * (L / (2 * Real.log L))) := by
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
  have hf := quantitative_weil_index_frequency_real hWeil E hInf N r hNth hbudget
  have hlog : 2 * ((3 : ℝ) / 4) ^ r ≤
      (8 / 3 : ℝ) * Real.exp
        (-(Real.log ((4 : ℝ) / 3)) * (L / (2 * Real.log L))) :=
    logarithmic_sieve_contraction_weil L hQ
  exact hf.trans hlog


end SparseDeletion
