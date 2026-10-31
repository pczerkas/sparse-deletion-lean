module -- shake: keep-all

public import QuantitativeConstants

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-!
# Improved exponent constant in the log/loglog decay

The original proof chooses depth floor(L/(8*log L)), but its cubic
elementary budget allows floor(L/(3*log L)) for L >= 2048.
Thus the explicit exponential rate constant improves from
log(7/6)/8 to log(7/6)/3. The threshold is unchanged.
-/

private theorem half_le_log_of_large_fast
    (L : ℝ) (hL : 2048 ≤ L) :
    (1 / 2 : ℝ) ≤ Real.log L := by
  have hlog2 : Real.log 2 ≤ Real.log L :=
    Real.log_le_log (by norm_num) (by linarith)
  have hnum := Real.log_two_gt_d9
  linarith

/-- For large L and r ≤ L/(8 log L), the polynomial CRT budget fits
under exp L; no PNT or conjectures are used. -/
private theorem budget_exponential_of_floor_bound_fast
    (L : ℝ) (hL : 2048 ≤ L) (r : ℕ)
    (hr : (r : ℝ) ≤ L / (3 * Real.log L)) :
    (((448 * (r + 50) ^ 2 : ℕ) : ℝ) ^ r) ≤ Real.exp L := by
  have hLpos : 0 < L := by linarith
  have hlog : (1 / 2 : ℝ) ≤ Real.log L :=
    half_le_log_of_large_fast L hL
  have hlogpos : 0 < 3 * Real.log L := by linarith
  have hrmul : (r : ℝ) * (3 * Real.log L) ≤ L :=
    (le_div_iff₀ hlogpos).mp hr
  have hrle : (r : ℝ) ≤ L := by
    have hnonneg : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have hfactor : 0 ≤ 3 * Real.log L - 1 := by linarith
    have hmul := mul_nonneg hnonneg hfactor
    nlinarith
  have hr50 : (r : ℝ) + 50 ≤ 2 * L := by linarith
  have hbase : (448 : ℝ) * ((r : ℝ) + 50) ^ 2 ≤ L ^ 3 := by
    have hsq : ((r : ℝ) + 50) ^ 2 ≤ (2 * L) ^ 2 := by
      gcongr
    have hother : (1792 : ℝ) * L ^ 2 ≤ L ^ 3 := by
      have hp := mul_nonneg (by linarith : 0 ≤ L - 1792) (sq_nonneg L)
      nlinarith
    nlinarith
  have hexp :
      ((448 : ℝ) * ((r : ℝ) + 50) ^ 2) ^ r ≤ Real.exp L := by
    calc
      ((448 : ℝ) * ((r : ℝ) + 50) ^ 2) ^ r ≤
          (L ^ 3) ^ r := by gcongr
      _ = Real.exp (Real.log ((L ^ 3) ^ r)) :=
          (Real.exp_log (pow_pos (pow_pos hLpos 3) r)).symm
      _ = Real.exp ((r : ℝ) * (3 * Real.log L)) := by
        rw [Real.log_pow, Real.log_pow]
        ring
      _ ≤ Real.exp L := by
        apply Real.exp_le_exp.mpr
        have hnonneg : 0 ≤ (r : ℝ) * Real.log L :=
          mul_nonneg (Nat.cast_nonneg _) (by linarith)
        nlinarith [hrmul]
  have hcast :
      (((448 * (r + 50) ^ 2 : ℕ) : ℝ)) =
        (448 : ℝ) * ((r : ℝ) + 50) ^ 2 := by
    norm_num [Nat.cast_mul, Nat.cast_pow]
  simpa only [hcast] using hexp

/-- The explicit logarithmic depth always fits the finite integer
sieve budget when the ratio N/(deletions+1) is sufficiently large. -/
theorem quantitative_log_choice_budget_fast
    (E : Set ℕ) (N : ℕ) (hN : 0 < N)
    (hQ : 2048 ≤ Real.log ((N : ℝ) / (countUpTo E N + 1))) :
    let L := Real.log ((N : ℝ) / (countUpTo E N + 1))
    let r := ⌊L / (3 * Real.log L)⌋₊
    (448 * (r + 50) ^ 2) ^ r * (countUpTo E N + 1) ≤ N := by
  dsimp
  let d : ℕ := countUpTo E N + 1
  let Q : ℝ := (N : ℝ) / (d : ℝ)
  let L : ℝ := Real.log Q
  let r : ℕ := ⌊L / (3 * Real.log L)⌋₊
  have hd : 0 < d := by omega
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hnp : (0 : ℝ) < N := by exact_mod_cast hN
  have hQpos : 0 < Q := div_pos hnp hdp
  have hL : 2048 ≤ L := by
    dsimp [L, Q, d]
    simpa only [Nat.cast_add, Nat.cast_one] using hQ
  have hlogpos : 0 < 3 * Real.log L := by
    have hh := half_le_log_of_large_fast L hL
    linarith
  have htpos : 0 ≤ L / (3 * Real.log L) :=
    le_of_lt (div_pos (by linarith) hlogpos)
  have hr : (r : ℝ) ≤ L / (3 * Real.log L) :=
    Nat.floor_le htpos
  have he := budget_exponential_of_floor_bound_fast L hL r hr
  have hQexp : Real.exp L = Q := Real.exp_log hQpos
  rw [hQexp] at he
  have hreal : (((448 * (r + 50) ^ 2) ^ r * d : ℕ) : ℝ) ≤ (N : ℝ) := by
    have hmul := (le_div_iff₀ hdp).mp he
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] using hmul
  exact_mod_cast hreal


private theorem logarithmic_sieve_contraction_fast
    (L : ℝ) (hL : 2048 ≤ L) :
    let r : ℕ := ⌊L / (3 * Real.log L)⌋₊
    2 * ((6 : ℝ) / 7) ^ r ≤
      (7 / 3 : ℝ) * Real.exp
        (-(Real.log ((7 : ℝ) / 6)) * (L / (3 * Real.log L))) := by
  dsimp
  let t : ℝ := L / (3 * Real.log L)
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
theorem quantitative_value_loglog_bound_fast
    (E : Set ℕ) (N : ℕ) (hN : 0 < N)
    (hQ : 2048 ≤ Real.log ((N : ℝ) / (countUpTo E N + 1))) :
    let L := Real.log ((N : ℝ) / (countUpTo E N + 1))
    ((countUpTo (hitSet E) N : ℝ) / (N : ℝ)) ≤
      (7 / 3 : ℝ) * Real.exp
        (-(Real.log ((7 : ℝ) / 6)) * (L / (3 * Real.log L))) := by
  dsimp
  let L : ℝ := Real.log ((N : ℝ) / (countUpTo E N + 1))
  let r : ℕ := ⌊L / (3 * Real.log L)⌋₊
  have hbudget :
      (448 * (r + 50) ^ 2) ^ r * (countUpTo E N + 1) ≤ N := by
    simpa only [r, L] using quantitative_log_choice_budget_fast E N hN hQ
  have hf := quantitative_value_frequency_real E N r hN hbudget
  have hlog : 2 * ((6 : ℝ) / 7) ^ r ≤
      (7 / 3 : ℝ) * Real.exp
        (-(Real.log ((7 : ℝ) / 6)) * (L / (3 * Real.log L))) :=
    logarithmic_sieve_contraction_fast L hQ
  exact hf.trans hlog

/-- Same rate for the index within the retained sequence. The
standard Nth-survivor bound remains an explicit hypothesis. -/
theorem quantitative_index_loglog_bound_fast
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
        (-(Real.log ((7 : ℝ) / 6)) * (L / (3 * Real.log L))) := by
  dsimp
  let L : ℝ := Real.log
    (((2 * N + 2 : ℕ) : ℝ) / (countUpTo E (2 * N + 2) + 1))
  let r : ℕ := ⌊L / (3 * Real.log L)⌋₊
  have hN : 0 < 2 * N + 2 := by omega
  have hbudget :
      (448 * (r + 50) ^ 2) ^ r *
        (countUpTo E (2 * N + 2) + 1) ≤ (2 * N + 2) := by
    simpa only [r, L] using
      quantitative_log_choice_budget_fast E (2 * N + 2) hN hQ
  have hf := quantitative_index_frequency_real E hInf N r hNth hbudget
  have hlog : 2 * ((6 : ℝ) / 7) ^ r ≤
      (7 / 3 : ℝ) * Real.exp
        (-(Real.log ((7 : ℝ) / 6)) * (L / (3 * Real.log L))) :=
    logarithmic_sieve_contraction_fast L hQ
  exact hf.trans hlog


end SparseDeletion
