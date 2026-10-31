module -- shake: keep-all

public import QuantitativeReal

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-!
# Explicit logarithmic choice of the CRT sieve depth

The finite hit bound is already verified in QuantitativeReal.
Here we use a deliberately large numerical threshold (log Q ≥ 2048)
to formalize the first missing real-analysis step: the explicit
integer budget for r = floor(log Q / (8 log log Q)).
-/

/-- Elementary logarithmic estimate used to control the sieve depth. -/
private theorem half_le_log_of_large
    (L : ℝ) (hL : 2048 ≤ L) :
    (1 / 2 : ℝ) ≤ Real.log L := by
  have hlog2 : Real.log 2 ≤ Real.log L :=
    Real.log_le_log (by norm_num) (by linarith)
  have hnum := Real.log_two_gt_d9
  linarith

/-- For large L and r ≤ L/(8 log L), the polynomial CRT budget fits
under exp L; no PNT or conjectures are used. -/
private theorem budget_exponential_of_floor_bound
    (L : ℝ) (hL : 2048 ≤ L) (r : ℕ)
    (hr : (r : ℝ) ≤ L / (8 * Real.log L)) :
    (((448 * (r + 50) ^ 2 : ℕ) : ℝ) ^ r) ≤ Real.exp L := by
  have hLpos : 0 < L := by linarith
  have hlog : (1 / 2 : ℝ) ≤ Real.log L :=
    half_le_log_of_large L hL
  have hlogpos : 0 < 8 * Real.log L := by linarith
  have hrmul : (r : ℝ) * (8 * Real.log L) ≤ L :=
    (le_div_iff₀ hlogpos).mp hr
  have hrle : (r : ℝ) ≤ L := by
    have hnonneg : (0 : ℝ) ≤ r := Nat.cast_nonneg _
    have hfactor : 0 ≤ 8 * Real.log L - 1 := by linarith
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
theorem quantitative_log_choice_budget
    (E : Set ℕ) (N : ℕ) (hN : 0 < N)
    (hQ : 2048 ≤ Real.log ((N : ℝ) / (countUpTo E N + 1))) :
    let L := Real.log ((N : ℝ) / (countUpTo E N + 1))
    let r := ⌊L / (8 * Real.log L)⌋₊
    (448 * (r + 50) ^ 2) ^ r * (countUpTo E N + 1) ≤ N := by
  dsimp
  let d : ℕ := countUpTo E N + 1
  let Q : ℝ := (N : ℝ) / (d : ℝ)
  let L : ℝ := Real.log Q
  let r : ℕ := ⌊L / (8 * Real.log L)⌋₊
  have hd : 0 < d := by omega
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hnp : (0 : ℝ) < N := by exact_mod_cast hN
  have hQpos : 0 < Q := div_pos hnp hdp
  have hL : 2048 ≤ L := hQ
  have hlogpos : 0 < 8 * Real.log L := by
    have hh := half_le_log_of_large L hL
    linarith
  have htpos : 0 ≤ L / (8 * Real.log L) :=
    le_of_lt (div_pos (by linarith) hlogpos)
  have hr : (r : ℝ) ≤ L / (8 * Real.log L) :=
    Nat.floor_le htpos
  have he := budget_exponential_of_floor_bound L hL r hr
  have hQexp : Real.exp L = Q := Real.exp_log hQpos
  rw [hQexp] at he
  have hreal : (((448 * (r + 50) ^ 2) ^ r * d : ℕ) : ℝ) ≤ (N : ℝ) := by
    have hmul := (le_div_iff₀ hdp).mp he
    push_cast
    simpa only [Nat.cast_mul, Nat.cast_pow] using hmul
  exact_mod_cast hreal

end SparseDeletion
