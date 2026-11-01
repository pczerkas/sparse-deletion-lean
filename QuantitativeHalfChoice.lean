module -- shake: keep-all

public import QuantitativeHalfBudget

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-!
# Stronger effective logarithmic depth: r = floor(L/(2 log L))

With the certified prime modulus (16*(r+50)^2)^r, the exact
finite budget needs base 112 = 7*16. For log Q >= 2048,
L=log Q, this choice guarantees the finite-N budget.
-/

private theorem log_lower_half_choice
    (L : ℝ) (hL : 2048 ≤ L) :
    (15 / 2 : ℝ) ≤ Real.log L := by
  have hlog2 : Real.log (2048 : ℝ) ≤ Real.log L :=
    Real.log_le_log (by norm_num) hL
  have hpow : Real.log (2048 : ℝ) = 11 * Real.log 2 := by
    have heq : (2048 : ℝ) = (2 : ℝ) ^ 11 := by norm_num
    rw [heq, Real.log_pow]
    ring
  have hnum := Real.log_two_gt_d9
  rw [hpow] at hlog2
  linarith

/-- For large L and r ≤ L/(2 log L), the polynomial CRT budget fits
under exp L; no PNT or conjectures are used. -/
private theorem budget_exponential_half_choice
    (L : ℝ) (hL : 2048 ≤ L) (r : ℕ)
    (hr : (r : ℝ) ≤ L / (2 * Real.log L)) :
    (((112 * (r + 50) ^ 2 : ℕ) : ℝ) ^ r) ≤ Real.exp L := by
  have hLpos : 0 < L := by linarith
  have hlog : (15 / 2 : ℝ) ≤ Real.log L :=
    log_lower_half_choice L hL
  have hlogpos : 0 < 2 * Real.log L := by linarith
  have hrmul : (r : ℝ) * (2 * Real.log L) ≤ L :=
    (le_div_iff₀ hlogpos).mp hr
  have hrle : (r : ℝ) ≤ L / 15 := by
    have hnonneg : 0 ≤ (r : ℝ) := Nat.cast_nonneg _
    have hfactor : 0 ≤ 2 * Real.log L - 15 := by linarith
    have hmul := mul_nonneg hnonneg hfactor
    nlinarith
  have hr50 : (r : ℝ) + 50 ≤ (11 / 120 : ℝ) * L := by
    have h50 : (50 : ℝ) ≤ L / 40 := by linarith
    linarith
  have hbase : (112 : ℝ) * ((r : ℝ) + 50) ^ 2 ≤ L ^ 2 := by
    have hsq : ((r : ℝ) + 50) ^ 2 ≤ ((11 / 120 : ℝ) * L) ^ 2 := by
      gcongr
    have hother : (112 : ℝ) * ((11 / 120 : ℝ) * L) ^ 2 ≤ L ^ 2 := by
      nlinarith [sq_nonneg L]
    nlinarith
  have hexp :
      ((112 : ℝ) * ((r : ℝ) + 50) ^ 2) ^ r ≤ Real.exp L := by
    calc
      ((112 : ℝ) * ((r : ℝ) + 50) ^ 2) ^ r ≤
          (L ^ 2) ^ r := by gcongr
      _ = Real.exp (Real.log ((L ^ 2) ^ r)) :=
          (Real.exp_log (pow_pos (pow_pos hLpos 2) r)).symm
      _ = Real.exp ((r : ℝ) * (2 * Real.log L)) := by
        rw [Real.log_pow, Real.log_pow]
        ring
      _ ≤ Real.exp L := by
        apply Real.exp_le_exp.mpr
        have hnonneg : 0 ≤ (r : ℝ) * Real.log L :=
          mul_nonneg (Nat.cast_nonneg _) (by linarith)
        nlinarith [hrmul]
  have hcast :
      (((112 * (r + 50) ^ 2 : ℕ) : ℝ)) =
        (112 : ℝ) * ((r : ℝ) + 50) ^ 2 := by
    norm_num [Nat.cast_mul, Nat.cast_pow]
  simpa only [hcast] using hexp

/-- The explicit logarithmic depth always fits the finite integer
sieve budget when the ratio N/(deletions+1) is sufficiently large. -/
theorem quantitative_half_log_choice_budget
    (E : Set ℕ) (N : ℕ) (hN : 0 < N)
    (hQ : 2048 ≤ Real.log ((N : ℝ) / (countUpTo E N + 1))) :
    let L := Real.log ((N : ℝ) / (countUpTo E N + 1))
    let r := ⌊L / (2 * Real.log L)⌋₊
    (112 * (r + 50) ^ 2) ^ r * (countUpTo E N + 1) ≤ N := by
  dsimp
  let d : ℕ := countUpTo E N + 1
  let Q : ℝ := (N : ℝ) / (d : ℝ)
  let L : ℝ := Real.log Q
  let r : ℕ := ⌊L / (2 * Real.log L)⌋₊
  have hd : 0 < d := by omega
  have hdp : (0 : ℝ) < d := by exact_mod_cast hd
  have hnp : (0 : ℝ) < N := by exact_mod_cast hN
  have hQpos : 0 < Q := div_pos hnp hdp
  have hL : 2048 ≤ L := by
    dsimp [L, Q, d]
    simpa only [Nat.cast_add, Nat.cast_one] using hQ
  have hlogpos : 0 < 2 * Real.log L := by
    have hh := log_lower_half_choice L hL
    linarith
  have htpos : 0 ≤ L / (2 * Real.log L) :=
    le_of_lt (div_pos (by linarith) hlogpos)
  have hr : (r : ℝ) ≤ L / (2 * Real.log L) :=
    Nat.floor_le htpos
  have he := budget_exponential_half_choice L hL r hr
  have hQexp : Real.exp L = Q := Real.exp_log hQpos
  rw [hQexp] at he
  have hreal : (((112 * (r + 50) ^ 2) ^ r * d : ℕ) : ℝ) ≤ (N : ℝ) := by
    have hmul := (le_div_iff₀ hdp).mp he
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] using hmul
  exact_mod_cast hreal


end SparseDeletion
