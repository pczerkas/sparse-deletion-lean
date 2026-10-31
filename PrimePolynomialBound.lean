module -- shake: keep-all

public import QuantitativeSharper
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

namespace SparseDeletion

open Real
attribute [local instance] Classical.propDecidable

/-!
# Polynomial growth of the prime family from Chebyshev's elementary lower bound

This is an optional analytical strengthening of the purely Bertrand-based
bound. We use Chebyshev.pi_ge from Mathlib and simple logarithm estimates,
not the prime number theorem.
-/

private theorem log_le_two_sqrt (x : ℝ) (hx : 1 ≤ x) :
    Real.log x ≤ 2 * Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.2 (by linarith)
  have hlog : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 :=
    Real.log_le_sub_one_of_pos hs
  have he : Real.log x = 2 * Real.log (Real.sqrt x) := by
    calc
      Real.log x = Real.log ((Real.sqrt x) ^ 2) := by
        rw [Real.sq_sqrt hx0]
      _ = 2 * Real.log (Real.sqrt x) := by rw [Real.log_pow]; ring
  linarith

private theorem log_succ_le_three_sqrt (x : ℝ) (hx : 1 ≤ x) :
    Real.log (x + 1) ≤ 3 * Real.sqrt x := by
  have hlog := log_le_two_sqrt (x + 1) (by linarith)
  have h0 : 0 ≤ x := by linarith
  have h1 : 0 ≤ x + 1 := by linarith
  have hxrt : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hyrt : 0 ≤ Real.sqrt (x + 1) := Real.sqrt_nonneg (x + 1)
  have hsx : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt h0
  have hsy : (Real.sqrt (x + 1)) ^ 2 = x + 1 := Real.sq_sqrt h1
  have hb : 2 * Real.sqrt (x + 1) ≤ 3 * Real.sqrt x := by
    nlinarith
  linarith

/-- An explicit, deliberately generous lower bound for prime counting.
The constant is chosen so the proof uses only Chebyshev and elementary
logarithm estimates. -/
theorem primeCounting_quadratic_lower (r : ℕ) :
    r + 38 ≤ Nat.primeCounting (64 * (r + 50) ^ 2) := by
  let n : ℕ := 64 * (r + 50) ^ 2
  have hn : 1 < n := by
    have ht : 0 < r + 50 := by omega
    have hp : 0 < (r + 50) ^ 2 := pow_pos ht 2
    dsimp [n]
    omega
  have hnreal : (n : ℝ) = 64 * ((r : ℝ) + 50) ^ 2 := by
    simp only [n, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
  have hsqrt : Real.sqrt (n : ℝ) = 8 * ((r : ℝ) + 50) := by
    have h : (n : ℝ) = (8 * ((r : ℝ) + 50)) ^ 2 := by
      rw [hnreal]
      ring
    rw [h, Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity
  have hnrealge : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) :=
    log_le_two_sqrt n hnrealge
  have hlogsucc : Real.log ((n : ℝ) + 1) ≤ 3 * Real.sqrt (n : ℝ) :=
    log_succ_le_three_sqrt n hnrealge
  have htwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    linarith [Real.log_two_gt_d9]
  have hmain :
      ((r : ℝ) + 38) * Real.log (n : ℝ) ≤
        (n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1) := by
    have ht : 0 ≤ ((r : ℝ) + 38) := by positivity
    have ha :
        ((r : ℝ) + 38) * Real.log (n : ℝ) ≤
          ((r : ℝ) + 38) * (2 * Real.sqrt (n : ℝ)) :=
      mul_le_mul_of_nonneg_left hlog ht
    have hb : (n : ℝ) / 2 - 3 * Real.sqrt (n : ℝ) ≤
        (n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1) := by
      have hnonneg : (0 : ℝ) ≤ n := by exact_mod_cast (Nat.zero_le n)
      nlinarith [mul_nonneg hnonneg (sub_nonneg.mpr htwo)]
    calc
      ((r : ℝ) + 38) * Real.log (n : ℝ) ≤
        ((r : ℝ) + 38) * (2 * Real.sqrt (n : ℝ)) := ha
      _ ≤ (n : ℝ) / 2 - 3 * Real.sqrt (n : ℝ) := by
        rw [hsqrt, hnreal]
        nlinarith [sq_nonneg (r : ℝ)]
      _ ≤ (n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1) := hb
  have hlogpos : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast hn)
  have hcheb := Chebyshev.pi_ge n
  have hfrac : ((r : ℝ) + 38) ≤
        ((n : ℝ) * Real.log 2 - Real.log ((n : ℝ) + 1)) /
          Real.log (n : ℝ) :=
    (le_div_iff₀ hlogpos).2 hmain
  have hpi : ((r : ℝ) + 38) ≤ (Nat.primeCounting n : ℝ) :=
    hfrac.trans hcheb
  exact_mod_cast hpi

/-- Every prime ≤ n is either in the ≥37 prime family or among the
37 smaller natural numbers. The latter are bounded very crudely. -/
theorem primeCounting_le_largePrime_count_add_37 (n : ℕ) :
    Nat.primeCounting n ≤ Nat.count largePrimePred (n + 1) + 37 := by
  classical
  let all : Finset ℕ := (Finset.range (n + 1)).filter Nat.Prime
  let large : Finset ℕ := (Finset.range (n + 1)).filter largePrimePred
  have hsub : all ⊆ large ∪ Finset.range 37 := by
    intro p hp
    simp only [all, Finset.mem_filter, Finset.mem_range] at hp
    by_cases h37 : 37 ≤ p
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hp.1, hp.2, h37⟩
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_range.mpr (by omega)
  have hc : all.card ≤ large.card + 37 := by
    calc
      all.card ≤ (large ∪ Finset.range 37).card := Finset.card_le_card hsub
      _ ≤ large.card + (Finset.range 37).card := Finset.card_union_le _ _
      _ = large.card + 37 := by simp
  have hall : all.card = Nat.primeCounting n := by
    simpa [all, Nat.primesLE_eq_filter_range] using
      (Nat.primesLE_card_eq_primeCounting n)
  have hlarge : large.card = Nat.count largePrimePred (n + 1) := by
    simp only [large, Nat.count_eq_card_filter_range]
  omega

/-- An unconditional polynomial upper bound on our enumerated primes. -/
theorem largePrime_le_quadratic (r : ℕ) :
    largePrime r ≤ 64 * (r + 50) ^ 2 := by
  let n := 64 * (r + 50) ^ 2
  have hcount : r + 38 ≤ Nat.primeCounting n :=
    primeCounting_quadratic_lower r
  have hsubset : Nat.primeCounting n ≤ Nat.count largePrimePred (n + 1) + 37 :=
    primeCounting_le_largePrime_count_add_37 n
  have hlt : r < Nat.count largePrimePred (n + 1) := by omega
  have hnth : largePrime r < n + 1 := by
    change Nat.nth largePrimePred r < n + 1
    exact Nat.nth_lt_of_lt_count hlt
  omega

end SparseDeletion
