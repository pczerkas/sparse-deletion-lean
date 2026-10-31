module -- shake: keep-all

public import QuantitativeLogRate

@[expose] public section

namespace SparseDeletion

open Real
attribute [local instance] Classical.propDecidable

/-!
# Improved concrete constants via Chebyshev's prime counting lower bound

The same elementary argument as PrimePolynomialBound suffices with the
smaller base 16 instead of 64. This optional result does not change the
existing log-rate proof or the main theorem.
-/

private theorem log_le_two_sqrt_16 (x : ℝ) (hx : 1 ≤ x) :
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

private theorem log_succ_le_three_sqrt_16 (x : ℝ) (hx : 1 ≤ x) :
    Real.log (x + 1) ≤ 3 * Real.sqrt x := by
  have hlog := log_le_two_sqrt_16 (x + 1) (by linarith)
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
theorem primeCounting_quadratic_lower_16 (r : ℕ) :
    r + 38 ≤ Nat.primeCounting (16 * (r + 50) ^ 2) := by
  let n : ℕ := 16 * (r + 50) ^ 2
  have hn : 1 < n := by
    have ht : 0 < r + 50 := by omega
    have hp : 0 < (r + 50) ^ 2 := pow_pos ht 2
    dsimp [n]
    omega
  have hnreal : (n : ℝ) = 16 * ((r : ℝ) + 50) ^ 2 := by
    simp only [n, Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat]
  have hsqrt : Real.sqrt (n : ℝ) = 4 * ((r : ℝ) + 50) := by
    have h : (n : ℝ) = (4 * ((r : ℝ) + 50)) ^ 2 := by
      rw [hnreal]
      ring
    rw [h, Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity
  have hnrealge : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hlog : Real.log (n : ℝ) ≤ 2 * Real.sqrt (n : ℝ) :=
    log_le_two_sqrt_16 n hnrealge
  have hlogsucc : Real.log ((n : ℝ) + 1) ≤ 3 * Real.sqrt (n : ℝ) :=
    log_succ_le_three_sqrt_16 n hnrealge
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


/-- An unconditional polynomial upper bound on our enumerated primes. -/
theorem largePrime_le_quadratic_16 (r : ℕ) :
    largePrime r ≤ 16 * (r + 50) ^ 2 := by
  let n := 16 * (r + 50) ^ 2
  have hcount : r + 38 ≤ Nat.primeCounting n :=
    primeCounting_quadratic_lower_16 r
  have hsubset : Nat.primeCounting n ≤ Nat.count largePrimePred (n + 1) + 37 :=
    primeCounting_le_largePrime_count_add_37 n
  have hlt : r < Nat.count largePrimePred (n + 1) := by omega
  have hnth : largePrime r < n + 1 := by
    change Nat.nth largePrimePred r < n + 1
    exact Nat.nth_lt_of_lt_count hlt
  omega


/-- The CRT modulus grows no faster than a fixed polynomial
in r raised to the r-th power. -/
theorem largePrime_modulus_le_polynomial_16 (r : ℕ) :
    modulusProd largePrime r ≤ (16 * (r + 50) ^ 2) ^ r := by
  induction r with
  | zero => simp [modulusProd]
  | succ r ih =>
      have hbase : 16 * (r + 50) ^ 2 ≤
          16 * (r + 1 + 50) ^ 2 := by
        gcongr
        omega
      have hpow : (16 * (r + 50) ^ 2) ^ r ≤
          (16 * (r + 1 + 50) ^ 2) ^ r := by
        gcongr
      calc
        modulusProd largePrime (r + 1) =
            modulusProd largePrime r * largePrime r := rfl
        _ ≤ (16 * (r + 50) ^ 2) ^ r * (16 * (r + 50) ^ 2) :=
          Nat.mul_le_mul ih (largePrime_le_quadratic_16 r)
        _ ≤ (16 * (r + 1 + 50) ^ 2) ^ r *
              (16 * (r + 1 + 50) ^ 2) :=
          Nat.mul_le_mul hpow hbase
        _ = (16 * (r + 1 + 50) ^ 2) ^ (r + 1) :=
          (pow_succ (16 * (r + 1 + 50) ^ 2) r).symm

/-- Fully explicit finite-N bound with a polynomially growing modulus. -/
theorem quantitative_value_bound_polynomial_16
    (E : Set ℕ) (r N : ℕ) :
    7 ^ r * countUpTo (hitSet E) N ≤
      6 ^ r * N +
        7 ^ r * (16 * (r + 50) ^ 2) ^ r * (countUpTo E N + 1) := by
  have hM : 0 < modulusProd largePrime r :=
    modulusProd_pos largePrime largePrime_positive r
  have hs : ∀ u b,
      7 ^ r * (cubicCandidates u (modulusProd largePrime r) b).card ≤
        6 ^ r * modulusProd largePrime r := by
    intro u b
    exact quantitative_cubic_sieve_explicit r u b
  have hb := quantitative_value_hit_bound_of_scaled_sieve
    E (6 ^ r) (7 ^ r) (modulusProd largePrime r) N
    hM (pow_pos (by decide : 0 < 7) r) hs
  calc
    7 ^ r * countUpTo (hitSet E) N ≤
        6 ^ r * N +
          7 ^ r * modulusProd largePrime r *
            (countUpTo E N + 1) := hb
    _ ≤ 6 ^ r * N +
          7 ^ r * (16 * (r + 50) ^ 2) ^ r *
            (countUpTo E N + 1) := by
      gcongr
      exact largePrime_modulus_le_polynomial_16 r

/-- Polynomial-modulus estimate for retained-sequence indices. -/
theorem quantitative_index_bound_polynomial_16
    (E : Set ℕ) (hInf : (Set.ofPred (keptPred E)).Infinite)
    (r N : ℕ) (hNth : keptNth E N < 2 * N + 2) :
    7 ^ r * countUpTo (indexHitSet E) (N + 1) ≤
      6 ^ r * (2 * N + 2) +
        7 ^ r * (16 * (r + 50) ^ 2) ^ r *
          (countUpTo E (2 * N + 2) + 1) := by
  have hM : 0 < modulusProd largePrime r :=
    modulusProd_pos largePrime largePrime_positive r
  have hs : ∀ u b,
      7 ^ r * (cubicCandidates u (modulusProd largePrime r) b).card ≤
        6 ^ r * modulusProd largePrime r := by
    intro u b
    exact quantitative_cubic_sieve_explicit r u b
  have hb := quantitative_index_hit_bound_of_scaled_sieve
    E hInf (6 ^ r) (7 ^ r) (modulusProd largePrime r) N
    hNth hM (pow_pos (by decide : 0 < 7) r) hs
  calc
    7 ^ r * countUpTo (indexHitSet E) (N + 1) ≤
        6 ^ r * (2 * N + 2) +
          7 ^ r * modulusProd largePrime r *
            (countUpTo E (2 * N + 2) + 1) := hb
    _ ≤ 6 ^ r * (2 * N + 2) +
          7 ^ r * (16 * (r + 50) ^ 2) ^ r *
            (countUpTo E (2 * N + 2) + 1) := by
      gcongr
      exact largePrime_modulus_le_polynomial_16 r


end SparseDeletion
