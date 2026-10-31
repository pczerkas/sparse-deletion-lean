module -- shake: keep-all

public import PrimePolynomialBound

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-!
# Fully explicit polynomial-modulus finite-N estimates

This optional module relies on the elementary Chebyshev lower
bound for the prime-counting function, not the prime number theorem.
-/

/-- The CRT modulus grows no faster than a fixed polynomial
in r raised to the r-th power. -/
theorem largePrime_modulus_le_polynomial (r : ℕ) :
    modulusProd largePrime r ≤ (64 * (r + 50) ^ 2) ^ r := by
  induction r with
  | zero => simp [modulusProd]
  | succ r ih =>
      have hbase : 64 * (r + 50) ^ 2 ≤
          64 * (r + 1 + 50) ^ 2 := by
        gcongr
        omega
      have hpow : (64 * (r + 50) ^ 2) ^ r ≤
          (64 * (r + 1 + 50) ^ 2) ^ r := by
        gcongr
      calc
        modulusProd largePrime (r + 1) =
            modulusProd largePrime r * largePrime r := rfl
        _ ≤ (64 * (r + 50) ^ 2) ^ r * (64 * (r + 50) ^ 2) :=
          Nat.mul_le_mul ih (largePrime_le_quadratic r)
        _ ≤ (64 * (r + 1 + 50) ^ 2) ^ r *
              (64 * (r + 1 + 50) ^ 2) :=
          Nat.mul_le_mul hpow hbase
        _ = (64 * (r + 1 + 50) ^ 2) ^ (r + 1) :=
          (pow_succ (64 * (r + 1 + 50) ^ 2) r).symm

/-- Fully explicit finite-N bound with a polynomially growing modulus. -/
theorem quantitative_value_bound_polynomial
    (E : Set ℕ) (r N : ℕ) :
    7 ^ r * countUpTo (hitSet E) N ≤
      6 ^ r * N +
        7 ^ r * (64 * (r + 50) ^ 2) ^ r * (countUpTo E N + 1) := by
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
          7 ^ r * (64 * (r + 50) ^ 2) ^ r *
            (countUpTo E N + 1) := by
      gcongr
      exact largePrime_modulus_le_polynomial r

/-- Polynomial-modulus estimate for retained-sequence indices. -/
theorem quantitative_index_bound_polynomial
    (E : Set ℕ) (hInf : (Set.ofPred (keptPred E)).Infinite)
    (r N : ℕ) (hNth : keptNth E N < 2 * N + 2) :
    7 ^ r * countUpTo (indexHitSet E) (N + 1) ≤
      6 ^ r * (2 * N + 2) +
        7 ^ r * (64 * (r + 50) ^ 2) ^ r *
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
          7 ^ r * (64 * (r + 50) ^ 2) ^ r *
            (countUpTo E (2 * N + 2) + 1) := by
      gcongr
      exact largePrime_modulus_le_polynomial r

end SparseDeletion
