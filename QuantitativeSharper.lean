module -- shake: keep-all

public import QuantitativeEffective
public import Mathlib.Algebra.BigOperators.Intervals

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-!
# Sharper elementary CRT modulus estimate

The bound from Bertrand used in `QuantitativeEffective` was
`37^r * 2^(r*r)`. Retaining the exponents of the individual primes
before multiplying gives the significantly tighter and still completely
elementary bound `37^r * 2^(r*(r-1)/2)`.
No prime number theorem, Hasse estimate or numerical testing is needed.
-/

/-- Multiply the individual Bertrand upper bounds without replacing
every exponent by the largest one. -/
theorem largePrime_modulus_le_sum_exponent (r : ℕ) :
    modulusProd largePrime r ≤
      37 ^ r * 2 ^ (∑ i ∈ Finset.range r, i) := by
  induction r with
  | zero =>
      simp [modulusProd]
  | succ r ih =>
      calc
        modulusProd largePrime (r + 1) =
            modulusProd largePrime r * largePrime r := rfl
        _ ≤ (37 ^ r * 2 ^ (∑ i ∈ Finset.range r, i)) *
              (37 * 2 ^ r) :=
          Nat.mul_le_mul ih (largePrime_le_exponential r)
        _ = 37 ^ (r + 1) *
              2 ^ (∑ i ∈ Finset.range (r + 1), i) := by
          rw [Finset.sum_range_succ, pow_succ, pow_add]
          ring

/-- The exponent is a triangular number. -/
theorem largePrime_modulus_le_half_square (r : ℕ) :
    modulusProd largePrime r ≤
      37 ^ r * 2 ^ (r * (r - 1) / 2) := by
  simpa only [Finset.sum_range_id] using
    largePrime_modulus_le_sum_exponent r

/-- The finite bound with the sharper explicitly known modulus. -/
theorem quantitative_value_bound_sharper
    (E : Set ℕ) (r N : ℕ) :
    7 ^ r * countUpTo (hitSet E) N ≤
      6 ^ r * N +
        7 ^ r * (37 ^ r * 2 ^ (r * (r - 1) / 2)) *
          (countUpTo E N + 1) := by
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
          7 ^ r * (37 ^ r * 2 ^ (r * (r - 1) / 2)) *
            (countUpTo E N + 1) := by
      gcongr
      exact largePrime_modulus_le_half_square r

/-- An analogous sharpened bound for retained-index triangular hits. -/
theorem quantitative_index_bound_sharper
    (E : Set ℕ) (hInf : (Set.ofPred (keptPred E)).Infinite)
    (r N : ℕ) (hNth : keptNth E N < 2 * N + 2) :
    7 ^ r * countUpTo (indexHitSet E) (N + 1) ≤
      6 ^ r * (2 * N + 2) +
        7 ^ r * (37 ^ r * 2 ^ (r * (r - 1) / 2)) *
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
          7 ^ r * (37 ^ r * 2 ^ (r * (r - 1) / 2)) *
            (countUpTo E (2 * N + 2) + 1) := by
      gcongr
      exact largePrime_modulus_le_half_square r

end SparseDeletion
