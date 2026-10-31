module -- shake: keep-all

public import QuantitativeSieve
public import Mathlib.NumberTheory.Bertrand

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-!
# Explicit elementary modulus growth and finite-N hit bounds

Bertrand's postulate supplies a loose but fully explicit upper bound on
the primes used by the sieve. This eliminates the existential modulus
from the quantitative inequality, without any prime number theorem.
-/

/-- Consecutive sieve primes grow by at most a factor of two. -/
theorem largePrime_succ_le_twice (r : ℕ) :
    largePrime (r + 1) ≤ 2 * largePrime r := by
  have hn : largePrime r ≠ 0 := by
    have hp := largePrime_positive r
    omega
  obtain ⟨p, hp, hgt, htwice⟩ := Nat.bertrand (largePrime r) hn
  have hpred : largePrimePred p := ⟨hp, by
    have h37 := largePrime_ge r
    omega⟩
  have hnext : largePrime (r + 1) ≤ p :=
    (Nat.nth_add_one_le_iff largePrimePred_infinite hpred).2 hgt
  omega

/-- An explicit elementary upper bound for the r-th chosen prime. -/
theorem largePrime_le_exponential (r : ℕ) :
    largePrime r ≤ 37 * 2 ^ r := by
  induction r with
  | zero =>
      have h37 : largePrimePred 37 := ⟨by norm_num, by omega⟩
      have hfirst : largePrime 0 ≤ 37 := by
        change Nat.nth largePrimePred 0 ≤ 37
        rw [Nat.nth_zero]
        exact Nat.sInf_le h37
      simpa using hfirst
  | succ r ih =>
      calc
        largePrime (r + 1) ≤ 2 * largePrime r :=
          largePrime_succ_le_twice r
        _ ≤ 2 * (37 * 2 ^ r) := Nat.mul_le_mul_left 2 ih
        _ = 37 * 2 ^ (r + 1) := by rw [pow_succ]; ring

/-- Explicit modulus bound; deliberately loose to avoid deep prime estimates. -/
theorem largePrime_modulus_le_exponential (r : ℕ) :
    modulusProd largePrime r ≤ 37 ^ r * 2 ^ (r * r) := by
  induction r with
  | zero =>
      simp [modulusProd]
  | succ r ih =>
      calc
        modulusProd largePrime (r + 1) =
            modulusProd largePrime r * largePrime r := rfl
        _ ≤ (37 ^ r * 2 ^ (r * r)) * (37 * 2 ^ r) :=
          Nat.mul_le_mul ih (largePrime_le_exponential r)
        _ = 37 ^ (r + 1) * 2 ^ (r * r + r) := by
          rw [pow_succ, pow_add]
          ring
        _ ≤ 37 ^ (r + 1) * 2 ^ ((r + 1) * (r + 1)) :=
          Nat.mul_le_mul_left _ (pow_le_pow_right₀
            (by decide : (1 : ℕ) ≤ 2) (by nlinarith))

/-- An explicitly identified block modulus, rather than an existential
one. The proof is the same CRT counting step as the generic sieve. -/
theorem quantitative_cubic_sieve_explicit (r u : ℕ) (b : ℤ) :
    7 ^ r * (cubicCandidates u (modulusProd largePrime r) b).card ≤
      6 ^ r * modulusProd largePrime r := by
  classical
  let q := largePrime
  let P := primeSquarePass
  have hq : ∀ k, 0 < q k := largePrime_positive
  have hcop : ∀ k, Nat.Coprime (modulusProd q k) (q k) :=
    largePrime_coprime_previous
  have hper : ∀ k b x, P k b (x % q k) ↔ P k b x :=
    primeSquarePass_periodic
  have hgood : ∀ k b,
      7 * ((Finset.range (q k)).filter (P k b)).card ≤ 6 * q k :=
    quantitative_prime_modular_bound cubicValueLowerBound_proved
  have htri : ∀ k b x,
      TriangularInt (naturalSquareSum x + b) → P k b x :=
    primeSquarePass_of_triangular
  let M := modulusProd q r
  have hbound := crt_sieve_product_count_param 6 7 q P hq hcop hper hgood r b
  have hpass :
      (cubicCandidates u M b).card ≤
       ((Finset.Ico u (u + M)).filter (passesProd P b r)).card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hxi, htriX⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr
      ⟨hxi, passesProd_of_triangular P htri r b x htriX⟩
  have hperiod :
      ((Finset.Ico u (u + M)).filter (passesProd P b r)).card ≤
        ((Finset.range M).filter (passesProd P b r)).card := by
    have h := crt_periodic_intersection_bound M 1 u
      (by simp : Nat.Coprime M 1) (modulusProd_pos q hq r) (by decide)
      (passesProd P b r) (fun _ => True)
      (by
        intro x hx
        exact (passesProd_periodic q P hper r b x).mpr hx)
      (by intro x hx; exact hx)
    simpa only [Nat.mul_one, and_true, Finset.filter_true,
      Finset.card_range, mul_one] using h
  calc
    7 ^ r * (cubicCandidates u M b).card ≤
        7 ^ r * ((Finset.Ico u (u + M)).filter (passesProd P b r)).card :=
      Nat.mul_le_mul_left _ hpass
    _ ≤ 7 ^ r * ((Finset.range M).filter (passesProd P b r)).card :=
      Nat.mul_le_mul_left _ hperiod
    _ ≤ 6 ^ r * M := hbound


/-- An unconditional finite-N bound using only N, the deletion count,
and the chosen sieve depth r. No existential modulus remains. -/
theorem quantitative_value_bound_explicit
    (E : Set ℕ) (r N : ℕ) :
    7 ^ r * countUpTo (hitSet E) N ≤
      6 ^ r * N +
        7 ^ r * (37 ^ r * 2 ^ (r * r)) * (countUpTo E N + 1) := by
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
          7 ^ r * modulusProd largePrime r * (countUpTo E N + 1) := hb
    _ ≤ 6 ^ r * N +
          7 ^ r * (37 ^ r * 2 ^ (r * r)) * (countUpTo E N + 1) := by
      gcongr
      exact largePrime_modulus_le_exponential r

/-- If deletions are sufficiently sparse relative to the explicit
modulus, the number of hits is at most twice the clean CRT term. -/
theorem quantitative_value_bound_under_budget
    (E : Set ℕ) (r N : ℕ)
    (hbudget : 7 ^ r * (37 ^ r * 2 ^ (r * r)) *
        (countUpTo E N + 1) ≤ 6 ^ r * N) :
    7 ^ r * countUpTo (hitSet E) N ≤ 2 * 6 ^ r * N := by
  have hb := quantitative_value_bound_explicit E r N
  calc
    7 ^ r * countUpTo (hitSet E) N ≤
        6 ^ r * N +
          7 ^ r * (37 ^ r * 2 ^ (r * r)) * (countUpTo E N + 1) := hb
    _ ≤ 6 ^ r * N + 6 ^ r * N := Nat.add_le_add_left hbudget _
    _ = 2 * 6 ^ r * N := by ring

end SparseDeletion
