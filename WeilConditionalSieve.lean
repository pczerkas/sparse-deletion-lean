module -- shake: keep-all

public import WeilCharacterBridge

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-!
# Conditional Weil refinement, with assumptions visible in every theorem

The two explicitly displayed hypotheses are:
  (1) the cubic quadratic-character sum is at most 2*sqrt(p), and
  (2) the cubic has at most 3 roots.

These are mathematically standard consequences of Weil's theorem
and cubic degree, but they are **not** proved by this module.

All the subsequent modular-CRT and finite hit-count reductions are
verified by Lean and require no new axioms. The main theorem is
unaffected.
-/

/-- Missing finite-field input for the stronger 3/4 local sieve.
No unproven assumption is added as a global axiom. -/
def CubicWeilLocalInput : Prop :=
  ∀ (r : ℕ) (b : ℤ),
    letI : Fact (largePrime r).Prime := ⟨largePrime_prime r⟩
    let f : ZMod (largePrime r) → ZMod (largePrime r) :=
      fun x => (primeCubicPoly (largePrime r)
        (b : ZMod (largePrime r))).eval x
    ((((∑ x : ZMod (largePrime r),
         quadraticCharFun (ZMod (largePrime r)) (f x)) : ℤ) : ℝ) ≤
         2 * Real.sqrt (largePrime r : ℝ)) ∧
      ((Finset.univ : Finset (ZMod (largePrime r))).filter
        (fun x => f x = 0)).card ≤ 3

/-- The local modular inequality, conditional on the precisely
stated Weil character-sum and elementary cubic-root inputs. -/
theorem quantitative_weil_prime_modular_bound
    (hWeil : CubicWeilLocalInput) (r : ℕ) (b : ℤ) :
    4 * ((Finset.range (largePrime r)).filter
      (primeSquarePass r b)).card ≤ 3 * largePrime r := by
  classical
  let p := largePrime r
  letI : Fact p.Prime := ⟨largePrime_prime r⟩
  let f : ZMod p → ZMod p :=
    fun x => (primeCubicPoly p (b : ZMod p)).eval x
  have hp : 37 ≤ p := largePrime_ge r
  have hlocal := hWeil r b
  have hfield : 4 * ((Finset.univ : Finset (ZMod p)).filter
      (fun x => IsSquare (f x))).card ≤ 3 * p :=
    three_quarters_of_character_bound p hp f hlocal.1 hlocal.2
  have hpred (x : ℕ) : primeSquarePass r b x ↔
      IsSquare (f (x : ZMod p)) := by
    unfold primeSquarePass
    rfl
  have heq : ((Finset.range (largePrime r)).filter (primeSquarePass r b)) =
      ((Finset.range p).filter
        (fun x : ℕ => IsSquare (f (x : ZMod p)))) := by
    ext x
    simp only [Finset.mem_filter, hpred]
    rfl
  rw [heq]
  have hc := residue_filter_card_eq_field_count p
    (fun z : ZMod p => IsSquare (f z))
  rw [hc]
  simpa only [ZMod.card, p] using hfield

/-- The same CRT induction now carries the local 3/4 contraction,
without altering the existing original 6/7 sieve proof. -/
theorem quantitative_weil_cubic_sieve
    (hWeil : CubicWeilLocalInput) (r u : ℕ) (b : ℤ) :
    4 ^ r * (cubicCandidates u (modulusProd largePrime r) b).card ≤
      3 ^ r * modulusProd largePrime r := by
  classical
  let q := largePrime
  let P := primeSquarePass
  have hq : ∀ k, 0 < q k := largePrime_positive
  have hcop : ∀ k, Nat.Coprime (modulusProd q k) (q k) :=
    largePrime_coprime_previous
  have hper : ∀ k b x, P k b (x % q k) ↔ P k b x :=
    primeSquarePass_periodic
  have hgood : ∀ k b,
      4 * ((Finset.range (q k)).filter (P k b)).card ≤ 3 * q k :=
    quantitative_weil_prime_modular_bound hWeil
  have htri : ∀ k b x,
      TriangularInt (naturalSquareSum x + b) → P k b x :=
    primeSquarePass_of_triangular
  let M := modulusProd q r
  have hbound := crt_sieve_product_count_param 3 4 q P hq hcop hper hgood r b
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
    4 ^ r * (cubicCandidates u M b).card ≤
        4 ^ r * ((Finset.Ico u (u + M)).filter (passesProd P b r)).card :=
      Nat.mul_le_mul_left _ hpass
    _ ≤ 4 ^ r * ((Finset.range M).filter (passesProd P b r)).card :=
      Nat.mul_le_mul_left _ hperiod
    _ ≤ 3 ^ r * M := hbound

/-- Conditional finite-N inequality with explicit polynomial CRT modulus. -/
theorem quantitative_weil_value_bound
    (hWeil : CubicWeilLocalInput) (E : Set ℕ) (r N : ℕ) :
    4 ^ r * countUpTo (hitSet E) N ≤
      3 ^ r * N +
        4 ^ r * (16 * (r + 50) ^ 2) ^ r *
          (countUpTo E N + 1) := by
  have hM : 0 < modulusProd largePrime r :=
    modulusProd_pos largePrime largePrime_positive r
  have hs : ∀ u b,
      4 ^ r * (cubicCandidates u (modulusProd largePrime r) b).card ≤
        3 ^ r * modulusProd largePrime r := by
    intro u b
    exact quantitative_weil_cubic_sieve hWeil r u b
  have hb := quantitative_value_hit_bound_of_scaled_sieve
    E (3 ^ r) (4 ^ r) (modulusProd largePrime r) N
    hM (pow_pos (by decide : 0 < 4) r) hs
  calc
    4 ^ r * countUpTo (hitSet E) N ≤
        3 ^ r * N +
          4 ^ r * modulusProd largePrime r *
            (countUpTo E N + 1) := hb
    _ ≤ 3 ^ r * N +
          4 ^ r * (16 * (r + 50) ^ 2) ^ r *
            (countUpTo E N + 1) := by
      gcongr
      exact largePrime_modulus_le_polynomial_16 r

/-- Conditional retained-enumeration finite-N inequality. -/
theorem quantitative_weil_index_bound
    (hWeil : CubicWeilLocalInput)
    (E : Set ℕ) (hInf : (Set.ofPred (keptPred E)).Infinite)
    (r N : ℕ) (hNth : keptNth E N < 2 * N + 2) :
    4 ^ r * countUpTo (indexHitSet E) (N + 1) ≤
      3 ^ r * (2 * N + 2) +
        4 ^ r * (16 * (r + 50) ^ 2) ^ r *
          (countUpTo E (2 * N + 2) + 1) := by
  have hM : 0 < modulusProd largePrime r :=
    modulusProd_pos largePrime largePrime_positive r
  have hs : ∀ u b,
      4 ^ r * (cubicCandidates u (modulusProd largePrime r) b).card ≤
        3 ^ r * modulusProd largePrime r := by
    intro u b
    exact quantitative_weil_cubic_sieve hWeil r u b
  have hb := quantitative_index_hit_bound_of_scaled_sieve
    E hInf (3 ^ r) (4 ^ r) (modulusProd largePrime r) N
    hNth hM (pow_pos (by decide : 0 < 4) r) hs
  calc
    4 ^ r * countUpTo (indexHitSet E) (N + 1) ≤
        3 ^ r * (2 * N + 2) +
          4 ^ r * modulusProd largePrime r *
            (countUpTo E (2 * N + 2) + 1) := hb
    _ ≤ 3 ^ r * (2 * N + 2) +
          4 ^ r * (16 * (r + 50) ^ 2) ^ r *
            (countUpTo E (2 * N + 2) + 1) := by
      gcongr
      exact largePrime_modulus_le_polynomial_16 r

end SparseDeletion
