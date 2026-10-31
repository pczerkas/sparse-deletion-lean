module -- shake: keep-all

public import QuantitativeBound
public import MainUnconditionalValueSet

@[expose] public section

namespace SparseDeletion

open Finset Polynomial
attribute [local instance] Classical.propDecidable

/-!
# Concrete finite-N CRT sieve bounds

This is an *optional* quantitative specialization of the existing
modular proof. The prime bound below restates the same finite-field
argument already used by MainExactValueReduction, avoiding any change
to the original main theorem's source or import graph.
-/

/-- The modular 6/7 contraction for each large prime, uniform in b.
This reuses the original unconditional cubic value-set certificate. -/
theorem quantitative_prime_modular_bound
    (hvalue : CubicValueLowerBound) (r : ℕ) (b : ℤ) :
    7 * ((Finset.range (largePrime r)).filter (primeSquarePass r b)).card ≤
      6 * largePrime r := by
  classical
  intro r b
  let _ := Fact.mk (largePrime_prime r)
  let p := largePrime r
  have hp : 37 ≤ p := largePrime_ge r
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hle : p ≤ 2 := Nat.le_of_dvd (by omega) hdvd
    omega
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro hz
    have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hz
    have hle : p ≤ 3 := Nat.le_of_dvd (by omega) hdvd
    omega
  have himage : 2 * Fintype.card (ZMod p) ≤
      3 * ((Finset.univ : Finset (ZMod p)).image
        (fun z : ZMod p => (primeCubicPoly p (b : ZMod p)).eval z)).card + 1 := by
    have hcard :
        ((Finset.univ : Finset (ZMod p)).image
          (fun z : ZMod p => (primeCubicPoly p (b : ZMod p)).eval z)).card =
        ((Finset.univ : Finset (ZMod p)).image
          (fun t : ZMod p => t ^ 3 - t)).card := by
      exact cubicShape_image_card_eq_xcube_sub_x (b : ZMod p) h2 h3
    rw [hcard, ZMod.card]
    exact hvalue r
  have hsquares :
      2 * ((Finset.univ : Finset (ZMod p)).filter IsSquare).card ≤
        Fintype.card (ZMod p) + 1 :=
    (card_square_values_exact (prime_char_not_two p hp)).le
  have hfield : 7 * ((Finset.univ : Finset (ZMod p)).filter
      (fun z => IsSquare ((primeCubicPoly p (b : ZMod p)).eval z))).card ≤
      6 * Fintype.card (ZMod p) :=
    six_sevenths_of_cubic_image_bound
      (fun z : ZMod p => (primeCubicPoly p (b : ZMod p)).eval z)
      (by simpa only [ZMod.card] using (show 35 ≤ p by omega)) himage hsquares
  have hpred (x : ℕ) : primeSquarePass r b x ↔
      IsSquare ((primeCubicPoly p (b : ZMod p)).eval (x : ZMod p)) := by
    unfold primeSquarePass
    rfl
  have heq : ((Finset.range (largePrime r)).filter (primeSquarePass r b)) =
      ((Finset.range p).filter
        (fun x : ℕ => IsSquare ((primeCubicPoly p (b : ZMod p)).eval (x : ZMod p)))) := by
    ext x
    simp only [Finset.mem_filter, hpred]
    rfl
  rw [heq]
  have hc := residue_filter_card_eq_field_count p
    (fun z : ZMod p => IsSquare ((primeCubicPoly p (b : ZMod p)).eval z))
  rw [hc]
  simpa only [ZMod.card, p] using hfield

/-- The same infinite prime family as the main proof supplies
finite periodic CRT bounds for every number of modular tests. -/
theorem quantitative_cubic_sieve_family (r : ℕ) :
    ∃ M : ℕ, 0 < M ∧
      ∀ (u : ℕ) (b : ℤ),
        7 ^ r * (cubicCandidates u M b).card ≤ 6 ^ r * M := by
  apply uniformCubicSieve_of_modular_family_param 6 7
    largePrime primeSquarePass largePrime_positive largePrime_coprime_previous
  · intro k b x
    exact primeSquarePass_periodic k b x
  · intro k b
    exact quantitative_prime_modular_bound cubicValueLowerBound_proved k b
  · intro k b x ht
    exact primeSquarePass_of_triangular k b x ht

/-- Unconditional finite-N upper bound in terms of the exact number of
deleted integers and an explicit CRT sieve depth r. No assumption d(E)=0. -/
theorem quantitative_value_bound_unconditional
    (E : Set ℕ) (r N : ℕ) :
    ∃ M : ℕ, 0 < M ∧
      7 ^ r * countUpTo (hitSet E) N ≤
        6 ^ r * N +
          7 ^ r * M * (countUpTo E N + 1) := by
  exact quantitative_value_hit_bound_of_sieve_family
    E 6 7 (by decide) quantitative_cubic_sieve_family r N

/-- The matching concrete bound for retained-sequence indices; the
index-to-value inequality is explicit and is eventually true for d(E)=0. -/
theorem quantitative_index_bound_unconditional
    (E : Set ℕ) (hInf : (Set.ofPred (keptPred E)).Infinite)
    (N r : ℕ) (hNth : keptNth E N < 2 * N + 2) :
    ∃ M : ℕ, 0 < M ∧
      7 ^ r * countUpTo (indexHitSet E) (N + 1) ≤
        6 ^ r * (2 * N + 2) +
          7 ^ r * M * (countUpTo E (2 * N + 2) + 1) := by
  obtain ⟨M, hM, hsieve⟩ := quantitative_cubic_sieve_family r
  exact ⟨M, hM,
    quantitative_index_hit_bound_of_scaled_sieve
      E hInf (6 ^ r) (7 ^ r) M N hNth hM
      (pow_pos (by decide : 0 < 7) r) hsieve⟩

end SparseDeletion
