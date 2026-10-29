import HasseArithmetic
import ResidueCountBridge
import CubicSumBridge

namespace SparseDeletion

open Polynomial

section ConcretePrime

variable (p : ℕ) [Fact p.Prime]

noncomputable def primeCubicPoly (b : ZMod p) : Polynomial (ZMod p) :=
  cubicShape (16 * (6 : ZMod p)⁻¹) (24 * (6 : ZMod p)⁻¹)
    (8 * (6 : ZMod p)⁻¹) (8 * b + 1)

theorem prime_h6 (hp : 37 ≤ p) : (6 : ZMod p) ≠ 0 := by
  intro hz
  have hdvd : p ∣ 6 := (ZMod.natCast_eq_zero_iff 6 p).mp hz
  have hle : p ≤ 6 := Nat.le_of_dvd (by omega) hdvd
  omega

theorem prime_h16 (hp : 37 ≤ p) : (16 : ZMod p) ≠ 0 := by
  intro hz
  have hdvd : p ∣ 16 := (ZMod.natCast_eq_zero_iff 16 p).mp hz
  have hle : p ≤ 16 := Nat.le_of_dvd (by omega) hdvd
  omega

theorem prime_char_not_two (hp : 37 ≤ p) :
    ringChar (ZMod p) ≠ 2 := by
  rw [ringChar.eq (ZMod p) p]
  omega

theorem primeCubicPoly_nonzero (hp : 37 ≤ p) (b : ZMod p) :
    primeCubicPoly p b ≠ 0 := by
  unfold primeCubicPoly
  exact cubicShape_sum_nonzero b (prime_h6 p hp) (prime_h16 p hp)

theorem primeCubicPoly_degree (hp : 37 ≤ p) (b : ZMod p) :
    (primeCubicPoly p b).natDegree = 3 := by
  unfold primeCubicPoly
  apply cubicShape_natDegree
  exact mul_ne_zero (prime_h16 p hp) (inv_ne_zero (prime_h6 p hp))

theorem primeCubicPoly_eval_nat (hp : 37 ≤ p) (b : ZMod p) (x : ℕ) :
    (primeCubicPoly p b).eval (x : ZMod p) =
      8 * ((((naturalSquareSum x : ℤ) : ZMod p)) + b) + 1 := by
  unfold primeCubicPoly
  exact cubicShape_eval_nat x b (prime_h6 p hp)

/-- For the EXACT shifted cubic from the original sum-of-squares problem,
the general Hasse upper character bound gives <= 3/4 passing residues. -/
theorem primeCubic_sieve_of_hasse (hp : 37 ≤ p) (b : ZMod p)
    (hhasse : (quadraticCharSum (fun x => (primeCubicPoly p b).eval x) : ℝ) ≤
      2 * Real.sqrt (p : ℝ)) :
    4 * ((Finset.range p).filter
      (fun x : ℕ => IsSquare ((primeCubicPoly p b).eval (x : ZMod p)))).card ≤
      3 * p := by
  classical
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  have hnumeric := hasse_sqrt_to_quarter p hp
    (quadraticCharSum (fun x => (primeCubicPoly p b).eval x)) hhasse
  have hfield : 4 * ((Finset.univ : Finset (ZMod p)).filter
      (fun x => IsSquare ((primeCubicPoly p b).eval x))).card ≤
      3 * Fintype.card (ZMod p) := by
    apply cubic_square_card_le_three_quarters (prime_char_not_two p hp)
      (primeCubicPoly p b) (primeCubicPoly_nonzero p hp b)
    · rw [primeCubicPoly_degree p hp b]
    · simpa only [hcard] using hnumeric
  rw [residue_filter_card_eq_field_count p
    (fun z : ZMod p => IsSquare ((primeCubicPoly p b).eval z))]
  simpa only [hcard] using hfield

#print axioms primeCubicPoly_nonzero
#print axioms primeCubicPoly_eval_nat
#print axioms primeCubic_sieve_of_hasse

end ConcretePrime
end SparseDeletion
