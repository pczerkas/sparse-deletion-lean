module -- shake: keep-all

public import CubicSumBridge

@[expose] public section

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

theorem prime_char_not_two (hp : 37 ≤ p) :
    ringChar (ZMod p) ≠ 2 := by
  rw [ringChar.eq (ZMod p) p]
  omega

theorem primeCubicPoly_eval_nat (hp : 37 ≤ p) (b : ZMod p) (x : ℕ) :
    (primeCubicPoly p b).eval (x : ZMod p) =
      8 * ((((naturalSquareSum x : ℤ) : ZMod p)) + b) + 1 := by
  unfold primeCubicPoly
  exact cubicShape_eval_nat x b (prime_h6 p hp)

end ConcretePrime
end SparseDeletion
