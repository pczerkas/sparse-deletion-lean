module

public import Mathlib
public import HasseWeil.SparseDeletion.ZModWeil

@[expose] public section

/-!
# Exact polynomial interface matching PrimeCubicPoly.lean

The original Lean 4.35 project defines primeCubicPoly as
cubicShape (16 * (6:ZMod p)⁻¹) (24 * 6⁻¹) (8 * 6⁻¹) (8*b+1).
We reproduce precisely that coefficient-level expression here
in the AINTLIB Lean 4.36 workspace and prove the character bound
for its evaluation at every prime p ≥ 37.

This file does not import 4.35 .olean files.
-/

namespace SparseDeletion.AINTLIBBridge

open Polynomial
attribute [local instance] Classical.propDecidable

noncomputable def matchingPrimeCubicPoly
    (p : ℕ) [Fact p.Prime] (b : ZMod p) : Polynomial (ZMod p) :=
  C (16 * (6 : ZMod p)⁻¹) * X ^ 3 +
    C (24 * (6 : ZMod p)⁻¹) * X ^ 2 +
    C (8 * (6 : ZMod p)⁻¹) * X +
    C (8 * b + 1)

theorem matchingPrimeCubicPoly_eval
    (p : ℕ) [Fact p.Prime] (hp : 37 ≤ p)
    (b x : ZMod p) :
    (matchingPrimeCubicPoly p b).eval x =
      8 * (x * (x+1) * (2*x+1) / 6 + b) + 1 := by
  have h6 : (6 : ZMod p) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 6 := (ZMod.natCast_eq_zero_iff 6 p).mp hz
    have hle : p ≤ 6 := Nat.le_of_dvd (by decide) hdiv
    omega
  simp only [matchingPrimeCubicPoly, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_pow]
  field_simp [h6]
  ring

/-- Same statement as CubicWeilCharacterUpper's inner inequality,
but elaborated in AINTLIB's separate Lean 4.36 workspace. -/
theorem matchingPrimeCubicPoly_character_upper
    (p : ℕ) [Fact p.Prime] (hp : 37 ≤ p) (b : ZMod p) :
    (((∑ x : ZMod p,
      quadraticCharFun (ZMod p)
        ((matchingPrimeCubicPoly p b).eval x)) : ℤ) : ℝ) ≤
        2 * Real.sqrt (p : ℝ) := by
  have hsum :
      (∑ x : ZMod p,
        quadraticCharFun (ZMod p)
          ((matchingPrimeCubicPoly p b).eval x)) =
      ∑ x : ZMod p,
        quadraticCharFun (ZMod p)
          (8 * (x * (x+1) * (2*x+1) / 6 + b) + 1) := by
    apply Finset.sum_congr rfl
    intro x _
    rw [matchingPrimeCubicPoly_eval p hp b x]
  rw [hsum]
  exact triangular_character_upper_zmod p hp b

end SparseDeletion.AINTLIBBridge

#print axioms SparseDeletion.AINTLIBBridge.matchingPrimeCubicPoly_eval
#print axioms SparseDeletion.AINTLIBBridge.matchingPrimeCubicPoly_character_upper
