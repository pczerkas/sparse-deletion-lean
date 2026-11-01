module

public import Mathlib
public import HasseWeil.SparseDeletion.AllFibers

@[expose] public section

/-!
# ZMod specialization of the unconditional Hasse/Weil cubic bound

This is formulated for every prime p >= 37 and every shift b in ZMod p.
It has no character-sum hypothesis. This Lean 4.36 module is independent
of the original Lean 4.35 code and must be separately certified.
-/

namespace SparseDeletion.AINTLIBBridge

attribute [local instance] Classical.propDecidable

/-- The unconditional upper character-sum bound for our original
triangular-square cubic modulo every prime p ≥ 37. -/
theorem triangular_character_upper_zmod
    (p : ℕ) [Fact p.Prime] (hp : 37 ≤ p) (b : ZMod p) :
    ((∑ x : ZMod p, quadraticCharFun (ZMod p)
      (8 * (x * (x+1) * (2*x+1) / 6 + b) + 1) : ℤ) : ℝ) ≤
        2 * Real.sqrt (p : ℝ) := by
  classical
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
    have hle : p ≤ 2 := Nat.le_of_dvd (by decide) hdiv
    omega
  have hthree : (3 : ZMod p) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hz
    have hle : p ≤ 3 := Nat.le_of_dvd (by decide) hdiv
    omega
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  let W := triangularWeierstrass b
  let A : Type := {xy : ZMod p × ZMod p //
    W.toAffine.Nonsingular xy.1 xy.2}
  let e : W.toAffine.Point ≃ WithZero A := W.toAffine.nonsingularPointEquiv
  letI : Fintype W.toAffine.Point := Fintype.ofEquiv (WithZero A) e.symm
  have h := triangular_original_character_sum_abs_bound_all
    b htwo hthree hchar
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  rw [hcard] at h
  have hle : (∑ x : ZMod p, ((quadraticCharFun (ZMod p)
      (8 * (x * (x+1) * (2*x+1) / 6 + b) + 1) : ℤ) : ℝ)) ≤
        2 * Real.sqrt (p : ℝ) := (le_abs_self _).trans h
  simpa only [Int.cast_sum] using hle

end SparseDeletion.AINTLIBBridge

#print axioms SparseDeletion.AINTLIBBridge.triangular_character_upper_zmod
