module

public import Mathlib
public import HasseWeil.HasseBound
public import HasseWeil.SparseDeletion.PointCharacterSum
public import HasseWeil.SparseDeletion.CubicModel

@[expose] public section

/-!
# Specialize the exact character-count formula to our triangular cubic

This file uses only the already-certified Hasse point-count API, the
finite fiber identity and the explicit Weierstrass family. It does
not yet transport from the monic cubic to the original x-coordinate.
-/

namespace SparseDeletion.AINTLIBBridge

attribute [local instance] Classical.propDecidable

theorem triangular_model_equation_iff
    {F : Type*} [Field F] (b X Y : F) :
    (triangularWeierstrass b).toAffine.Equation X Y ↔
      Y ^ 2 = X ^ 3 + 4 * X ^ 2 +
        (32 / 9) * X + (64 / 9) * (8 * b + 1) := by
  rw [WeierstrassCurve.Affine.equation_iff']
  change (Y ^ 2 + (0 : F) * X * Y + 0 * Y -
    (X ^ 3 + 4 * X ^ 2 + (32 / 9) * X +
      (64 / 9) * (8 * b + 1)) = 0) ↔ _
  simp only [zero_mul, add_zero, sub_eq_zero]

theorem triangular_pointCount_character_sum
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (b : F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hchar : ringChar F ≠ 2)
    (hq : 15552 * b ^ 2 + 3888 * b + 239 ≠ 0)
    [Fintype (triangularWeierstrass b).toAffine.Point] :
    ((HasseWeil.pointCount (triangularWeierstrass b).toAffine : ℕ) : ℤ) =
      (Fintype.card F : ℤ) + 1 +
        ∑ X : F, quadraticCharFun F
          (X ^ 3 + 4 * X ^ 2 + (32 / 9) * X +
            (64 / 9) * (8 * b + 1)) := by
  letI : (triangularWeierstrass b).toAffine.IsElliptic :=
    triangular_weierstrass_isElliptic b h2 h3 hq
  exact pointCount_eq_field_card_add_character_sum
    (triangularWeierstrass b)
    (fun X : F => X ^ 3 + 4 * X ^ 2 +
      (32 / 9) * X + (64 / 9) * (8 * b + 1))
    hchar (fun X Y => triangular_model_equation_iff b X Y)

end SparseDeletion.AINTLIBBridge

#print axioms SparseDeletion.AINTLIBBridge.triangular_pointCount_character_sum
