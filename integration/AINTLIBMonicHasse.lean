module

public import Mathlib
public import HasseWeil.HasseBound
public import HasseWeil.SparseDeletion.CubicCharacter

@[expose] public section

/-!
# Unconditional Hasse bound for the *monic* triangular cubic

This module depends on the actual AINTLIB Hasse theorem and the
already separate point-count-to-character-sum identity. It establishes
the unconditional upper bound for the monic cubic when its
discriminant is nonzero. The original triangular-prefix cubic uses
a nontrivial linear rescaling, which is a later separate lemma.
-/

namespace SparseDeletion.AINTLIBBridge

attribute [local instance] Classical.propDecidable

theorem triangular_monic_character_sum_abs_bound
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (b : F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hchar : ringChar F ≠ 2)
    (hq : 15552 * b ^ 2 + 3888 * b + 239 ≠ 0)
    [Fintype (triangularWeierstrass b).toAffine.Point] :
    |(∑ X : F, ((quadraticCharFun F
      (X ^ 3 + 4 * X ^ 2 + (32 / 9) * X +
        (64 / 9) * (8 * b + 1)) : ℤ) : ℝ))| ≤
        2 * Real.sqrt (Fintype.card F : ℝ) := by
  letI : (triangularWeierstrass b).toAffine.IsElliptic :=
    triangular_weierstrass_isElliptic b h2 h3 hq
  have hcount := triangular_pointCount_character_sum
    b h2 h3 hchar hq
  have hcountR :
      (HasseWeil.pointCount (triangularWeierstrass b).toAffine : ℝ) =
        (Fintype.card F : ℝ) + 1 +
        ∑ X : F, ((quadraticCharFun F
          (X ^ 3 + 4 * X ^ 2 + (32 / 9) * X +
            (64 / 9) * (8 * b + 1)) : ℤ) : ℝ) := by
    exact_mod_cast hcount
  have hHasse := triangular_weierstrass_hasse_bound b h2 h3 hq
  rw [hcountR] at hHasse
  have hcancel :
      (Fintype.card F : ℝ) + 1 +
          (∑ X : F, ((quadraticCharFun F
            (X ^ 3 + 4 * X ^ 2 + (32 / 9) * X +
              (64 / 9) * (8 * b + 1)) : ℤ) : ℝ)) -
          (Fintype.card F : ℝ) - 1 =
        (∑ X : F, ((quadraticCharFun F
          (X ^ 3 + 4 * X ^ 2 + (32 / 9) * X +
            (64 / 9) * (8 * b + 1)) : ℤ) : ℝ)) := by ring
  simpa only [hcancel] using hHasse

end SparseDeletion.AINTLIBBridge

#print axioms SparseDeletion.AINTLIBBridge.triangular_monic_character_sum_abs_bound
