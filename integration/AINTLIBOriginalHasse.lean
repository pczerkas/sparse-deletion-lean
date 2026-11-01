module

public import Mathlib
public import HasseWeil.SparseDeletion.MonicHasse
public import HasseWeil.SparseDeletion.RescaleCharacter

@[expose] public section

/-!
# Hasse-bound character sum for the original triangular-square cubic

Combines the certified Hasse bound for the monic Weierstrass model
with the finite-field character-sum invariance under X=(8/3)*x.

The discriminant nonzero hypothesis is explicit. A singular-cubic
proof remains necessary to discharge the full unconditional
CubicWeilCharacterUpper interface for every shift.
-/

namespace SparseDeletion.AINTLIBBridge

attribute [local instance] Classical.propDecidable

theorem triangular_original_character_sum_abs_bound
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (b : F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hchar : ringChar F ≠ 2)
    (hq : 15552 * b ^ 2 + 3888 * b + 239 ≠ 0)
    [Fintype (triangularWeierstrass b).toAffine.Point] :
    |(∑ x : F, ((quadraticCharFun F
      (8 * (x * (x + 1) * (2 * x + 1) / 6 + b) + 1) : ℤ) : ℝ))| ≤
        2 * Real.sqrt (Fintype.card F : ℝ) := by
  have hm := triangular_monic_character_sum_abs_bound
    b h2 h3 hchar hq
  have hz := triangular_cubic_character_sum_rescale
    b h2 h3
  have hzR :
      (∑ X : F, ((quadraticCharFun F
        (X ^ 3 + 4 * X ^ 2 + (32 / 9) * X +
          (64 / 9) * (8 * b + 1)) : ℤ) : ℝ)) =
      (∑ x : F, ((quadraticCharFun F
        (8 * (x * (x + 1) * (2 * x + 1) / 6 + b) + 1) : ℤ) : ℝ)) := by
    exact_mod_cast hz
  rw [hzR] at hm
  exact hm

end SparseDeletion.AINTLIBBridge

#print axioms SparseDeletion.AINTLIBBridge.triangular_original_character_sum_abs_bound
