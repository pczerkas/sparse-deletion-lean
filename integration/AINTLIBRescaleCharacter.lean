module

public import Mathlib
public import HasseWeil.SparseDeletion.CubicModel

@[expose] public section

/-!
# Quadratic character invariance under the triangular-cubic rescaling

The affine isomorphism uses a = 8/3, X = a*x, Y = a*y.
This proof shows that the associated quadratic character sums
are invariant, because multiplication by nonzero a permutes the
finite field and multiplying by a square does not change the character.

This does not require ellipticity or the Hasse theorem.
-/

namespace SparseDeletion.AINTLIBBridge

attribute [local instance] Classical.propDecidable

theorem quadraticCharFun_square_scale
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (a z : F) (ha : a ≠ 0) :
    quadraticCharFun F (a ^ 2 * z) = quadraticCharFun F z := by
  have hs : quadraticCharFun F (a ^ 2) = 1 := by
    simpa only [quadraticChar_apply] using
      (quadraticChar_sq_one' (F := F) ha)
  rw [quadraticCharFun_mul, hs]
  simp

theorem triangular_cubic_character_sum_rescale
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (b : F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (∑ X : F, quadraticCharFun F
      (X ^ 3 + 4 * X ^ 2 + (32 / 9) * X +
        (64 / 9) * (8 * b + 1))) =
    ∑ x : F, quadraticCharFun F
      (8 * (x * (x + 1) * (2 * x + 1) / 6 + b) + 1) := by
  let a : F := 8 / 3
  have h8 : (8 : F) ≠ 0 := by
    have heq : (8 : F) = (2 : F) ^ 3 := by norm_num
    rw [heq]
    exact pow_ne_zero 3 h2
  have ha : a ≠ 0 := div_ne_zero h8 h3
  let g : F → ℤ := fun X =>
    quadraticCharFun F (X ^ 3 + 4 * X ^ 2 +
      (32 / 9) * X + (64 / 9) * (8 * b + 1))
  have hperm : (∑ X : F, g X) = ∑ x : F, g (a * x) := by
    exact ((Equiv.mulLeft₀ a ha).sum_comp g).symm
  have hpointwise : ∀ x : F,
      g (a * x) =
        quadraticCharFun F
          (8 * (x * (x + 1) * (2 * x + 1) / 6 + b) + 1) := by
    intro x
    dsimp [g, a]
    rw [triangular_cubic_rescale_identity x b h2 h3]
    exact quadraticCharFun_square_scale (8 / 3 : F) _ ha
  calc
    (∑ X : F, quadraticCharFun F
      (X ^ 3 + 4 * X ^ 2 + (32 / 9) * X +
        (64 / 9) * (8 * b + 1))) =
      ∑ X : F, g X := rfl
    _ = ∑ x : F, g (a * x) := hperm
    _ = ∑ x : F, quadraticCharFun F
      (8 * (x * (x + 1) * (2 * x + 1) / 6 + b) + 1) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hpointwise x

end SparseDeletion.AINTLIBBridge

#print axioms SparseDeletion.AINTLIBBridge.triangular_cubic_character_sum_rescale
