module

public import Mathlib
public import HasseWeil.HasseBound

@[expose] public section

/-!
# Algebraic change of variables for the triangular-square cubic

This is an exact field identity, independent of Weil/Hasse and
independent of any large-number estimates.

For characteristic != 2,3, set a = 8/3.
Our cubic f_b(x) = 8*(x(x+1)(2x+1)/6+b)+1
transforms to the monic Weierstrass cubic:
g_b(X) = X^3 + 4 X^2 + (32/9) X + (64/9)(8b+1).
The identity g_b(a*x) = a^2*f_b(x) is checked below.
-/

namespace SparseDeletion.AINTLIBBridge

/-- The Weierstrass curve whose affine equation is the rescaled
triangular-prefix cubic. Nonsingularity will be addressed separately. -/
def triangularWeierstrass
    {F : Type*} [Field F] (b : F) : WeierstrassCurve F :=
  { a₁ := 0
    a₂ := 4
    a₃ := 0
    a₄ := 32 / 9
    a₆ := (64 / 9) * (8 * b + 1) }

theorem triangular_cubic_rescale_identity
    {F : Type*} [Field F] (x b : F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    let a : F := 8 / 3
    (a * x)^3 + 4 * (a * x)^2 +
        (32 / 9) * (a * x) + (64 / 9) * (8 * b + 1) =
      a^2 * (8 * (x * (x + 1) * (2 * x + 1) / 6 + b) + 1) := by
  dsimp
  have h6 : (6 : F) ≠ 0 := by
    have h : (6 : F) = 2 * 3 := by norm_num
    rw [h]
    exact mul_ne_zero h2 h3
  have h9 : (9 : F) ≠ 0 := by
    have h : (9 : F) = 3 * 3 := by norm_num
    rw [h]
    exact mul_ne_zero h3 h3
  field_simp [h2, h3, h6, h9]
  ring

end SparseDeletion.AINTLIBBridge

#print axioms SparseDeletion.AINTLIBBridge.triangular_cubic_rescale_identity
