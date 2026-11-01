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

/-- Exact discriminant of the triangular-prefix Weierstrass family.
This makes the nonsingular/singular case split explicit. -/
theorem triangular_weierstrass_discriminant
    {F : Type*} [Field F] (b : F)
    (h3 : (3 : F) ≠ 0) :
    (triangularWeierstrass b).Δ =
      -(65536 / 729 : F) * (15552 * b^2 + 3888 * b + 239) := by
  have h9 : (9 : F) ≠ 0 := by
    have heq : (9 : F) = (3 : F)^2 := by norm_num
    rw [heq]
    exact pow_ne_zero 2 h3
  have h729 : (729 : F) ≠ 0 := by
    have heq : (729 : F) = (3 : F)^6 := by norm_num
    rw [heq]
    exact pow_ne_zero 6 h3
  dsimp [triangularWeierstrass, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  field_simp [h3, h9, h729]
  ring

#print axioms SparseDeletion.AINTLIBBridge.triangular_weierstrass_discriminant

/-- Nonsingular fibers are elliptic curves. The explicit denominator
conditions hold automatically over ZMod p for primes p >= 37. -/
theorem triangular_weierstrass_isElliptic
    {F : Type*} [Field F] (b : F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hq : 15552 * b^2 + 3888 * b + 239 ≠ 0) :
    (triangularWeierstrass b).IsElliptic := by
  have h65536 : (65536 : F) ≠ 0 := by
    have heq : (65536 : F) = (2 : F)^16 := by norm_num
    rw [heq]
    exact pow_ne_zero 16 h2
  have h729 : (729 : F) ≠ 0 := by
    have heq : (729 : F) = (3 : F)^6 := by norm_num
    rw [heq]
    exact pow_ne_zero 6 h3
  have hΔ : (triangularWeierstrass b).Δ ≠ 0 := by
    rw [triangular_weierstrass_discriminant b h3]
    exact mul_ne_zero
      (neg_ne_zero.mpr (div_ne_zero h65536 h729)) hq
  exact ⟨isUnit_iff_ne_zero.mpr hΔ⟩

/-- Apply the genuine upstream Hasse theorem to our *explicit*
nonsingular triangular-prefix Weierstrass model. -/
theorem triangular_weierstrass_hasse_bound
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (b : F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hq : 15552 * b^2 + 3888 * b + 239 ≠ 0)
    [Fintype (triangularWeierstrass b).toAffine.Point] :
    |((HasseWeil.pointCount (triangularWeierstrass b).toAffine : ℝ) -
      (Fintype.card F : ℝ) - 1)| ≤
      2 * Real.sqrt (Fintype.card F : ℝ) := by
  letI : (triangularWeierstrass b).toAffine.IsElliptic :=
    triangular_weierstrass_isElliptic b h2 h3 hq
  exact HasseWeil.WeilPairing.hasse_bound (triangularWeierstrass b)

#print axioms SparseDeletion.AINTLIBBridge.triangular_weierstrass_hasse_bound

end SparseDeletion.AINTLIBBridge

#print axioms SparseDeletion.AINTLIBBridge.triangular_cubic_rescale_identity
