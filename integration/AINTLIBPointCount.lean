module

public import Mathlib
public import HasseWeil.HasseBound

@[expose] public section

/-!
# Point count of an elliptic Weierstrass equation

A nonsingular Weierstrass curve has one point at infinity, and
every other point is exactly one ordered pair (x,y) satisfying
its affine equation. This module records the combinatorial bridge
required before relating pointCount to a quadratic-character sum.

This is not yet the full cubic character-sum identity.
-/

namespace SparseDeletion.AINTLIBBridge

attribute [local instance] Classical.propDecidable

theorem pointCount_eq_one_add_card_equation
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [Fintype W.toAffine.Point] :
    HasseWeil.pointCount W.toAffine =
      1 + ((Finset.univ : Finset (K × K)).filter
        (fun (xy : K × K) => W.toAffine.Equation xy.1 xy.2)).card := by
  classical
  let A : Type _ :=
    {xy : K × K // W.toAffine.Equation xy.1 xy.2}
  let finiteOption : Fintype (Option A) := inferInstance
  let e : W.toAffine.Point ≃ WithZero A := W.toAffine.pointEquiv
  let finiteWithZero : Fintype (WithZero A) :=
    Fintype.ofEquiv W.toAffine.Point e
  letI : Fintype (WithZero A) := finiteWithZero
  have heq : Fintype.card W.toAffine.Point =
      Fintype.card (WithZero A) :=
    Fintype.card_congr e
  have hop : Fintype.card (WithZero A) =
      @Fintype.card (Option A) finiteOption :=
    @Fintype.card_congr (WithZero A) (Option A)
      finiteWithZero finiteOption (Equiv.refl (Option A))
  have hopt : @Fintype.card (Option A) finiteOption =
      Fintype.card A + 1 := by
    simpa using (Fintype.card_option (α := A))
  have hcard : Fintype.card A =
      ((Finset.univ : Finset (K × K)).filter
        (fun (xy : K × K) => W.toAffine.Equation xy.1 xy.2)).card := by
    dsimp [A]
    rw [Fintype.card_subtype]
  dsimp [HasseWeil.pointCount]
  calc
    Fintype.card W.toAffine.Point =
        Fintype.card (WithZero A) := heq
    _ = @Fintype.card (Option A) finiteOption := hop
    _ = Fintype.card A + 1 := hopt
    _ = 1 + ((Finset.univ : Finset (K × K)).filter
        (fun (xy : K × K) => W.toAffine.Equation xy.1 xy.2)).card := by
      omega

end SparseDeletion.AINTLIBBridge

#print axioms SparseDeletion.AINTLIBBridge.pointCount_eq_one_add_card_equation
