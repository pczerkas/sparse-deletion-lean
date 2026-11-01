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

theorem pointCount_eq_one_add_card_equation
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [Fintype W.toAffine.Point] :
    HasseWeil.pointCount W.toAffine =
      1 + ((Finset.univ : Finset (K × K)).filter
        (fun (xy : K × K) => W.toAffine.Equation xy.1 xy.2)).card := by
  classical
  letI : Fintype (WithZero
      {xy : K × K // W.toAffine.Equation xy.1 xy.2}) :=
    Fintype.ofEquiv W.toAffine.Point (W.toAffine.pointEquiv)
  have heq :
      Fintype.card W.toAffine.Point =
        Fintype.card (WithZero
          {xy : K × K // W.toAffine.Equation xy.1 xy.2}) :=
    Fintype.card_congr (W.toAffine.pointEquiv)
  have hcard :
      Fintype.card {xy : K × K // W.toAffine.Equation xy.1 xy.2} =
        ((Finset.univ : Finset (K × K)).filter
          (fun (xy : K × K) => W.toAffine.Equation xy.1 xy.2)).card := by
    rw [Fintype.card_subtype]
  dsimp [HasseWeil.pointCount]
  rw [heq]
  change Fintype.card
    (Option {xy : K × K // W.toAffine.Equation xy.1 xy.2}) =
      1 + ((Finset.univ : Finset (K × K)).filter
        (fun (xy : K × K) => W.toAffine.Equation xy.1 xy.2)).card
  simp [hcard, Nat.add_comm]

end SparseDeletion.AINTLIBBridge

#print axioms SparseDeletion.AINTLIBBridge.pointCount_eq_one_add_card_equation
