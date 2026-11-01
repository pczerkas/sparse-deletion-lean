module

public import Mathlib
public import HasseWeil.HasseBound

@[expose] public section

/-!
# External downstream smoke test of AINTLIB's Hasse bound

This file is compiled inside AINTLIB's pinned Lean 4.36.0-rc2
workspace by GitHub Actions, not inside the main
sparse-deletion-lean Lean 4.35 workspace.

Successful compilation verifies that our downstream client can
import the published capstone without sorryAx. It does NOT yet
establish the specific cubic-character-sum bound.
-/

namespace SparseDeletion.AINTLIBBridge

/-- Hasse's inequality, callable from an independent downstream module. -/
theorem hasse_import_available
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [Fintype W.toAffine.Point] :
    |((HasseWeil.pointCount W.toAffine : ℝ) -
      (Fintype.card K : ℝ) - 1)| ≤
      2 * Real.sqrt (Fintype.card K : ℝ) :=
  HasseWeil.WeilPairing.hasse_bound W

/-- Bridge from a proved elliptic point-count identity to the character
sum estimate. The point-count identity for our cubic is not supplied
here and remains a separate proof obligation. -/
theorem abs_character_sum_le_of_point_count
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (W : WeierstrassCurve K)
    [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (S : ℝ)
    (hcount : (HasseWeil.pointCount W.toAffine : ℝ) =
      (Fintype.card K : ℝ) + 1 + S) :
    |S| ≤ 2 * Real.sqrt (Fintype.card K : ℝ) := by
  have h := hasse_import_available W
  rw [hcount] at h
  have hnormalize :
      (Fintype.card K : ℝ) + 1 + S -
        (Fintype.card K : ℝ) - 1 = S := by ring
  simpa only [hnormalize] using h

end SparseDeletion.AINTLIBBridge

/-- info: 'HasseWeil.WeilPairing.hasse_bound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms HasseWeil.WeilPairing.hasse_bound

/-- info: 'SparseDeletion.AINTLIBBridge.abs_character_sum_le_of_point_count' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SparseDeletion.AINTLIBBridge.abs_character_sum_le_of_point_count
