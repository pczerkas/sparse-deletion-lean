module

public import Mathlib
public import HasseWeil.HasseBound
public import HasseWeil.SparseDeletion.PointCount
public import HasseWeil.SparseDeletion.Fubini
public import HasseWeil.SparseDeletion.CharacterFiber

@[expose] public section

/-!
# Exact character-sum formula for the number of elliptic points

For a nonsingular Weierstrass curve presented as y² = g(x)
over a finite field of odd characteristic, the number of points
(including infinity) is p+1+Σ_x χ(g(x)).

All three ingredients are kernel-proved in separate modules:
  * equivalence between elliptic points and affine equation solutions,
  * finite Fubini counting over Cartesian products,
  * the quadratic-character count of y² = z.
-/

namespace SparseDeletion.AINTLIBBridge

attribute [local instance] Classical.propDecidable

theorem pointCount_eq_field_card_add_character_sum
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (W : WeierstrassCurve F)
    [W.toAffine.IsElliptic] [Fintype W.toAffine.Point]
    (g : F → F) (hchar : ringChar F ≠ 2)
    (hEquation : ∀ x y : F,
      W.toAffine.Equation x y ↔ y ^ 2 = g x) :
    ((HasseWeil.pointCount W.toAffine : ℕ) : ℤ) =
      (Fintype.card F : ℤ) + 1 +
        ∑ x : F, quadraticCharFun F (g x) := by
  classical
  have hSet :
      ((Finset.univ : Finset (F × F)).filter
        (fun (xy : F × F) => W.toAffine.Equation xy.1 xy.2)) =
      ((Finset.univ : Finset (F × F)).filter
        (fun (xy : F × F) => xy.2 ^ 2 = g xy.1)) := by
    ext xy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hEquation xy.1 xy.2
  have hCount := pointCount_eq_one_add_card_equation W
  -- The filters below carry the very same Decidable instances as
  -- the goal. Proving the finite Fubini equality locally avoids
  -- instance-dependent elaboration differences across modules.
  have hFiber :
      (((Finset.univ : Finset (F × F)).filter
        (fun (xy : F × F) => xy.2 ^ 2 = g xy.1)).card : ℤ) =
      ∑ x : F, (((Finset.univ : Finset F).filter
        (fun y => y ^ 2 = g x)).card : ℤ) := by
    calc
      (((Finset.univ : Finset (F × F)).filter
        (fun (xy : F × F) => xy.2 ^ 2 = g xy.1)).card : ℤ) =
          ∑ xy : F × F, if xy.2 ^ 2 = g xy.1 then (1 : ℤ) else 0 := by
        simpa using (Finset.sum_boole
          (fun xy : F × F => xy.2 ^ 2 = g xy.1)
          (Finset.univ : Finset (F × F))).symm
      _ = ∑ x : F, ∑ y : F, if y ^ 2 = g x then (1 : ℤ) else 0 := by
        simpa only using
          (Fintype.sum_prod_type
            (fun xy : F × F =>
              if xy.2 ^ 2 = g xy.1 then (1 : ℤ) else 0))
      _ = ∑ x : F, (((Finset.univ : Finset F).filter
        (fun y => y ^ 2 = g x)).card : ℤ) := by
        apply Finset.sum_congr rfl
        intro x hx
        simpa using (Finset.sum_boole
          (fun y : F => y ^ 2 = g x) (Finset.univ : Finset F))
  have hChar :
      (∑ x : F, (((Finset.univ : Finset F).filter
          (fun y => y ^ 2 = g x)).card : ℤ)) =
      ∑ x : F, (1 + quadraticCharFun F (g x)) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact square_fiber_card_eq_character hchar (g x)
  have hCountZ :
      ((HasseWeil.pointCount W.toAffine : ℕ) : ℤ) =
        1 + (((Finset.univ : Finset (F × F)).filter
           (fun (xy : F × F) => W.toAffine.Equation xy.1 xy.2)).card : ℤ) := by
    exact_mod_cast hCount
  calc
    ((HasseWeil.pointCount W.toAffine : ℕ) : ℤ) =
        1 + (((Finset.univ : Finset (F × F)).filter
          (fun (xy : F × F) => W.toAffine.Equation xy.1 xy.2)).card : ℤ) := hCountZ
    _ = 1 + (((Finset.univ : Finset (F × F)).filter
          (fun (xy : F × F) => xy.2 ^ 2 = g xy.1)).card : ℤ) := by rw [hSet]
    _ = 1 + ∑ x : F, (((Finset.univ : Finset F).filter
          (fun y => y ^ 2 = g x)).card : ℤ) := by
      exact congrArg (fun z : ℤ => 1 + z) hFiber
    _ = 1 + ∑ x : F, (1 + quadraticCharFun F (g x)) := by rw [hChar]
    _ = (Fintype.card F : ℤ) + 1 +
          ∑ x : F, quadraticCharFun F (g x) := by
      rw [Finset.sum_add_distrib]
      simp
      ring

end SparseDeletion.AINTLIBBridge

#print axioms SparseDeletion.AINTLIBBridge.pointCount_eq_field_card_add_character_sum
