module

public import Mathlib
public import HasseWeil.SparseDeletion.OriginalHasse
public import HasseWeil.SparseDeletion.SingularFactor

@[expose] public section

/-!
# Unconditional cubic character estimate for every shift

The nonsingular case uses AINTLIB's actual Hasse theorem via the
point-count bridge. The singular case uses explicit double-root
factorization and the elementary quadratic-character sum identity.

This downstream theorem will still need specialization from arbitrary
finite fields to ZMod p and transport to the original 4.35 project.
-/

namespace SparseDeletion.AINTLIBBridge

attribute [local instance] Classical.propDecidable

private theorem quadraticCharFun_three_values
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (z : F) :
    quadraticCharFun F z = 0 ∨
      quadraticCharFun F z = 1 ∨ quadraticCharFun F z = -1 := by
  classical
  unfold quadraticCharFun
  split_ifs <;> simp

/-- A singular cubic has character sum of absolute value at most one. -/
theorem triangular_singular_character_abs_le_one
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (b : F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hchar : ringChar F ≠ 2)
    (hq : 15552*b^2+3888*b+239 = 0) :
    |(∑ x : F, ((quadraticCharFun F
      (8*(x*(x+1)*(2*x+1)/6+b)+1) : ℤ) : ℝ))| ≤ 1 := by
  obtain ⟨u, v, hsum⟩ :=
    triangular_singular_character_sum_exact b h2 h3 hchar hq
  have hval : |(∑ x : F, quadraticCharFun F
      (8*(x*(x+1)*(2*x+1)/6+b)+1))| ≤ (1 : ℤ) := by
    rw [hsum]
    rcases quadraticCharFun_three_values ((8/3 : F)) with ha | ha | ha <;>
      rcases quadraticCharFun_three_values (u-v) with hb | hb | hb <;>
      simp [ha, hb]
  have hcast : (∑ x : F, ((quadraticCharFun F
      (8*(x*(x+1)*(2*x+1)/6+b)+1) : ℤ) : ℝ)) =
    ((∑ x : F, quadraticCharFun F
      (8*(x*(x+1)*(2*x+1)/6+b)+1)) : ℝ) := by
    push_cast
    rfl
  rw [hcast]
  exact_mod_cast hval

/-- The exact unconditional Weil/Hasse-type bound for our cubic,
including both nonsingular and singular parameter values. -/
theorem triangular_original_character_sum_abs_bound_all
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (b : F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hchar : ringChar F ≠ 2)
    [Fintype (triangularWeierstrass b).toAffine.Point] :
    |(∑ x : F, ((quadraticCharFun F
      (8*(x*(x+1)*(2*x+1)/6+b)+1) : ℤ) : ℝ))| ≤
        2 * Real.sqrt (Fintype.card F : ℝ) := by
  by_cases hq : 15552*b^2+3888*b+239 = 0
  · have hs := triangular_singular_character_abs_le_one b h2 h3 hchar hq
    have hcn : 1 ≤ Fintype.card F := by
      have hc : 0 < Fintype.card F := Fintype.card_pos
      omega
    have hc : (1 : ℝ) ≤ (Fintype.card F : ℝ) := by exact_mod_cast hcn
    have hr0 : 0 ≤ Real.sqrt (Fintype.card F : ℝ) :=
      Real.sqrt_nonneg _
    have hsqrt : (Real.sqrt (Fintype.card F : ℝ)) ^ 2 =
        (Fintype.card F : ℝ) :=
      Real.sq_sqrt (by linarith)
    have hroot : (1 : ℝ) ≤ Real.sqrt (Fintype.card F : ℝ) := by
      nlinarith
    linarith
  · exact triangular_original_character_sum_abs_bound
      b h2 h3 hchar hq

end SparseDeletion.AINTLIBBridge

#print axioms SparseDeletion.AINTLIBBridge.triangular_singular_character_abs_le_one
#print axioms SparseDeletion.AINTLIBBridge.triangular_original_character_sum_abs_bound_all
