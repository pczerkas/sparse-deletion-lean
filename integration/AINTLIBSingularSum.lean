module

public import Mathlib

@[expose] public section

/-!
# Elementary singular cubic character-sum identity

For an odd-characteristic finite field, a*(x-u)^2*(x-v)
has an exact quadratic-character sum -χ(a)χ(u-v). No Hasse
or Weil theorem is needed. The nonsingular case is treated
separately by the AINTLIB Hasse bridge.

This file does NOT itself prove the discriminant-zero
factorization of the particular triangular cubic.
-/

namespace SparseDeletion.AINTLIBBridge

attribute [local instance] Classical.propDecidable

theorem singular_double_root_character_sum
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hchar : ringChar F ≠ 2)
    (a u v : F) :
    (∑ x : F, quadraticCharFun F
      (a * (x-u)^2 * (x-v))) =
      -(quadraticCharFun F a) * quadraticCharFun F (u-v) := by
  classical
  let f : F → ℤ := fun x =>
    quadraticCharFun F a * quadraticCharFun F (x-v)
  have hsumZero : (∑ x : F, quadraticCharFun F (x-v)) = 0 := by
    have h0 : (∑ x : F, quadraticCharFun F x) = 0 := by
      simpa only [quadraticChar_apply] using
        (quadraticChar_sum_zero (F := F) hchar)
    calc
      (∑ x : F, quadraticCharFun F (x-v)) =
          ∑ x : F, quadraticCharFun F x := by
        exact (Equiv.subRight v).sum_comp (quadraticCharFun F)
      _ = 0 := h0
  have hsumF : (∑ x : F, f x) = 0 := by
    simp only [f, ← Finset.mul_sum, hsumZero, mul_zero]
  have hsingle :
      (∑ x : F, if x = u then f x else (0 : ℤ)) = f u := by
    simpa using (Fintype.sum_ite_eq' u f)
  have hdiff :
      (∑ x : F, if x = u then (0 : ℤ) else f x) =
        (∑ x : F, f x) - f u := by
    calc
      (∑ x : F, if x = u then (0 : ℤ) else f x) =
          ∑ x : F, (f x - if x = u then f x else 0) := by
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxu : x = u <;> simp [hxu]
      _ = (∑ x : F, f x) -
            (∑ x : F, if x = u then f x else (0 : ℤ)) := by
        rw [Finset.sum_sub_distrib]
      _ = (∑ x : F, f x) - f u := by rw [hsingle]
  have hpointwise : ∀ x : F,
      quadraticCharFun F (a * (x-u)^2 * (x-v)) =
        if x=u then 0 else f x := by
    intro x
    by_cases hx : x = u
    · subst x
      simp
    · have hxu : x-u ≠ 0 := sub_ne_zero.mpr hx
      have hsq : quadraticCharFun F ((x-u)^2) = 1 := by
        simpa only [quadraticChar_apply] using
          (quadraticChar_sq_one' (F := F) hxu)
      rw [quadraticCharFun_mul, quadraticCharFun_mul, hsq]
      simp [f, hx]
  calc
    (∑ x : F, quadraticCharFun F
      (a * (x-u)^2 * (x-v))) =
        ∑ x : F, if x = u then (0 : ℤ) else f x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hpointwise x
    _ = (∑ x : F, f x) - f u := hdiff
    _ = -(quadraticCharFun F a) *
        quadraticCharFun F (u-v) := by
      rw [hsumF]
      simp only [zero_sub, f]
      ring

end SparseDeletion.AINTLIBBridge

#print axioms SparseDeletion.AINTLIBBridge.singular_double_root_character_sum
