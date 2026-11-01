module

public import Mathlib
public import HasseWeil.SparseDeletion.SingularSum

@[expose] public section

/-!
# Explicit factorization of singular triangular-square cubics

When q(b)=15552*b^2+3888*b+239 vanishes in a field with
2,3 invertible, our cubic has the explicit factorization

 f_b(x) = (8/3)*(x-u)^2*(x-v)

where t=3*(24*b+3)/2, u=(t-1)/2, v=(-2*t-1)/2.

An exact algebraic identity is sufficient; no abstract
discriminant/splitting-field theory is required.
-/

namespace SparseDeletion.AINTLIBBridge

attribute [local instance] Classical.propDecidable

theorem triangular_singular_cubic_factors
    {F : Type*} [Field F]
    (b : F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hq : 15552 * b ^ 2 + 3888 * b + 239 = 0) :
    ∃ u v : F, ∀ x : F,
      8 * (x * (x + 1) * (2*x+1) / 6 + b) + 1 =
        (8/3 : F) * (x-u)^2 * (x-v) := by
  let t : F := 3 * (24*b+3) / 2
  let u : F := (t-1)/2
  let v : F := (-2*t-1)/2
  refine ⟨u, v, ?_⟩
  intro x
  have h6 : (6 : F) ≠ 0 := by
    have h : (6 : F) = 2*3 := by norm_num
    rw [h]
    exact mul_ne_zero h2 h3
  have hid :
      (8 * (x * (x+1) * (2*x+1) / 6 + b) + 1) -
          (8/3 : F)*(x-u)^2*(x-v) =
        (x - 12*b - 1) * (15552*b^2+3888*b+239) / 6 := by
    dsimp [u,v,t]
    field_simp [h2, h3, h6]
    ring
  rw [hq] at hid
  simp only [mul_zero, zero_div, sub_eq_zero] at hid
  exact hid

/-- In the singular case, the original cubic character sum
is explicitly a single negative character product. -/
theorem triangular_singular_character_sum_exact
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (b : F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hchar : ringChar F ≠ 2)
    (hq : 15552*b^2+3888*b+239 = 0) :
    ∃ u v : F,
      (∑ x : F, quadraticCharFun F
        (8 * (x * (x+1) * (2*x+1) / 6 + b) + 1)) =
        -quadraticCharFun F (8/3) * quadraticCharFun F (u-v) := by
  obtain ⟨u,v,heq⟩ := triangular_singular_cubic_factors b h2 h3 hq
  refine ⟨u,v,?_⟩
  calc
    (∑ x : F, quadraticCharFun F
        (8 * (x * (x+1) * (2*x+1) / 6 + b) + 1)) =
      ∑ x : F, quadraticCharFun F ((8/3 : F)*(x-u)^2*(x-v)) := by
        apply Finset.sum_congr rfl
        intro x hx
        rw [heq x]
    _ = -quadraticCharFun F (8/3) * quadraticCharFun F (u-v) :=
      singular_double_root_character_sum hchar (8/3) u v

end SparseDeletion.AINTLIBBridge

#print axioms SparseDeletion.AINTLIBBridge.triangular_singular_cubic_factors
#print axioms SparseDeletion.AINTLIBBridge.triangular_singular_character_sum_exact
