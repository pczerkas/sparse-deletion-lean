module -- shake: keep-all

public import CubicShape

@[expose] public section

namespace SparseDeletion

open Finset Polynomial

attribute [local instance] Classical.propDecidable

section AffineValue
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
theorem cubic_eval_affine_value (b x : F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    (cubicShape (16 * (6 : F)⁻¹) (24 * (6 : F)⁻¹)
      (8 * (6 : F)⁻¹) (8 * b + 1)).eval x =
      (3 : F)⁻¹ * ((2 * x + 1)^3 - (2 * x + 1)) + (8 * b + 1) := by
  simp only [cubicShape, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_pow]
  have h6 : (6 : F) ≠ 0 := by
    rw [show (6 : F) = (2 : F) * (3 : F) by norm_num]
    exact mul_ne_zero h2 h3
  field_simp
  ring

theorem cubicShape_image_card_eq_xcube_sub_x
    (b : F) (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    ((univ : Finset F).image
      (fun x => (cubicShape (16 * (6 : F)⁻¹) (24 * (6 : F)⁻¹)
        (8 * (6 : F)⁻¹) (8 * b + 1)).eval x)).card =
    ((univ : Finset F).image (fun t : F => t ^ 3 - t)).card := by
  let f : F → F := fun x =>
    (cubicShape (16 * (6 : F)⁻¹) (24 * (6 : F)⁻¹)
      (8 * (6 : F)⁻¹) (8 * b + 1)).eval x
  let g : F → F := fun t => t ^ 3 - t
  let A : F → F := fun y => (3 : F)⁻¹ * y + (8 * b + 1)
  have hsurj : Function.Surjective (fun x : F => 2 * x + 1) := by
    intro t
    refine ⟨(2 : F)⁻¹ * (t - 1), ?_⟩
    field_simp
    ring
  have hinj : Function.Injective A := by
    intro x y h
    have h' : (3 : F)⁻¹ * x = (3 : F)⁻¹ * y :=
      add_right_cancel h
    exact (mul_left_cancel₀ (inv_ne_zero h3)) h'
  have himage : (univ : Finset F).image f =
      ((univ : Finset F).image g).image A := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨g (2 * x + 1), ⟨2 * x + 1, rfl⟩, ?_⟩
      exact (cubic_eval_affine_value b x h2 h3).symm
    · rintro ⟨_, ⟨t, rfl⟩, rfl⟩
      obtain ⟨x, hx⟩ := hsurj t
      refine ⟨x, ?_⟩
      rw [← hx]
      exact cubic_eval_affine_value b x h2 h3
  change ((univ : Finset F).image f).card =
    ((univ : Finset F).image g).card
  rw [himage]
  exact Finset.card_image_of_injective _ hinj

#print axioms cubic_eval_affine_value
#print axioms cubicShape_image_card_eq_xcube_sub_x

end AffineValue

end SparseDeletion
