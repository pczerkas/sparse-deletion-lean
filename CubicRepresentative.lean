module -- shake: keep-all

public import ConicPointBound

@[expose] public section

namespace SparseDeletion

open Finset

attribute [local instance] Classical.propDecidable

section Representatives

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def cubicVal (x : F) : F := x ^ 3 - x

/-- Choose one representative from every nonempty fiber of x³-x. -/
noncomputable def cubicRep (v : F) : F :=
  if h : ∃ x : F, cubicVal x = v then Classical.choose h else 0

theorem cubicRep_is_root (x : F) :
    cubicVal (cubicRep (cubicVal x)) = cubicVal x := by
  unfold cubicRep
  have h : ∃ y : F, cubicVal y = cubicVal x := ⟨x, rfl⟩
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem cubicRep_stable (x : F) :
    cubicRep (cubicVal (cubicRep (cubicVal x))) =
      cubicRep (cubicVal x) := by
  rw [cubicRep_is_root]

noncomputable def cubicFixed : Finset F :=
  Finset.univ.filter (fun x => cubicRep (cubicVal x) = x)

noncomputable def cubicExtra : Finset F :=
  Finset.univ.filter (fun x => cubicRep (cubicVal x) ≠ x)

/-- Exactly one representative is selected for each value of the cubic. -/
theorem cubicFixed_card_eq_image :
    (cubicFixed (F := F)).card =
    ((Finset.univ : Finset F).image cubicVal).card := by
  have heq : (cubicFixed (F := F)).image cubicVal =
      (Finset.univ : Finset F).image cubicVal := by
    ext z
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, _, rfl⟩
      exact ⟨x, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨cubicRep (cubicVal x), ?_, cubicRep_is_root x⟩
      simp only [cubicFixed, Finset.mem_filter, Finset.mem_univ, true_and]
      exact cubicRep_stable x
  have hinj : Set.InjOn cubicVal (↑(cubicFixed (F := F)) : Set F) := by
    intro x hx y hy hxy
    have hrx := (Finset.mem_filter.mp hx).2
    have hry := (Finset.mem_filter.mp hy).2
    calc
      x = cubicRep (cubicVal x) := hrx.symm
      _ = cubicRep (cubicVal y) := by rw [hxy]
      _ = y := hry
  rw [← heq]
  exact (Finset.card_image_of_injOn hinj).symm

/-- The number of nonrepresentatives is exactly p minus the value-set size. -/
theorem cubicExtra_card_add_image :
    (cubicExtra (F := F)).card +
        ((Finset.univ : Finset F).image cubicVal).card =
      Fintype.card F := by
  have hp : (cubicFixed (F := F)).card + (cubicExtra (F := F)).card =
      Fintype.card F := by
    simpa only [cubicFixed, cubicExtra, Finset.card_univ] using
      (Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset F)) (fun x => cubicRep (cubicVal x) = x))
  have hc := cubicFixed_card_eq_image (F := F)
  omega

#print axioms cubicRep_is_root
#print axioms cubicFixed_card_eq_image
#print axioms cubicExtra_card_add_image

end Representatives

end SparseDeletion
