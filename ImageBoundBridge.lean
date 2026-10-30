module -- shake: keep-all

public import CubicSumBridge

@[expose] public section

namespace SparseDeletion

open Finset

attribute [local instance] Classical.propDecidable

/-!
The elementary finite-set bridge needed by the new value-set approach.
Unlike the Hasse path, this uses no quadratic-character sums.
-/

section FiniteImage
variable {α β : Type*}
variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

omit [DecidableEq α] in
theorem good_card_add_image_le
    (f : α → β) (P : β → Prop) [DecidablePred P] :
    ((univ : Finset α).filter (fun x => P (f x))).card +
      ((univ : Finset α).image f).card ≤
      Fintype.card α + ((univ : Finset β).filter P).card := by
  let G : Finset α := univ.filter (fun x => P (f x))
  let B : Finset α := univ.filter (fun x => ¬ P (f x))
  have hunion :
      ((univ : Finset α).image f) ⊆ (G.image f) ∪ (B.image f) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    by_cases h : P (f x)
    · apply Finset.mem_union.mpr
      left
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_filter.mpr ⟨hx, h⟩, rfl⟩
    · apply Finset.mem_union.mpr
      right
      exact Finset.mem_image.mpr
        ⟨x, Finset.mem_filter.mpr ⟨hx, h⟩, rfl⟩
  have hgood :
      (G.image f).card ≤ ((univ : Finset β).filter P).card := by
    apply Finset.card_le_card
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  have hbad : (B.image f).card ≤ B.card := Finset.card_image_le
  have hpartition : G.card + B.card = Fintype.card α := by
    simpa only [G, B, Finset.card_univ] using
      (Finset.card_filter_add_card_filter_not
        (s := (univ : Finset α)) (fun x => P (f x)))
  have htotal : ((univ : Finset α).image f).card ≤
      (G.image f).card + (B.image f).card :=
    (Finset.card_le_card hunion).trans (Finset.card_union_le _ _)
  dsimp [G] at *
  omega

theorem six_sevenths_of_cubic_image_bound
    {F : Type*} [CommRing F] [Fintype F] [DecidableEq F]
    (f : F → F)
    (hlarge : 35 ≤ Fintype.card F)
    (himage : 2 * Fintype.card F ≤
      3 * ((univ : Finset F).image f).card + 1)
    (hsquares : 2 * ((univ : Finset F).filter IsSquare).card ≤
      Fintype.card F + 1) :
    7 * ((univ : Finset F).filter (fun x => IsSquare (f x))).card ≤
      6 * Fintype.card F := by
  have hcomb := good_card_add_image_le f IsSquare
  omega

end FiniteImage

#print axioms good_card_add_image_le
#print axioms six_sevenths_of_cubic_image_bound

end SparseDeletion
