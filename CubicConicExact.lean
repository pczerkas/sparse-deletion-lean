module -- shake: keep-all

public import CubicConicInjection

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

section Exact
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A conic pair determines the three possible roots of the cubic fiber. -/
theorem cubic_conic_rep_cases (u v : F)
    (h : u ^ 2 + u * v + v ^ 2 = 1) :
    let a := cubicRep (cubicVal u)
    a = u ∨ a = v ∨ a = -u - v := by
  dsimp
  have hroot := cubicRep_is_root u
  have hfactor :
      cubicVal (cubicRep (cubicVal u)) - cubicVal u =
      (cubicRep (cubicVal u) - u) *
      (cubicRep (cubicVal u) - v) *
      (cubicRep (cubicVal u) - (-u-v)) := by
    calc
      _ = (cubicRep (cubicVal u) - u) *
          (cubicRep (cubicVal u) - v) *
          (cubicRep (cubicVal u) - (-u-v)) +
          (cubicRep (cubicVal u) - u) * (u ^ 2 + u*v + v^2 - 1) := by
            unfold cubicVal
            ring
      _ = _ := by rw [h]; ring
  rw [hroot, sub_self] at hfactor
  have hzero := hfactor.symm
  rcases mul_eq_zero.mp hzero with hab | haw
  · rcases mul_eq_zero.mp hab with ha | hb
    · exact Or.inl (sub_eq_zero.mp ha)
    · exact Or.inr (Or.inl (sub_eq_zero.mp hb))
  · exact Or.inr (Or.inr (sub_eq_zero.mp haw))


/-- Every point of the collision conic comes from a nonrepresentative and a
cyclic orientation of its cubic fiber. This complements cubicCode_inj. -/
theorem cubicCode_surj_conic (u v : F)
    (h : u ^ 2 + u * v + v ^ 2 = 1) :
    ∃ x : F, x ∈ cubicExtra (F := F) ∧
      ∃ i : Fin 3, cubicCode (x, i) = (u, v) := by
  let a : F := cubicRep (cubicVal u)
  have hvalv : cubicVal v = cubicVal u := by
    apply (cubic_value_collision_iff v u).mpr
    right
    linear_combination h
  have hvalw : cubicVal (-u-v) = cubicVal u := by
    apply (cubic_value_collision_iff (-u-v) u).mpr
    right
    calc
      (-u-v)^2 + (-u-v)*u + u^2 = u^2 + u*v + v^2 := by ring
      _ = 1 := h
  have hrepv : cubicRep (cubicVal v) = a := by rw [hvalv]
  have hrepw : cubicRep (cubicVal (-u-v)) = a := by rw [hvalw]
  have hcases : a = u ∨ a = v ∨ a = -u-v := cubic_conic_rep_cases u v h
  by_cases hau : a = u
  · by_cases huv : u = v
    · subst v
      have hw : -u-u ≠ u := by
        intro he
        have h10 : (1 : F) = 0 := by
          linear_combination -h - u * he
        exact one_ne_zero h10
      refine ⟨-u-u, ?_, (2 : Fin 3), ?_⟩
      · simp only [cubicExtra, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hrepw, hau]
        exact hw.symm
      · change cubicTriple (cubicRep (cubicVal (-u-u))) (-u-u) 2 = (u,u)
        rw [hrepw, hau]
        simp [cubicTriple]
    · refine ⟨v, ?_, (0 : Fin 3), ?_⟩
      · simp only [cubicExtra, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hrepv, hau]
        exact huv
      · change cubicTriple (cubicRep (cubicVal v)) v 0 = (u,v)
        rw [hrepv, hau]
        simp [cubicTriple]
  · by_cases haw : a = -u-v
    · refine ⟨u, ?_, (1 : Fin 3), ?_⟩
      · simp only [cubicExtra, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hau
      · change cubicTriple a u 1 = (u,v)
        rw [haw]
        simp [cubicTriple]
    · have hav : a = v := (hcases.resolve_left hau).resolve_right haw
      refine ⟨-u-v, ?_, (2 : Fin 3), ?_⟩
      · simp only [cubicExtra, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [hrepw]
        exact haw
      · change cubicTriple (cubicRep (cubicVal (-u-v))) (-u-v) 2 = (u,v)
        rw [hrepw, hav]
        simp [cubicTriple]
        ring


/-- The cubic coding is a bijection between three orientations of each
nonrepresentative and all points of the collision conic. -/
theorem cubicExtra_three_eq_conic_card :
    3 * (cubicExtra (F := F)).card = (cubicConicPoints (F := F)).card := by
  let D : Finset F := cubicExtra
  let S : Finset (F × Fin 3) := D.product Finset.univ
  have hcover : cubicConicPoints (F := F) ⊆ S.image cubicCode := by
    intro z hz
    rcases z with ⟨u, v⟩
    have hc : u ^ 2 + u * v + v ^ 2 = 1 :=
      (Finset.mem_filter.mp hz).2
    obtain ⟨x, hx, i, heq⟩ := cubicCode_surj_conic u v hc
    exact Finset.mem_image.mpr
      ⟨(x, i), Finset.mem_product.mpr ⟨hx, Finset.mem_univ _⟩, heq⟩
  have hinj : Set.InjOn cubicCode (↑S : Set (F × Fin 3)) := by
    intro z hz w hw heq
    have hx := (Finset.mem_product.mp hz).1
    have hy := (Finset.mem_product.mp hw).1
    obtain ⟨hxy, hij⟩ := cubicCode_inj z.1 w.1 z.2 w.2 hx hy heq
    exact Prod.ext hxy hij
  have hrev := Finset.card_le_card hcover
  rw [Finset.card_image_of_injOn hinj] at hrev
  change (cubicConicPoints (F := F)).card ≤
    (D.product (Finset.univ : Finset (Fin 3))).card at hrev
  rw [Finset.product_eq_sprod, Finset.card_product,
    Finset.card_univ, Fintype.card_fin] at hrev
  have hfwd := cubicExtra_three_le_conic_card (F := F)
  dsimp [D] at hrev
  omega

/-- Exact relation between the cubic value set and its collision conic. -/
theorem cubic_value_set_conic_exact :
    3 * Fintype.card F =
      3 * ((Finset.univ : Finset F).image (fun t : F => t ^ 3 - t)).card +
        (cubicConicPoints (F := F)).card := by
  have hconic := cubicExtra_three_eq_conic_card (F := F)
  have hpartition := cubicExtra_card_add_image (F := F)
  change (cubicExtra (F := F)).card +
    ((Finset.univ : Finset F).image (fun t : F => t ^ 3 - t)).card =
    Fintype.card F at hpartition
  omega

#print axioms cubic_conic_rep_cases
#print axioms cubicCode_surj_conic
#print axioms cubicExtra_three_eq_conic_card
#print axioms cubic_value_set_conic_exact

end Exact
end SparseDeletion
