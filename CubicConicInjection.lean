module -- shake: keep-all

public import CubicRepresentative

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

section Triples

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def cubicTriple (a x : F) (i : Fin 3) : F × F :=
  if i = 0 then (a, x)
  else if i = 1 then (x, -a - x)
  else (-a - x, a)

omit [Fintype F] [DecidableEq F] in
theorem cubicTriple_conic
    (a x : F) (ha : a ≠ x) (hax : cubicVal a = cubicVal x)
    (i : Fin 3) :
    (cubicTriple a x i).1 ^ 2 +
      (cubicTriple a x i).1 * (cubicTriple a x i).2 +
      (cubicTriple a x i).2 ^ 2 = 1 := by
  have hconic : a ^ 2 + a * x + x ^ 2 = 1 :=
    ((cubic_value_collision_iff a x).mp hax).resolve_left ha
  fin_cases i
  · simpa [cubicTriple] using hconic
  · change x ^ 2 + x * (-a - x) + (-a - x) ^ 2 = 1
    linear_combination hconic
  · change (-a - x) ^ 2 + (-a - x) * a + a ^ 2 = 1
    linear_combination hconic

omit [Fintype F] [DecidableEq F] in
theorem cubicTriple_fst_value
    (a x : F) (ha : a ≠ x) (hax : cubicVal a = cubicVal x)
    (i : Fin 3) :
    cubicVal (cubicTriple a x i).1 = cubicVal x := by
  have hconic : a ^ 2 + a * x + x ^ 2 = 1 :=
    ((cubic_value_collision_iff a x).mp hax).resolve_left ha
  have hz : cubicVal (-a-x) = cubicVal x := by
    unfold cubicVal
    apply (cubic_value_collision_iff (-a-x) x).mpr
    right
    calc
      (-a-x)^2 + (-a-x)*x + x^2 = a^2 + a*x + x^2 := by ring
      _ = 1 := hconic
  fin_cases i <;> simp [cubicTriple, hax, hz]

omit [Fintype F] [DecidableEq F] in
theorem cubicTriple_inj_fixed_base
    (a x y : F) (hx : x ≠ a) (hy : y ≠ a)
    (i j : Fin 3)
    (h : cubicTriple a x i = cubicTriple a y j) :
    x = y ∧ i = j := by
  fin_cases i <;> fin_cases j
  all_goals
    simp only [cubicTriple] at h
  · exact ⟨(Prod.mk.inj h).2, rfl⟩
  · have hz := (Prod.mk.inj h).1
    exact (hy hz.symm).elim
  · have hz := (Prod.mk.inj h).2
    exact (hx hz).elim
  · have hz := (Prod.mk.inj h).1
    exact (hx hz).elim
  · exact ⟨(Prod.mk.inj h).1, rfl⟩
  · obtain ⟨h1,h2⟩ := Prod.mk.inj h
    have hya : y = a := by linear_combination h1 + h2
    exact (hy hya).elim
  · have hz := (Prod.mk.inj h).2
    exact (hy hz.symm).elim
  · obtain ⟨h1,h2⟩ := Prod.mk.inj h
    have hxa : x = a := by linear_combination -h1 - h2
    exact (hx hxa).elim
  · obtain ⟨h1,_⟩ := Prod.mk.inj h
    constructor
    · linear_combination -h1
    · rfl


/-- Encode every nonrepresentative x as three conic points. -/
noncomputable def cubicCode (z : F × Fin 3) : F × F :=
  cubicTriple (cubicRep (cubicVal z.1)) z.1 z.2

theorem cubicCode_mem_conic (x : F) (hx : x ∈ cubicExtra (F := F)) (i : Fin 3) :
    cubicCode (x, i) ∈ cubicConicPoints (F := F) := by
  have hneq : cubicRep (cubicVal x) ≠ x := (Finset.mem_filter.mp hx).2
  have hsame := cubicRep_is_root x
  change (cubicTriple (cubicRep (cubicVal x)) x i) ∈ cubicConicPoints
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, cubicTriple_conic _ _ hneq hsame i⟩

theorem cubicCode_inj (x y : F) (i j : Fin 3)
    (hx : x ∈ cubicExtra (F := F))
    (hy : y ∈ cubicExtra (F := F))
    (heq : cubicCode (x, i) = cubicCode (y, j)) :
    x = y ∧ i = j := by
  let a : F := cubicRep (cubicVal x)
  let b : F := cubicRep (cubicVal y)
  have hxa : x ≠ a := Ne.symm (Finset.mem_filter.mp hx).2
  have hyb : y ≠ b := Ne.symm (Finset.mem_filter.mp hy).2
  have hax : cubicVal a = cubicVal x := cubicRep_is_root x
  have hby : cubicVal b = cubicVal y := cubicRep_is_root y
  have hrootx : cubicVal (cubicCode (x, i)).1 = cubicVal x :=
    cubicTriple_fst_value a x hxa.symm hax i
  have hrooty : cubicVal (cubicCode (y, j)).1 = cubicVal y :=
    cubicTriple_fst_value b y hyb.symm hby j
  have hxy : cubicVal x = cubicVal y := by
    calc
      _ = cubicVal (cubicCode (x, i)).1 := hrootx.symm
      _ = cubicVal (cubicCode (y, j)).1 := by rw [heq]
      _ = cubicVal y := hrooty
  have hab : a = b := congrArg cubicRep hxy
  have hya : y ≠ a := by rw [hab]; exact hyb
  have hc : cubicTriple a x i = cubicTriple a y j := by
    change cubicTriple a x i = cubicTriple b y j at heq
    simpa only [← hab] using heq
  exact cubicTriple_inj_fixed_base a x y hxa hya i j hc

theorem cubicExtra_three_le_conic_card :
    3 * (cubicExtra (F := F)).card ≤ (cubicConicPoints (F := F)).card := by
  let D : Finset F := cubicExtra
  let S : Finset (F × Fin 3) := D.product Finset.univ
  have hsub : S.image cubicCode ⊆ cubicConicPoints (F := F) := by
    intro z hz
    obtain ⟨z, hzS, rfl⟩ := Finset.mem_image.mp hz
    have hx := (Finset.mem_product.mp hzS).1
    exact cubicCode_mem_conic z.1 hx z.2
  have hinj : Set.InjOn cubicCode (↑S : Set (F × Fin 3)) := by
    intro z hz w hw heq
    have hx := (Finset.mem_product.mp hz).1
    have hy := (Finset.mem_product.mp hw).1
    have ⟨hxy, hij⟩ :=
      cubicCode_inj z.1 w.1 z.2 w.2 hx hy heq
    exact Prod.ext hxy hij
  have hc : S.card ≤ (cubicConicPoints (F := F)).card := by
    calc
      S.card = (S.image cubicCode).card :=
        (Finset.card_image_of_injOn hinj).symm
      _ ≤ _ := Finset.card_le_card hsub
  change (D.product (Finset.univ : Finset (Fin 3))).card ≤
    (cubicConicPoints (F := F)).card at hc
  rw [Finset.product_eq_sprod, Finset.card_product,
    Finset.card_univ, Fintype.card_fin] at hc
  simpa only [D, mul_comm] using hc

/-- The missing classical cubic value-set lower bound, now obtained
    from elementary conic geometry and a three-to-one injection. -/
theorem cubic_value_set_lower_bound (h3 : (3 : F) ≠ 0) :
    2 * Fintype.card F ≤
      3 * ((Finset.univ : Finset F).image (fun t : F => t ^ 3 - t)).card + 1 := by
  have hconic := cubicConicPoints_card_le (F := F) h3
  have henc := cubicExtra_three_le_conic_card (F := F)
  have hpartition := cubicExtra_card_add_image (F := F)
  change (cubicExtra (F := F)).card +
     ((Finset.univ : Finset F).image (fun t : F => t ^ 3 - t)).card =
     Fintype.card F at hpartition
  omega

#print axioms cubicCode_mem_conic
#print axioms cubicCode_inj
#print axioms cubicExtra_three_le_conic_card
#print axioms cubic_value_set_lower_bound

#print axioms cubicTriple_conic
#print axioms cubicTriple_fst_value
#print axioms cubicTriple_inj_fixed_base

end Triples
end SparseDeletion
