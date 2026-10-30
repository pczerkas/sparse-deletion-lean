module -- shake: keep-all

public import CubicConicExact

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

section Count
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def conicQuadratic (t : F) : F := 1 + t + t ^ 2

def conicSlopeRoots : Finset F :=
  Finset.univ.filter (fun t => conicQuadratic t = 0)

def conicGoodSlopes : Finset F :=
  Finset.univ.filter (fun t => t ≠ -2 ∧ conicQuadratic t ≠ 0)

def conicPointOfSlope (t : F) : F × F :=
  let u := -(2+t) / conicQuadratic t
  (1 + u, t*u)

omit [Fintype F] [DecidableEq F] in
theorem conic_point_of_slope (t : F)
    (ht : t ≠ -2) (hq : conicQuadratic t ≠ 0) :
    let z := conicPointOfSlope t
    z.1 ^ 2 + z.1*z.2 + z.2 ^ 2 = 1 ∧
    z.1 ≠ 1 ∧ z.2 / (z.1-1) = t := by
  dsimp [conicPointOfSlope]
  have hnum : (2 : F) + t ≠ 0 := by
    intro he
    apply ht
    linear_combination he
  have hu : -(2+t) / conicQuadratic t ≠ 0 := div_ne_zero (neg_ne_zero.mpr hnum) hq
  constructor
  · have hmul : (1 + t + t^2) * (-(2+t) / conicQuadratic t) = -(2+t) := by
      rw [show 1 + t + t^2 = conicQuadratic t from rfl]
      field_simp
    calc
      (1 + -(2+t) / conicQuadratic t)^2 +
          (1 + -(2+t) / conicQuadratic t) *
          (t * (-(2+t) / conicQuadratic t)) +
          (t * (-(2+t) / conicQuadratic t))^2 =
          1 + (-(2+t) / conicQuadratic t) *
            ((2+t) + (1+t+t^2) * (-(2+t) / conicQuadratic t)) := by ring
      _ = 1 := by rw [hmul]; ring
  constructor
  · intro he
    have hz : -(2+t) / conicQuadratic t = 0 := by
      linear_combination he
    exact hu hz
  · have hcancel : t * (-(2+t) / conicQuadratic t) /
      ((1 + -(2+t) / conicQuadratic t) - 1) = t := by
      simpa only [add_sub_cancel_left] using
        (mul_div_cancel_right₀ t hu)
    exact hcancel


omit [Fintype F] [DecidableEq F] in
theorem conic_slope_quadratic_ne_zero (h3 : (3 : F) ≠ 0)
    (x y : F) (hx : x ≠ 1)
    (hxy : x^2 + x*y + y^2 = 1) :
    conicQuadratic (y / (x-1)) ≠ 0 := by
  let t : F := y / (x-1)
  let u : F := x-1
  have hu : u ≠ 0 := sub_ne_zero.mpr hx
  have hy : t*u = y := conic_slope_coordinates x y hx
  have hqx : (1+u)^2 + (1+u)*(t*u) + (t*u)^2 = 1 := by
    convert hxy using 1
    simp [u, hy]
  have hlin := (mul_eq_zero.mp ((conic_line_factor t u).mp hqx)).resolve_left hu
  intro hzero
  have htwo : (2 : F) + t = 0 := by
    have hz : 1 + t + t^2 = 0 := hzero
    rw [hz] at hlin
    simpa using hlin
  exact (conic_slope_ne_tangent h3 x y hx hxy)
    (by linear_combination htwo)

theorem conic_good_slopes_eq_image (h3 : (3 : F) ≠ 0) :
    conicGoodSlopes (F := F) =
      ((cubicConicPoints (F := F)).filter (fun z => z.1 ≠ 1)).image
        (fun z => z.2 / (z.1 - 1)) := by
  ext t
  constructor
  · intro ht
    have ht' := (Finset.mem_filter.mp ht).2
    obtain ⟨ht2, hq⟩ := ht'
    let z := conicPointOfSlope t
    have hz := conic_point_of_slope t ht2 hq
    refine Finset.mem_image.mpr ⟨z, ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz.1⟩, hz.2.1⟩
    · exact hz.2.2
  · intro ht
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp ht
    have hx : z.1 ≠ 1 := (Finset.mem_filter.mp hz).2
    have hc : z.1^2 + z.1*z.2 + z.2^2 = 1 :=
      (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨
      conic_slope_ne_tangent h3 z.1 z.2 hx hc,
      conic_slope_quadratic_ne_zero h3 z.1 z.2 hx hc⟩⟩

theorem conic_nonvertical_card_eq_good (h3 : (3 : F) ≠ 0) :
    ((cubicConicPoints (F := F)).filter (fun z => z.1 ≠ 1)).card =
      (conicGoodSlopes (F := F)).card := by
  let A := (cubicConicPoints (F := F)).filter (fun z => z.1 ≠ 1)
  let slope : F × F → F := fun z => z.2 / (z.1-1)
  have hinj : Set.InjOn slope A := by
    intro z hz w hw he
    have hx := (Finset.mem_filter.mp hz).2
    have hx' := (Finset.mem_filter.mp hw).2
    have hc := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
    have hc' := (Finset.mem_filter.mp (Finset.mem_filter.mp hw).1).2
    obtain ⟨he1,he2⟩ :=
      conic_slope_unique h3 z.1 z.2 w.1 w.2 hx hx' hc hc' he
    exact Prod.ext he1 he2
  have h := conic_good_slopes_eq_image (F := F) h3
  change conicGoodSlopes = A.image slope at h
  have hcard := congrArg Finset.card h
  rw [Finset.card_image_of_injOn hinj] at hcard
  exact hcard.symm


theorem conic_vertical_card_two :
    ((cubicConicPoints (F := F)).filter (fun z => z.1 = 1)).card = 2 := by
  let B := (cubicConicPoints (F := F)).filter (fun z => z.1 = 1)
  have hB : B = ({(1, (0 : F)), (1, (-1 : F))} : Finset (F × F)) := by
    ext z
    constructor
    · intro hz
      have hx : z.1 = 1 := (Finset.mem_filter.mp hz).2
      have hc : z.1^2 + z.1*z.2 + z.2^2 = 1 :=
        (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
      have hm : z.2 * (z.2 + 1) = 0 := by
        have heq : z.1^2 + z.1*z.2 + z.2^2 - 1 = 0 :=
          sub_eq_zero.mpr hc
        rw [hx] at heq
        linear_combination heq
      rcases mul_eq_zero.mp hm with h0 | h1
      · simp [Prod.ext_iff, hx, h0]
      · have hminus : z.2 = -1 := by linear_combination h1
        simp [Prod.ext_iff, hx, hminus]
    · intro hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with hz | hz
      · subst z
        simp [B, cubicConicPoints]
      · subst z
        simp [B, cubicConicPoints]
  change B.card = 2
  rw [hB]
  simp

theorem conic_good_card_add_roots (h3 : (3 : F) ≠ 0) :
    (conicGoodSlopes (F := F)).card +
      (conicSlopeRoots (F := F)).card + 1 = Fintype.card F := by
  have hnotroot : conicQuadratic (-2 : F) ≠ 0 := by
    change (1 : F) + (-2 : F) + (-2 : F)^2 ≠ 0
    convert h3 using 1; ring
  let T : Finset F := Finset.univ.erase (-2)
  have hgood : T.filter (fun t => conicQuadratic t ≠ 0) =
      conicGoodSlopes (F := F) := by
    ext t
    simp only [T, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true, true_and, conicGoodSlopes]
  have hbad : T.filter (fun t => ¬conicQuadratic t ≠ 0) =
      conicSlopeRoots (F := F) := by
    ext t
    simp only [T, Finset.mem_filter, Finset.mem_erase, Finset.mem_univ,
      and_true, true_and, not_not, conicSlopeRoots]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨fun he => hnotroot (he ▸ h), h⟩
  have hpart := Finset.card_filter_add_card_filter_not
    (s := T) (fun t => conicQuadratic t ≠ 0)
  rw [hgood, hbad] at hpart
  have hT : T.card + 1 = Fintype.card F := by
    dsimp [T]
    rw [Finset.card_erase_of_mem (Finset.mem_univ (-2 : F))]
    have hpos : 0 < Fintype.card F := Fintype.card_pos
    simp only [Finset.card_univ]
    omega
  omega

/-- Exact affine point count of the conic, in terms of roots of t²+t+1.
Only characteristic three is excluded. -/
theorem cubicConicPoints_card_add_quadratic_roots (h3 : (3 : F) ≠ 0) :
    (cubicConicPoints (F := F)).card +
      (conicSlopeRoots (F := F)).card = Fintype.card F + 1 := by
  let C : Finset (F × F) := cubicConicPoints
  let A := C.filter (fun z => z.1 ≠ 1)
  let B := C.filter (fun z => z.1 = 1)
  have hpart : A.card + B.card = C.card := by
    simpa only [A, B, not_not] using
      (Finset.card_filter_add_card_filter_not
        (s := C) (fun z : F × F => z.1 ≠ 1))
  have hA := conic_nonvertical_card_eq_good (F := F) h3
  have hB := conic_vertical_card_two (F := F)
  have hgood := conic_good_card_add_roots (F := F) h3
  rw [hA, hB] at hpart
  dsimp [C] at hpart
  omega

/-- The corresponding exact cubic value-set identity in terms of
the roots of t²+t+1. -/
theorem cubic_value_set_exact_with_quadratic_roots (h3 : (3 : F) ≠ 0) :
    3 * ((Finset.univ : Finset F).image (fun t : F => t ^ 3 - t)).card =
      2 * Fintype.card F - 1 + (conicSlopeRoots (F := F)).card := by
  have h := cubic_value_set_conic_exact (F := F)
  have hc := cubicConicPoints_card_add_quadratic_roots (F := F) h3
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  omega

#print axioms cubicConicPoints_card_add_quadratic_roots
#print axioms cubic_value_set_exact_with_quadratic_roots


omit [Fintype F] [DecidableEq F] in
theorem conic_quadratic_roots_cases (t s : F)
    (ht : conicQuadratic t = 0) (hs : conicQuadratic s = 0) :
    s = t ∨ s = -1-t := by
  have hdiff : (s-t)*(s+t+1) = 0 := by
    have heq : conicQuadratic s - conicQuadratic t = 0 := by rw [hs, ht]; ring
    unfold conicQuadratic at heq
    linear_combination heq
  rcases mul_eq_zero.mp hdiff with h1 | h2
  · exact Or.inl (sub_eq_zero.mp h1)
  · exact Or.inr (by linear_combination h2)

omit [Fintype F] [DecidableEq F] in
theorem conic_quadratic_other_root (t : F)
    (ht : conicQuadratic t = 0) :
    conicQuadratic (-1-t) = 0 := by
  unfold conicQuadratic at *
  linear_combination ht

omit [Fintype F] [DecidableEq F] in
theorem conic_quadratic_other_ne (h3 : (3 : F) ≠ 0)
    (t : F) (ht : conicQuadratic t = 0) :
    -1-t ≠ t := by
  intro he
  have hlin : (2 : F)*t+1 = 0 := by linear_combination -he
  have hthree : (3 : F) = 0 := by
    have hfour : (4 : F)*conicQuadratic t -
        ((2 : F)*t+1)^2 = 3 := by
      unfold conicQuadratic
      ring
    rw [ht, hlin] at hfour
    linear_combination -hfour
  exact h3 hthree

/-- The quadratic t²+t+1 has either no roots or exactly two,
in any finite field of characteristic different from three. -/
theorem conic_quadratic_roots_card_eq_zero_or_two (h3 : (3 : F) ≠ 0) :
    (conicSlopeRoots (F := F)).card = 0 ∨
    (conicSlopeRoots (F := F)).card = 2 := by
  by_cases hne : (conicSlopeRoots (F := F)).Nonempty
  · obtain ⟨t, ht⟩ := hne
    have hroot : conicQuadratic t = 0 := (Finset.mem_filter.mp ht).2
    have heq : conicSlopeRoots (F := F) = {t, -1-t} := by
      ext s
      constructor
      · intro hs
        have hsroot : conicQuadratic s = 0 := (Finset.mem_filter.mp hs).2
        rcases conic_quadratic_roots_cases t s hroot hsroot with h1 | h2
        · simp [h1]
        · simp [h2]
      · intro hs
        simp only [Finset.mem_insert, Finset.mem_singleton] at hs
        rcases hs with h1 | h2
        · subst s
          exact ht
        · subst s
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
            conic_quadratic_other_root t hroot⟩
    right
    rw [heq]
    have hneq : t ≠ -1-t := (conic_quadratic_other_ne h3 t hroot).symm
    simp [hneq]
  · left
    exact Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hne)


/-- In the cardinality class 1 modulo 3, the conic has q-1 points. -/
theorem cubicConicPoints_card_of_mod_three_one (h3 : (3 : F) ≠ 0)
    (hq : Fintype.card F % 3 = 1) :
    (cubicConicPoints (F := F)).card + 1 = Fintype.card F := by
  have hc := cubicConicPoints_card_add_quadratic_roots (F := F) h3
  have hr := conic_quadratic_roots_card_eq_zero_or_two (F := F) h3
  have hv := cubic_value_set_conic_exact (F := F)
  rcases hr with h0 | h2 <;> omega

/-- In the cardinality class 2 modulo 3, the conic has q+1 points. -/
theorem cubicConicPoints_card_of_mod_three_two (h3 : (3 : F) ≠ 0)
    (hq : Fintype.card F % 3 = 2) :
    (cubicConicPoints (F := F)).card = Fintype.card F + 1 := by
  have hc := cubicConicPoints_card_add_quadratic_roots (F := F) h3
  have hr := conic_quadratic_roots_card_eq_zero_or_two (F := F) h3
  have hv := cubic_value_set_conic_exact (F := F)
  rcases hr with h0 | h2 <;> omega

/-- Exact classical cubic value-set count when q = 1 mod 3. -/
theorem cubic_value_set_card_of_mod_three_one (h3 : (3 : F) ≠ 0)
    (hq : Fintype.card F % 3 = 1) :
    ((Finset.univ : Finset F).image (fun t : F => t ^ 3 - t)).card =
      (2 * Fintype.card F + 1) / 3 := by
  have hc := cubicConicPoints_card_of_mod_three_one (F := F) h3 hq
  have hv := cubic_value_set_conic_exact (F := F)
  omega

/-- Exact classical cubic value-set count when q = 2 mod 3. -/
theorem cubic_value_set_card_of_mod_three_two (h3 : (3 : F) ≠ 0)
    (hq : Fintype.card F % 3 = 2) :
    ((Finset.univ : Finset F).image (fun t : F => t ^ 3 - t)).card =
      (2 * Fintype.card F - 1) / 3 := by
  have hc := cubicConicPoints_card_of_mod_three_two (F := F) h3 hq
  have hv := cubic_value_set_conic_exact (F := F)
  omega

#print axioms cubicConicPoints_card_of_mod_three_one
#print axioms cubicConicPoints_card_of_mod_three_two
#print axioms cubic_value_set_card_of_mod_three_one
#print axioms cubic_value_set_card_of_mod_three_two


/-- The classical exact formula over prime fields, for all primes at least five. -/
theorem cubic_value_set_card_prime (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) :
    let V := ((Finset.univ : Finset (ZMod p)).image
      (fun t : ZMod p => t ^ 3 - t)).card
    (p % 3 = 1 ∧ V = (2*p+1)/3) ∨
    (p % 3 = 2 ∧ V = (2*p-1)/3) := by
  dsimp
  have h3 : (3 : ZMod p) ≠ 0 := by
    intro hzero
    have hd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hzero
    have hle := Nat.le_of_dvd (by decide : 0 < 3) hd
    omega
  have hnot : p % 3 ≠ 0 := by
    intro hzero
    have hd : 3 ∣ p := Nat.dvd_of_mod_eq_zero hzero
    have heq : p = 3 := (Fact.out : p.Prime).dvd_iff_eq (by decide : 3 ≠ 1) |>.mp hd
    omega
  have hmod : p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hmod with h1 | h2
  · left
    refine ⟨h1, ?_⟩
    have h := cubic_value_set_card_of_mod_three_one (F := ZMod p) h3
      (by simpa only [ZMod.card] using h1)
    simpa only [ZMod.card] using h
  · right
    refine ⟨h2, ?_⟩
    have h := cubic_value_set_card_of_mod_three_two (F := ZMod p) h3
      (by simpa only [ZMod.card] using h2)
    simpa only [ZMod.card] using h

#print axioms cubic_value_set_card_prime

end Count
end SparseDeletion
