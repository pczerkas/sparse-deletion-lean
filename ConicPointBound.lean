module -- shake: keep-all

public import CubicCollisionBridge

@[expose] public section

namespace SparseDeletion

open Finset

attribute [local instance] Classical.propDecidable

section ConicBounds
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def cubicConicPoints : Finset (F × F) :=
  Finset.univ.filter (fun z => z.1 ^ 2 + z.1 * z.2 + z.2 ^ 2 = 1)

theorem conic_slope_coordinates (x y : F) (hx : x ≠ 1) :
    (y / (x - 1)) * (x - 1) = y := by
  have h : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  field_simp

theorem conic_slope_ne_tangent (h3 : (3 : F) ≠ 0) 
    (x y : F) (hx : x ≠ 1)
    (hxy : x ^ 2 + x * y + y ^ 2 = 1) :
    y / (x - 1) ≠ -2 := by
  let t : F := y / (x - 1)
  let u : F := x - 1
  have hu : u ≠ 0 := sub_ne_zero.mpr hx
  have hy : t * u = y := conic_slope_coordinates x y hx
  have hqx : (1 + u) ^ 2 + (1 + u) * (t * u) + (t * u) ^ 2 = 1 := by
    convert hxy using 1; simp [u, hy]
  have hfac := (conic_line_factor t u).mp hqx
  have hlin := (mul_eq_zero.mp hfac).resolve_left hu
  intro ht
  change t = -2 at ht
  have hmul : (3 : F) * u = 0 := by
    calc
      _ = (1 + t + t ^ 2) * u + (2 + t) := by rw [ht]; ring
      _ = 0 := hlin
  exact h3 ((mul_eq_zero.mp hmul).resolve_right hu)

theorem conic_slope_unique (h3 : (3 : F) ≠ 0)
    (x y x' y' : F)
    (hx : x ≠ 1) (hx' : x' ≠ 1)
    (hxy : x ^ 2 + x * y + y ^ 2 = 1)
    (hx'y' : x' ^ 2 + x' * y' + y' ^ 2 = 1)
    (hslope : y / (x - 1) = y' / (x' - 1)) :
    x = x' ∧ y = y' := by
  let t : F := y / (x - 1)
  let u : F := x - 1
  let v : F := x' - 1
  have hu : u ≠ 0 := sub_ne_zero.mpr hx
  have hv : v ≠ 0 := sub_ne_zero.mpr hx'
  have hy : t * u = y := conic_slope_coordinates x y hx
  have hy' : t * v = y' := by
    rw [show t = y' / (x' - 1) from hslope]
    exact conic_slope_coordinates x' y' hx'
  have hqu : (1 + u) ^ 2 + (1 + u) * (t * u) + (t * u) ^ 2 = 1 := by
    convert hxy using 1; simp [u, hy]
  have hqv : (1 + v) ^ 2 + (1 + v) * (t * v) + (t * v) ^ 2 = 1 := by
    convert hx'y' using 1; simp [v, hy']
  have huv : u = v := conic_line_unique h3 t u v hu hv hqu hqv
  constructor
  · dsimp [u, v] at huv
    linear_combination huv
  · rw [← hy, ← hy', huv]


/-- The conic x² + xy + y² = 1 has at most |F|+1 affine points
    over any finite field of characteristic other than three. -/
theorem cubicConicPoints_card_le (h3 : (3 : F) ≠ 0) :
    (cubicConicPoints (F := F)).card ≤ Fintype.card F + 1 := by
  let C : Finset (F × F) := cubicConicPoints
  let A : Finset (F × F) := C.filter (fun z => z.1 ≠ 1)
  let B : Finset (F × F) := C.filter (fun z => z.1 = 1)
  let slope : F × F → F := fun z => z.2 / (z.1 - 1)
  have hinj : Set.InjOn slope A := by
    intro z hz w hw he
    obtain ⟨hzC, hzx⟩ := Finset.mem_filter.mp hz
    obtain ⟨hwC, hwx⟩ := Finset.mem_filter.mp hw
    have hzc := (Finset.mem_filter.mp hzC).2
    have hwc := (Finset.mem_filter.mp hwC).2
    obtain ⟨hx, hy⟩ :=
      conic_slope_unique h3 z.1 z.2 w.1 w.2 hzx hwx hzc hwc he
    exact Prod.ext hx hy
  have hslope : slope (1, 0) = (0 : F) := by simp [slope]
  have hmissing : (-(2 : F)) ∉ A.image slope := by
    intro hm
    obtain ⟨z, hz, he⟩ := Finset.mem_image.mp hm
    have hzx := (Finset.mem_filter.mp hz).2
    have hzc := (Finset.mem_filter.mp (Finset.mem_filter.mp hz).1).2
    exact (conic_slope_ne_tangent h3 z.1 z.2 hzx hzc) he
  have hAsub : A.image slope ⊆ (Finset.univ : Finset F).erase (-2) := by
    intro t ht
    exact Finset.mem_erase.mpr
      ⟨by
        intro he
        exact hmissing (he ▸ ht), Finset.mem_univ _⟩
  have hA : A.card ≤ Fintype.card F - 1 := by
    have hc := Finset.card_le_card hAsub
    rw [Finset.card_erase_of_mem (Finset.mem_univ (-2 : F))] at hc
    simpa only [Finset.card_univ, Finset.card_image_of_injOn hinj] using hc
  have hBsub : B ⊆ ({(1, (0 : F)), (1, (-1 : F))} : Finset (F × F)) := by
    intro z hz
    obtain ⟨hzC, hzx⟩ := Finset.mem_filter.mp hz
    have hzc := (Finset.mem_filter.mp hzC).2
    have hm : z.2 * (z.2 + 1) = 0 := by
      have heq : z.1 ^ 2 + z.1 * z.2 + z.2 ^ 2 - 1 = 0 :=
        sub_eq_zero.mpr hzc
      rw [hzx] at heq
      linear_combination heq
    rcases mul_eq_zero.mp hm with h0 | h1
    · simp [Prod.ext_iff, hzx, h0]
    · have hminus : z.2 = -1 := by linear_combination h1
      simp [Prod.ext_iff, hzx, hminus]
  have hB : B.card ≤ 2 := by
    have hc := Finset.card_le_card hBsub
    have hpair : ({(1, (0 : F)), (1, (-1 : F))} : Finset (F × F)).card ≤ 2 := by
      simp
    omega
  have hpartition : A.card + B.card = C.card := by
    simpa only [A, B, not_not] using
      (Finset.card_filter_add_card_filter_not
        (s := C) (fun z : F × F => z.1 ≠ 1))
  have hpos : 0 < Fintype.card F := Fintype.card_pos
  dsimp [C] at hpartition ⊢
  omega

#print axioms cubicConicPoints_card_le

#print axioms conic_slope_ne_tangent
#print axioms conic_slope_unique

end ConicBounds

end SparseDeletion
