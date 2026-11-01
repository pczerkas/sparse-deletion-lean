module -- shake: keep-all

public import WeilSingleHypothesis

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-!
# Elementary quadratic-character identity for a singular cubic

A cubic with a repeated root has form a*(x-u)^2*(x-v).
Away from x=u, the square factor has quadratic character +1;
at x=u the character vanishes. This elementary observation
is one component of the planned unconditional singular-cubic
Weil bound. No Hasse theorem is assumed or imported here.
-/

/-- An exact pointwise reduction, valid over any finite field,
for a cubic with a repeated factor. -/
theorem quadraticCharFun_double_root_pointwise
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (a u v x : F) :
    quadraticCharFun F (a * (x-u)^2 * (x-v)) =
      if x=u then 0 else
        quadraticCharFun F a * quadraticCharFun F (x-v) := by
  classical
  by_cases hx : x = u
  · subst x
    simp
  · have hxu : x-u ≠ 0 := sub_ne_zero.mpr hx
    have hsq : quadraticCharFun F ((x-u)^2) = 1 := by
      have h := quadraticChar_sq_one' (F := F) hxu
      simpa only [quadraticChar_apply] using h
    rw [quadraticCharFun_mul, quadraticCharFun_mul, hsq]
    simp [hx]

end SparseDeletion
