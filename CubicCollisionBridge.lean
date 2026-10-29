import MainExactValueReduction

namespace SparseDeletion

/-- Cubic value collisions reduce to the affine conic
    x² + xy + y² = 1. This is the key algebraic identity
    for an elementary proof of the remaining value-set bound. -/
theorem cubic_value_collision_iff
    {F : Type*} [Field F] (x y : F) :
    x ^ 3 - x = y ^ 3 - y ↔
      x = y ∨ x ^ 2 + x * y + y ^ 2 = 1 := by
  have hfactor :
      (x ^ 3 - x) - (y ^ 3 - y) =
        (x - y) * (x ^ 2 + x * y + y ^ 2 - 1) := by
    ring
  have hiff :
      (x ^ 3 - x = y ^ 3 - y) ↔
        (x - y) * (x ^ 2 + x * y + y ^ 2 - 1) = 0 := by
    rw [← sub_eq_zero, hfactor]
  simpa only [hiff, mul_eq_zero, sub_eq_zero]

/-- Parameterize lines through the conic point (1,0), using
    (x,y)=(1+u,t*u). The conic equation becomes linear in u
    after factoring off the already-known root u=0. -/
theorem conic_line_factor
    {F : Type*} [Field F] (t u : F) :
    (1 + u) ^ 2 + (1 + u) * (t * u) + (t * u) ^ 2 = 1 ↔
      u * ((1 + t + t ^ 2) * u + (2 + t)) = 0 := by
  have h : (1 + u) ^ 2 + (1 + u) * (t * u) + (t * u) ^ 2 - 1 =
      u * ((1 + t + t ^ 2) * u + (2 + t)) := by
    ring
  rw [← sub_eq_zero, h]

/-- Two non-base points of the conic on the same line through (1,0)
    must coincide, provided the characteristic is not three. -/
theorem conic_line_unique
    {F : Type*} [Field F] (h3 : (3 : F) ≠ 0)
    (t u v : F) (hu : u ≠ 0) (hv : v ≠ 0)
    (hqu : (1 + u) ^ 2 + (1 + u) * (t * u) + (t * u) ^ 2 = 1)
    (hqv : (1 + v) ^ 2 + (1 + v) * (t * v) + (t * v) ^ 2 = 1) :
    u = v := by
  have hu1 : (1 + t + t ^ 2) * u + (2 + t) = 0 :=
    (mul_eq_zero.mp ((conic_line_factor t u).mp hqu)).resolve_left hu
  have hv1 : (1 + t + t ^ 2) * v + (2 + t) = 0 :=
    (mul_eq_zero.mp ((conic_line_factor t v).mp hqv)).resolve_left hv
  have hcoeff : (1 + t + t ^ 2) ≠ 0 := by
    intro hz
    have ht : 2 + t = 0 := by simpa only [hz, zero_mul, zero_add] using hu1
    have htvalue : t = -2 := by linear_combination ht
    rw [htvalue] at hz
    have hthree : (3 : F) = 0 := by linear_combination hz
    exact h3 hthree
  have heq : (1 + t + t ^ 2) * u = (1 + t + t ^ 2) * v := by
    linear_combination hu1 - hv1
  exact (mul_left_cancel₀ hcoeff) heq

#print axioms conic_line_unique
#print axioms conic_line_factor
#print axioms cubic_value_collision_iff

end SparseDeletion
