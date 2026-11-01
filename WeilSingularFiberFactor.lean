module -- shake: keep-all

public import WeilSingularSum
public import Mathlib.Tactic.FieldSimp

@[expose] public section

namespace SparseDeletion

open Finset

attribute [local instance] Classical.propDecidable

/-!
# Explicit singular-fiber factorization for triangular square-prefix cubics

A closed algebraic identity avoids using any general theorem about
repeated roots or polynomial splitting fields. If the discriminant
parameter q(b) vanishes, the cubic factors as one double and one
simple linear factor; the complete character sum then follows from
WeilSingularSum.lean, independently of Hasse.
-/

/-- The polynomial measuring the discriminant of the cubic. -/
def triangularSingularParameter (F : Type*) [Field F] (b : F) : F :=
  15552 * b^2 + 3888 * b + 239

/-- Exact polynomial identity for all x and b in characteristic
different from 2 and 3. -/
theorem triangular_singular_factorization_identity
    {F : Type*} [Field F] (x b : F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0) :
    8 * (x * (x + 1) * (2 * x + 1) / 6 + b) + 1 -
        (8 / 3) * (x - (18 * b + 7 / 4))^2 *
          (x - (-36 * b - 5)) =
      ((x - 12 * b - 1) / 6) * triangularSingularParameter F b := by
  have h4 : (4 : F) ≠ 0 := by
    have h : (4 : F) = (2 : F)^2 := by norm_num
    rw [h]
    exact pow_ne_zero 2 h2
  have h6 : (6 : F) ≠ 0 := by
    have h : (6 : F) = 2 * 3 := by norm_num
    rw [h]
    exact mul_ne_zero h2 h3
  dsimp [triangularSingularParameter]
  field_simp [h2, h3, h4, h6]
  ring

/-- The singular cubic has a completely explicit factorization. -/
theorem triangular_singular_factorization
    {F : Type*} [Field F] (x b : F)
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hq : triangularSingularParameter F b = 0) :
    8 * (x * (x + 1) * (2 * x + 1) / 6 + b) + 1 =
      (8 / 3) * (x - (18 * b + 7 / 4))^2 *
        (x - (-36 * b - 5)) := by
  have h := triangular_singular_factorization_identity x b h2 h3
  rw [hq, mul_zero] at h
  exact sub_eq_zero.mp h

/-- Fully elementary character-sum evaluation of a singular
triangular-prefix cubic; no conditional Weil hypothesis is used. -/
theorem triangular_singular_character_sum
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (h2 : (2 : F) ≠ 0) (h3 : (3 : F) ≠ 0)
    (hchar : ringChar F ≠ 2)
    (b : F) (hq : triangularSingularParameter F b = 0) :
    (∑ x : F,
        quadraticCharFun F
          (8 * (x * (x + 1) * (2 * x + 1) / 6 + b) + 1)) =
      -(quadraticCharFun F (8 / 3)) *
        quadraticCharFun F
          ((18 * b + 7 / 4) - (-36 * b - 5)) := by
  classical
  calc
    (∑ x : F, quadraticCharFun F
        (8 * (x * (x + 1) * (2 * x + 1) / 6 + b) + 1)) =
      ∑ x : F, quadraticCharFun F
        ((8 / 3) * (x - (18 * b + 7 / 4))^2 *
          (x - (-36 * b - 5))) := by
          apply Finset.sum_congr rfl
          intro x _
          rw [triangular_singular_factorization x b h2 h3 hq]
    _ = -(quadraticCharFun F (8 / 3)) *
        quadraticCharFun F
          ((18 * b + 7 / 4) - (-36 * b - 5)) :=
      quadraticCharFun_double_root_sum F hchar
        (8 / 3) (18 * b + 7 / 4) (-36 * b - 5)

end SparseDeletion
