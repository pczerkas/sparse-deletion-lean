module -- shake: keep-all

public import QuantitativeHalfRate
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

@[expose] public section

namespace SparseDeletion

open Finset Real

attribute [local instance] Classical.propDecidable

/-!
# Square residue counts as quadratic character sums

This unconditional, finite combinatorial identity is the first bridge
toward a Weil-based improvement of the local modular sieve.

Important: this module does NOT assert Weil's deep character-sum bound.
It only proves the implication from an explicit character-sum upper
bound and a root-count bound to the local contraction 3/4.
-/

/-- Pointwise identity: a zero is simultaneously a square and a
root, while nonzero arguments have quadratic character ±1. -/
private theorem double_square_indicator_eq_char (F : Type*)
    [Field F] [Fintype F] [DecidableEq F] (z : F) :
    (2 : ℤ) * (if IsSquare z then 1 else 0) =
      1 + quadraticCharFun F z + (if z = 0 then 1 else 0) := by
  by_cases hz : z = 0
  · subst z
    simp [quadraticCharFun]
  · by_cases hs : IsSquare z
    · simp [quadraticCharFun, hz, hs]
    · simp [quadraticCharFun, hz, hs]

/-- Exact character-count identity, valid for *any* function on any
finite field; it does not require a Weil or Hasse theorem. -/
theorem square_pass_character_identity (F : Type*)
    [Field F] [Fintype F] [DecidableEq F] (f : F → F) :
    (2 : ℤ) *
      (((Finset.univ : Finset F).filter (fun x => IsSquare (f x))).card : ℤ) =
    (Fintype.card F : ℤ) +
      (∑ x : F, quadraticCharFun F (f x)) +
      (((Finset.univ : Finset F).filter (fun x => f x = 0)).card : ℤ) := by
  classical
  have hpass :
      (∑ x : F, if IsSquare (f x) then (1 : ℤ) else 0) =
      (((Finset.univ : Finset F).filter (fun x => IsSquare (f x))).card : ℤ) := by
    simpa using
      (Finset.sum_boole (fun x : F => IsSquare (f x))
        (Finset.univ : Finset F) : _)
  have hzero :
      (∑ x : F, if f x = 0 then (1 : ℤ) else 0) =
      (((Finset.univ : Finset F).filter (fun x => f x = 0)).card : ℤ) := by
    simpa using
      (Finset.sum_boole (fun x : F => f x = 0)
        (Finset.univ : Finset F) : _)
  calc
    (2 : ℤ) *
      (((Finset.univ : Finset F).filter (fun x => IsSquare (f x))).card : ℤ) =
        2 * (∑ x : F, if IsSquare (f x) then (1 : ℤ) else 0) := by rw [hpass]
    _ = ∑ x : F, (2 : ℤ) * (if IsSquare (f x) then 1 else 0) := by
      rw [Finset.mul_sum]
    _ = ∑ x : F, (1 + quadraticCharFun F (f x) +
        (if f x = 0 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro x hx
      exact double_square_indicator_eq_char F (f x)
    _ = (Fintype.card F : ℤ) +
        (∑ x : F, quadraticCharFun F (f x)) +
        (((Finset.univ : Finset F).filter (fun x => f x = 0)).card : ℤ) := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hzero]
      simp

/-- A fully formal elementary bridge: for primes p≥37, a character
bias ≤2√p and at most three zeros imply at most 3p/4 square passes.

The deep Weil bound is *a hypothesis*, not an axiom or a theorem here. -/
theorem three_quarters_of_character_bound
    (p : ℕ) [Fact p.Prime] (hp : 37 ≤ p) (f : ZMod p → ZMod p)
    (hchar :
      (((∑ x : ZMod p, quadraticCharFun (ZMod p) (f x)) : ℤ) : ℝ) ≤
        2 * Real.sqrt (p : ℝ))
    (hzeros :
      ((Finset.univ : Finset (ZMod p)).filter (fun x => f x = 0)).card ≤ 3) :
    4 * ((Finset.univ : Finset (ZMod p)).filter
      (fun x => IsSquare (f x))).card ≤ 3 * p := by
  classical
  have hid := square_pass_character_identity (ZMod p) f
  rw [ZMod.card] at hid
  have hcast :
      (2 : ℝ) * (((Finset.univ : Finset (ZMod p)).filter
          (fun x => IsSquare (f x))).card : ℝ) =
        (p : ℝ) +
          (((∑ x : ZMod p, quadraticCharFun (ZMod p) (f x)) : ℤ) : ℝ) +
          (((Finset.univ : Finset (ZMod p)).filter
            (fun x => f x = 0)).card : ℝ) := by
    exact_mod_cast hid
  have hpR : (37 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
  have hsqrt : (Real.sqrt (p : ℝ)) ^ 2 = (p : ℝ) :=
    Real.sq_sqrt hp0
  have hroot0 : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hroot6 : (6 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    nlinarith
  have hextra :
      (0 : ℝ) ≤
        (Real.sqrt (p : ℝ) - 6) * Real.sqrt (p : ℝ) :=
    mul_nonneg (by linarith) hroot0
  have hzeror :
      (((Finset.univ : Finset (ZMod p)).filter
        (fun x => f x = 0)).card : ℝ) ≤ 3 := by
    exact_mod_cast hzeros
  have hresult :
      (4 : ℝ) * (((Finset.univ : Finset (ZMod p)).filter
        (fun x => IsSquare (f x))).card : ℝ) ≤ 3 * (p : ℝ) := by
    nlinarith [hcast, hchar, hzeror, hextra, hroot6]
  exact_mod_cast hresult

end SparseDeletion
