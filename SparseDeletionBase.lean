import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Basic definitions and elementary lemmas for the sparse-deletion theorem

This module contains the sorry-free foundational layer used by the verified
end-to-end proof.  The proof-specific arguments are developed in the modules
that import it.
-/

open Filter

namespace SparseDeletion

def Triangular (s : ℕ) : Prop :=
  ∃ m : ℕ, 2 * s = m * (m + 1)

theorem triangular_iff_odd_square (s : ℕ) :
    Triangular s ↔ ∃ m : ℕ, (2 * m + 1) ^ 2 = 8 * s + 1 := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    nlinarith
  · rintro ⟨m, hm⟩
    refine ⟨m, ?_⟩
    nlinarith

def prefixSquares (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  (Finset.range n).sum (fun i => (a i) ^ 2)

theorem prefixSquares_succ (a : ℕ → ℕ) (n : ℕ) :
    prefixSquares a (n + 1) = prefixSquares a n + (a n) ^ 2 := by
  simp [prefixSquares, Finset.sum_range_succ]

noncomputable def countUpTo (P : Set ℕ) (X : ℕ) : ℕ := by
  classical
  exact ((Finset.range X).filter (fun x => x ∈ P)).card

def HasDensityZero (P : Set ℕ) : Prop :=
  Tendsto (fun X : ℕ => (countUpTo P X : ℝ) / (X : ℝ))
    atTop (nhds (0 : ℝ))

noncomputable def keptSquaresUpTo (E : Set ℕ) (X : ℕ) : ℕ := by
  classical
  exact (Finset.Icc 1 X).sum (fun k => if k ∈ E then 0 else k ^ 2)

noncomputable def keptNth (E : Set ℕ) (n : ℕ) : ℕ :=
  Nat.nth (fun x => 0 < x ∧ x ∉ E) n

noncomputable def keptIndexPrefix (E : Set ℕ) (n : ℕ) : ℕ :=
  prefixSquares (keptNth E) n

def naturalSquareSum (X : ℕ) : ℤ :=
  (Finset.range (X + 1)).sum (fun k => (k : ℤ) ^ 2)

theorem naturalSquareSum_formula (X : ℕ) :
    6 * naturalSquareSum X =
      (X : ℤ) * ((X : ℤ) + 1) * (2 * (X : ℤ) + 1) := by
  induction X with
  | zero =>
      norm_num [naturalSquareSum]
  | succ n ih =>
      have hs : naturalSquareSum (n + 1) =
          naturalSquareSum n + ((n + 1 : ℕ) : ℤ) ^ 2 := by
        simp [naturalSquareSum, Finset.sum_range_succ]
      rw [hs]
      push_cast
      nlinarith [ih]

theorem naturalSquareSum_succ (x : ℕ) :
    naturalSquareSum (x + 1) = naturalSquareSum x + ((x + 1 : ℕ) : ℤ) ^ 2 := by
  simp [naturalSquareSum, Finset.sum_range_succ]

theorem naturalSquareSum_cubic (x : ℕ) :
    6 * naturalSquareSum x = (x : ℤ) * ((x : ℤ) + 1) * (2 * (x : ℤ) + 1) := by
  induction x with
  | zero => norm_num [naturalSquareSum]
  | succ n ih =>
    rw [naturalSquareSum_succ]
    push_cast
    nlinarith [ih]

def TriangularInt (s : ℤ) : Prop :=
  ∃ m : ℕ, 2 * s = (m : ℤ) * (m + 1)

end SparseDeletion
