module -- shake: keep-all

public import SparseDeletionBase

@[expose] public section

namespace SparseDeletion

noncomputable def removedTerm (E : Set ℕ) (k : ℕ) : ℤ := by
  classical
  exact if k ∈ E then (k : ℤ) ^ 2 else 0

noncomputable def removedSquareSum (E : Set ℕ) (x : ℕ) : ℤ := by
  classical
  exact (Finset.range (x + 1)).sum
    (fun k => removedTerm E k)

noncomputable def shiftedRemaining (E : Set ℕ) (x : ℕ) : ℤ :=
  naturalSquareSum x - removedSquareSum E x

theorem removedSquareSum_succ (E : Set ℕ) (x : ℕ) :
    removedSquareSum E (x + 1) =
      removedSquareSum E x +
        removedTerm E (x + 1) := by
  classical
  simp [removedSquareSum, Finset.sum_range_succ]

end SparseDeletion
