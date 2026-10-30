module -- shake: keep-all

public import SparseDeletionBase

@[expose] public section

/-!
# Sparse deletion: sieve interface

The elementary definitions and lemmas live in `SparseDeletionBase`.  This
module contains only the sorry-free candidate-set interface used by the
verified proof modules.
-/

namespace SparseDeletion

noncomputable def cubicCandidates (u M : ℕ) (b : ℤ) : Finset ℕ := by
  classical
  exact (Finset.Ico u (u + M)).filter
    (fun x => TriangularInt (naturalSquareSum x + b))

end SparseDeletion
