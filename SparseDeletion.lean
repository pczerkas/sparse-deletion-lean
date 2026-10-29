import SparseDeletionBase

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

theorem cubicCandidates_subset (u M : ℕ) (b : ℤ) :
    cubicCandidates u M b ⊆ Finset.Ico u (u + M) := by
  classical
  simp [cubicCandidates]

theorem cubicCandidates_card_le (u M : ℕ) (b : ℤ) :
    (cubicCandidates u M b).card ≤ M := by
  classical
  calc
    (cubicCandidates u M b).card ≤ (Finset.Ico u (u + M)).card :=
      Finset.card_le_card (cubicCandidates_subset u M b)
    _ = M := by simp

theorem uniformCubicSieve_zero :
    ∃ M : ℕ, 0 < M ∧
      ∀ (u : ℕ) (b : ℤ),
        4 ^ (0 : ℕ) * (cubicCandidates u M b).card ≤ 3 ^ (0 : ℕ) * M := by
  refine ⟨1, by decide, ?_⟩
  intro u b
  simpa using cubicCandidates_card_le u 1 b

end SparseDeletion
