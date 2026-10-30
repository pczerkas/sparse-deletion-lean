module -- shake: keep-all

public import SparseDeletion
public import SieveCRT31x37x41

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

theorem removedSquareSum_clean
    (E : Set ℕ) (u x : ℕ) (hu : u ≤ x)
    (hclean : ∀ k : ℕ, u < k → k ≤ x → k ∉ E) :
    removedSquareSum E x = removedSquareSum E u := by
  induction x, hu using Nat.le_induction with
  | base => rfl
  | succ n hle ih =>
    have hc : ∀ k : ℕ, u < k → k ≤ n → k ∉ E := by
      intro k h1 h2
      exact hclean k h1 (by omega)
    have hnot : n + 1 ∉ E := hclean (n + 1) (by omega) (by omega)
    rw [removedSquareSum_succ, ih hc]
    simp [removedTerm, hnot]

theorem shiftedRemaining_clean
    (E : Set ℕ) (u x : ℕ) (hu : u ≤ x)
    (hclean : ∀ k : ℕ, u < k → k ≤ x → k ∉ E) :
    shiftedRemaining E x =
      naturalSquareSum x - removedSquareSum E u := by
  unfold shiftedRemaining
  rw [removedSquareSum_clean E u x hu hclean]

noncomputable def cleanWindowCandidates (E : Set ℕ) (u : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico u (u + 47027)).filter
    (fun x => TriangularInt (shiftedRemaining E x))

/-- On a block free from deletions, all candidate values have one fixed cubic shift. -/
theorem clean_block_triangular_le_13608
    (E : Set ℕ) (u : ℕ)
    (hclean : ∀ k : ℕ, u < k → k < u + 47027 → k ∉ E) :
    (cleanWindowCandidates E u).card ≤ 13608 := by
  classical
  have hsub : cleanWindowCandidates E u ⊆
      cubicCandidates u 47027 (-removedSquareSum E u) := by
    intro x hx
    have hx' := Finset.mem_filter.mp (show x ∈ cleanWindowCandidates E u from hx)
    have hinterval : u ≤ x ∧ x < u + 47027 := Finset.mem_Ico.mp hx'.1
    apply Finset.mem_filter.mpr
    constructor
    · exact hx'.1
    · have heq : shiftedRemaining E x =
          naturalSquareSum x - removedSquareSum E u := by
        apply shiftedRemaining_clean E u x hinterval.1
        intro k h1 h2
        exact hclean k h1 (by omega)
      simpa only [heq, sub_eq_add_neg] using hx'.2
  exact (Finset.card_le_card hsub).trans (sieveCRT3_triangular_interval u _)

end SparseDeletion

#print axioms SparseDeletion.removedSquareSum_clean
#print axioms SparseDeletion.clean_block_triangular_le_13608
