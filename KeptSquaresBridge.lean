module -- shake: keep-all

public import RemovedSquares
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

namespace SparseDeletion

noncomputable def keptTermNat (E : Set ℕ) (k : ℕ) : ℕ := by
  classical
  exact if k ∈ E then 0 else k ^ 2

noncomputable def keptRangeNat (E : Set ℕ) (x : ℕ) : ℕ :=
  (Finset.range (x + 1)).sum (keptTermNat E)

theorem keptSquaresUpTo_eq_range (E : Set ℕ) (x : ℕ) :
    keptSquaresUpTo E x = keptRangeNat E x := by
  classical
  have hset : Finset.range (x + 1) = insert 0 (Finset.Icc 1 x) := by
    ext k
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0 : (0 : ℕ) ∉ Finset.Icc 1 x := by simp
  unfold keptRangeNat
  rw [hset, Finset.sum_insert h0]
  simp [keptSquaresUpTo, keptTermNat]

theorem keptRange_cast (E : Set ℕ) (x : ℕ) :
    (keptRangeNat E x : ℤ) = shiftedRemaining E x := by
  classical
  simp only [keptRangeNat, shiftedRemaining, naturalSquareSum, removedSquareSum,
    Nat.cast_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases h : k ∈ E
  · simp [keptTermNat, removedTerm, h]
  · simp [keptTermNat, removedTerm, h]

theorem keptSquaresUpTo_cast_eq_shiftedRemaining (E : Set ℕ) (x : ℕ) :
    (keptSquaresUpTo E x : ℤ) = shiftedRemaining E x := by
  rw [keptSquaresUpTo_eq_range, keptRange_cast]

theorem triangular_cast (s : ℕ) (h : Triangular s) : TriangularInt (s : ℤ) := by
  rcases h with ⟨m, hm⟩
  exact ⟨m, by exact_mod_cast hm⟩

theorem triangular_iff_triangularInt_cast (s : ℕ) :
    Triangular s ↔ TriangularInt (s : ℤ) := by
  constructor
  · exact triangular_cast s
  · rintro ⟨m, hm⟩
    exact ⟨m, by exact_mod_cast hm⟩

end SparseDeletion

#print axioms SparseDeletion.keptSquaresUpTo_cast_eq_shiftedRemaining
