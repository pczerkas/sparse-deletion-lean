module -- shake: keep-all

public import KeptSquaresBridge

@[expose] public section

namespace SparseDeletion

def keptPred (E : Set ℕ) (x : ℕ) : Prop :=
  0 < x ∧ x ∉ E

noncomputable def keptCount (E : Set ℕ) (x : ℕ) : ℕ := by
  classical
  exact Nat.count (keptPred E) x

theorem keptNth_eq_nth (E : Set ℕ) (n : ℕ) :
    keptNth E n = Nat.nth (keptPred E) n := rfl

theorem keptRangeNat_eq_prefixCount (E : Set ℕ) (x : ℕ) :
    keptRangeNat E x =
      prefixSquares (keptNth E) (keptCount E (x + 1)) := by
  classical
  induction x with
  | zero =>
      have hzero : keptCount E 1 = 0 := by
        simp [keptCount, Nat.count_one, keptPred]
      simp [hzero, keptRangeNat, keptTermNat, prefixSquares]
  | succ x ih =>
      have hsum : keptRangeNat E (x + 1) =
          keptRangeNat E x + keptTermNat E (x + 1) := by
        simp [keptRangeNat, Finset.sum_range_succ]
      rw [hsum, ih]
      have hc : keptCount E (x + 1 + 1) =
          keptCount E (x + 1) +
            if keptPred E (x + 1) then 1 else 0 :=
        by simpa [keptCount] using Nat.count_succ (keptPred E) (x + 1)
      rw [hc]
      by_cases he : x + 1 ∈ E
      · have hp : ¬keptPred E (x + 1) := by simp [keptPred, he]
        simp [hp, keptTermNat, he]
      · have hp : keptPred E (x + 1) := by simp [keptPred, he]
        have hnth : keptNth E (keptCount E (x + 1)) =
            x + 1 := by
          rw [keptNth_eq_nth]
          simpa [keptCount] using Nat.nth_count hp
        simp [hp, keptTermNat, he, prefixSquares_succ, hnth]

/-- Sums over enumerated retained values match sums over all integers
up to the n-th retained integer, provided the kept set is infinite. -/
theorem keptIndexPrefix_succ_eq_keptSquaresUpTo (E : Set ℕ)
    (hInf : (Set.ofPred (keptPred E)).Infinite) (n : ℕ) :
    keptIndexPrefix E (n + 1) = keptSquaresUpTo E (keptNth E n) := by
  classical
  have hcount : keptCount E (keptNth E n + 1) = n + 1 := by
    simpa [keptCount, keptNth_eq_nth] using
      Nat.count_nth_succ_of_infinite hInf n
  rw [keptSquaresUpTo_eq_range, keptRangeNat_eq_prefixCount, hcount]
  rfl

end SparseDeletion

#print axioms SparseDeletion.keptRangeNat_eq_prefixCount
#print axioms SparseDeletion.keptIndexPrefix_succ_eq_keptSquaresUpTo
