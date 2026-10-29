import FiniteBlocks

namespace SparseDeletion

/-!
Generalizes the finite 3-prime block estimate to an arbitrary
uniform sieve modulus M and bound C.  No analytic number theory is used.
-/

theorem clean_block_kept_general (E : Set ℕ) (u M C : ℕ)
    (hclean : ∀ k : ℕ, u < k → k < u + M → k ∉ E)
    (hsieve : ∀ v : ℕ, ∀ b : ℤ, (cubicCandidates v M b).card ≤ C) :
    selectedCount (hitSet E) u (u + M) ≤ C := by
  classical
  have hsub : ((Finset.Ico u (u + M)).filter
      (fun x => x ∈ hitSet E)) ⊆
      cubicCandidates u M (-removedSquareSum E u) := by
    intro x hx
    obtain ⟨hinterval, ht⟩ := Finset.mem_filter.mp hx
    have hle : u ≤ x := (Finset.mem_Ico.mp hinterval).1
    have hlt : x < u + M := (Finset.mem_Ico.mp hinterval).2
    have heq : shiftedRemaining E x =
        naturalSquareSum x - removedSquareSum E u := by
      apply shiftedRemaining_clean E u x hle
      intro k hk hkx
      exact hclean k hk (by omega)
    apply Finset.mem_filter.mpr
    constructor
    · exact hinterval
    · have htri : Triangular (keptSquaresUpTo E x) := ht
      have hcast : TriangularInt (shiftedRemaining E x) := by
        rw [← keptSquaresUpTo_cast_eq_shiftedRemaining]
        exact triangular_cast (keptSquaresUpTo E x) htri
      simpa only [heq, sub_eq_add_neg] using hcast
  change (((Finset.Ico u (u + M)).filter
    (fun x => x ∈ hitSet E)).card) ≤ C
  exact (Finset.card_le_card hsub).trans (hsieve u _)

theorem hit_block_general (E : Set ℕ) (M C u : ℕ)
    (hsieve : ∀ v : ℕ, ∀ b : ℤ, (cubicCandidates v M b).card ≤ C) :
    selectedCount (hitSet E) u (u + M) ≤
      C + M * selectedCount E u (u + M) := by
  classical
  by_cases hn : selectedCount E u (u + M) = 0
  · have hclean : ∀ k : ℕ, u < k → k < u + M → k ∉ E := by
      intro k hu hk hmem
      have hfin : k ∈ (Finset.Ico u (u + M)).filter
          (fun x => x ∈ E) :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hk⟩, hmem⟩
      have hpos : 0 < selectedCount E u (u + M) :=
        Finset.card_pos.mpr ⟨k, hfin⟩
      omega
    have hb := clean_block_kept_general E u M C hclean hsieve
    omega
  · have hpos : 1 ≤ selectedCount E u (u + M) := by omega
    have hbound : selectedCount (hitSet E) u (u + M) ≤ M := by
      unfold selectedCount
      exact (Finset.card_filter_le _ _).trans (by simp)
    have hmul : M ≤ M * selectedCount E u (u + M) := by
      simpa using Nat.mul_le_mul_left M hpos
    omega

theorem hit_count_mul_general (E : Set ℕ) (M C k : ℕ)
    (hsieve : ∀ v : ℕ, ∀ b : ℤ, (cubicCandidates v M b).card ≤ C) :
    countUpTo (hitSet E) (M * k) ≤
      C * k + M * countUpTo E (M * k) := by
  induction k with
  | zero =>
    simp [countUpTo]
  | succ k ih =>
    have hmul : M * (k + 1) = M * k + M := by ring
    have hH : countUpTo (hitSet E) (M * (k + 1)) =
      countUpTo (hitSet E) (M * k) +
        selectedCount (hitSet E) (M * k) (M * k + M) := by
      rw [hmul, countUpTo_eq_selectedCount, countUpTo_eq_selectedCount]
      exact selectedCount_add (hitSet E) (M * k) M
    have hE : countUpTo E (M * (k + 1)) =
      countUpTo E (M * k) + selectedCount E (M * k) (M * k + M) := by
      rw [hmul, countUpTo_eq_selectedCount, countUpTo_eq_selectedCount]
      exact selectedCount_add E (M * k) M
    have hb := hit_block_general E M C (M * k) hsieve
    rw [hH, hE]
    calc
      countUpTo (hitSet E) (M * k) +
          selectedCount (hitSet E) (M * k) (M * k + M) ≤
          (C * k + M * countUpTo E (M * k)) +
          (C + M * selectedCount E (M * k) (M * k + M)) :=
        Nat.add_le_add ih hb
      _ = C * (k + 1) +
          M * (countUpTo E (M * k) +
            selectedCount E (M * k) (M * k + M)) := by ring

theorem hit_count_bound_general (E : Set ℕ) (M C N : ℕ)
    (hM : 0 < M)
    (hsieve : ∀ v : ℕ, ∀ b : ℤ, (cubicCandidates v M b).card ≤ C) :
    countUpTo (hitSet E) N ≤
      C * (N / M) + M * countUpTo E N + N % M := by
  classical
  let k := N / M
  let r := N % M
  have hN : M * k + r = N := by
    dsimp [k, r]
    simpa [add_comm] using Nat.mod_add_div N M
  have hbase := hit_count_mul_general E M C k hsieve
  have hH : countUpTo (hitSet E) N =
      countUpTo (hitSet E) (M * k) +
        selectedCount (hitSet E) (M * k) N := by
    calc
      countUpTo (hitSet E) N =
        selectedCount (hitSet E) 0 (M * k + r) := by
          rw [hN]
          exact countUpTo_eq_selectedCount _ _
      _ = selectedCount (hitSet E) 0 (M * k) +
            selectedCount (hitSet E) (M * k) (M * k + r) :=
        selectedCount_add (hitSet E) (M * k) r
      _ = countUpTo (hitSet E) (M * k) +
            selectedCount (hitSet E) (M * k) N := by
        rw [countUpTo_eq_selectedCount, hN]
  have hE : countUpTo E N =
      countUpTo E (M * k) + selectedCount E (M * k) N := by
    calc
      countUpTo E N = selectedCount E 0 (M * k + r) := by
        rw [hN]
        exact countUpTo_eq_selectedCount _ _
      _ = selectedCount E 0 (M * k) +
            selectedCount E (M * k) (M * k + r) :=
        selectedCount_add E (M * k) r
      _ = countUpTo E (M * k) +
            selectedCount E (M * k) N := by
        rw [countUpTo_eq_selectedCount, hN]
  have hTail : selectedCount (hitSet E) (M * k) N ≤ r := by
    unfold selectedCount
    calc
      ((Finset.Ico (M * k) N).filter (fun x => x ∈ hitSet E)).card ≤
          (Finset.Ico (M * k) N).card :=
            Finset.card_filter_le _ _
      _ = r := by
        simp only [Nat.card_Ico]
        omega
  change countUpTo (hitSet E) N ≤
    C * k + M * countUpTo E N + r
  rw [hH, hE]
  calc
    countUpTo (hitSet E) (M * k) +
        selectedCount (hitSet E) (M * k) N ≤
        (C * k + M * countUpTo E (M * k)) + r :=
      Nat.add_le_add hbase hTail
    _ ≤ C * k + M *
          (countUpTo E (M * k) + selectedCount E (M * k) N) + r := by
      have hmono : M * countUpTo E (M * k) ≤
          M * (countUpTo E (M * k) + selectedCount E (M * k) N) :=
        Nat.mul_le_mul_left M (Nat.le_add_right _ _)
      omega

end SparseDeletion

#print axioms SparseDeletion.hit_count_bound_general
