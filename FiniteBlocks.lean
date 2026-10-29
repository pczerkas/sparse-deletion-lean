import BridgeRemaining

namespace SparseDeletion

noncomputable def selectedCount (P : Set ℕ) (u v : ℕ) : ℕ := by
  classical
  exact ((Finset.Ico u v).filter (fun x => x ∈ P)).card

theorem selectedCount_add (P : Set ℕ) (u v : ℕ) :
    selectedCount P 0 (u + v) =
      selectedCount P 0 u + selectedCount P u (u + v) := by
  classical
  let A : Finset ℕ := (Finset.Ico 0 u).filter (fun x => x ∈ P)
  let B : Finset ℕ := (Finset.Ico u (u + v)).filter (fun x => x ∈ P)
  have hIco : Finset.Ico 0 (u + v) =
      Finset.Ico 0 u ∪ Finset.Ico u (u + v) := by
    ext x
    simp only [Finset.mem_Ico, Finset.mem_union]
    omega
  have hd : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro x ha hb
    have ha' := (Finset.mem_filter.mp ha).1
    have hb' := (Finset.mem_filter.mp hb).1
    simp only [Finset.mem_Ico] at ha' hb'
    omega
  change ((Finset.Ico 0 (u + v)).filter (fun x => x ∈ P)).card =
    A.card + B.card
  rw [hIco, Finset.filter_union]
  exact Finset.card_union_of_disjoint hd

theorem countUpTo_eq_selectedCount (P : Set ℕ) (X : ℕ) :
    countUpTo P X = selectedCount P 0 X := by
  classical
  simp [countUpTo, selectedCount, Nat.Ico_zero_eq_range]

def hitSet (E : Set ℕ) : Set ℕ :=
  {x : ℕ | Triangular (keptSquaresUpTo E x)}

theorem hit_block_le_deletions (E : Set ℕ) (u : ℕ) :
    selectedCount (hitSet E) u (u + 47027) ≤
      13608 + 47027 * selectedCount E u (u + 47027) := by
  classical
  by_cases hn : selectedCount E u (u + 47027) = 0
  · have he : ∀ k : ℕ, u < k → k < u + 47027 → k ∉ E := by
      intro k hu hk hmem
      have hfin : k ∈ (Finset.Ico u (u + 47027)).filter
          (fun x => x ∈ E) :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hk⟩, hmem⟩
      have hpos : 0 < selectedCount E u (u + 47027) :=
        Finset.card_pos.mpr ⟨k, hfin⟩
      omega
    have hb := clean_block_kept_triangular_le_13608 E u he
    have heq : ((Finset.Ico u (u + 47027)).filter
        (fun x => x ∈ hitSet E)) = keptWindowCandidates E u := by
      ext x
      constructor
      · intro hx
        have h := Finset.mem_filter.mp hx
        apply Finset.mem_filter.mpr
        exact ⟨h.1, h.2⟩
      · intro hx
        have h := Finset.mem_filter.mp hx
        apply Finset.mem_filter.mpr
        exact ⟨h.1, h.2⟩
    have hh : selectedCount (hitSet E) u (u + 47027) ≤ 13608 := by
      change (((Finset.Ico u (u + 47027)).filter
        (fun x => x ∈ hitSet E)).card) ≤ 13608
      rw [heq]
      exact hb
    omega
  · have hpos : 1 ≤ selectedCount E u (u + 47027) := by omega
    have hbound : selectedCount (hitSet E) u (u + 47027) ≤ 47027 := by
      unfold selectedCount
      exact (Finset.card_filter_le _ _).trans (by simp)
    omega

theorem hit_count_mul_blocks (E : Set ℕ) (k : ℕ) :
    countUpTo (hitSet E) (47027 * k) ≤
      13608 * k + 47027 * countUpTo E (47027 * k) := by
  induction k with
  | zero =>
    simp [countUpTo]
  | succ k ih =>
    have hmul : 47027 * (k + 1) = 47027 * k + 47027 := by omega
    have hH : countUpTo (hitSet E) (47027 * (k + 1)) =
      countUpTo (hitSet E) (47027 * k) +
        selectedCount (hitSet E) (47027 * k) (47027 * k + 47027) := by
      rw [hmul, countUpTo_eq_selectedCount,
        countUpTo_eq_selectedCount]
      exact selectedCount_add (hitSet E) (47027 * k) 47027
    have hE : countUpTo E (47027 * (k + 1)) =
      countUpTo E (47027 * k) +
        selectedCount E (47027 * k) (47027 * k + 47027) := by
      rw [hmul, countUpTo_eq_selectedCount,
        countUpTo_eq_selectedCount]
      exact selectedCount_add E (47027 * k) 47027
    have hb := hit_block_le_deletions E (47027 * k)
    rw [hH, hE]
    omega


theorem hit_count_bound (E : Set ℕ) (N : ℕ) :
    countUpTo (hitSet E) N ≤
      13608 * (N / 47027) + 47027 * countUpTo E N + N % 47027 := by
  classical
  let k := N / 47027
  let r := N % 47027
  have hN : 47027 * k + r = N := by
    dsimp [k, r]
    omega
  have hbase := hit_count_mul_blocks E k
  have hH : countUpTo (hitSet E) N =
      countUpTo (hitSet E) (47027 * k) +
        selectedCount (hitSet E) (47027 * k) N := by
    calc
      countUpTo (hitSet E) N =
        selectedCount (hitSet E) 0 (47027 * k + r) := by
          rw [hN]
          exact countUpTo_eq_selectedCount _ _
      _ = selectedCount (hitSet E) 0 (47027 * k) +
            selectedCount (hitSet E) (47027 * k) (47027 * k + r) :=
        selectedCount_add (hitSet E) (47027 * k) r
      _ = countUpTo (hitSet E) (47027 * k) +
            selectedCount (hitSet E) (47027 * k) N := by
        rw [countUpTo_eq_selectedCount, hN]
  have hE : countUpTo E N =
      countUpTo E (47027 * k) + selectedCount E (47027 * k) N := by
    calc
      countUpTo E N = selectedCount E 0 (47027 * k + r) := by
        rw [hN]
        exact countUpTo_eq_selectedCount _ _
      _ = selectedCount E 0 (47027 * k) +
            selectedCount E (47027 * k) (47027 * k + r) :=
        selectedCount_add E (47027 * k) r
      _ = countUpTo E (47027 * k) +
            selectedCount E (47027 * k) N := by
        rw [countUpTo_eq_selectedCount, hN]
  have hTail : selectedCount (hitSet E) (47027 * k) N ≤ r := by
    unfold selectedCount
    calc
      ((Finset.Ico (47027 * k) N).filter
        (fun x => x ∈ hitSet E)).card ≤
          (Finset.Ico (47027 * k) N).card :=
            Finset.card_filter_le _ _
      _ = r := by
        simp only [Nat.card_Ico]
        omega
  change countUpTo (hitSet E) N ≤
    13608 * k + 47027 * countUpTo E N + r
  omega

#print axioms hit_count_bound

end SparseDeletion

#print axioms SparseDeletion.hit_count_mul_blocks
