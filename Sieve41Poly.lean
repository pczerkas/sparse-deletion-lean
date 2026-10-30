module -- shake: keep-all

public import Sieve41

@[expose] public section

namespace SparseDeletion

theorem cubicMod41_xperiod (x b : ℕ) :
    cubicMod41 (x + 41) b % 41 = cubicMod41 x b % 41 := by
  simp [cubicMod41, Nat.add_mod, Nat.mul_mod]

theorem cubicMod41_bperiod (x b : ℕ) :
    cubicMod41 x (b + 41) % 41 = cubicMod41 x b % 41 := by
  simp [cubicMod41, Nat.add_mod, Nat.mul_mod]

theorem cubicMod41_bmod (x b : ℕ) :
    cubicMod41 x b % 41 = cubicMod41 x (b % 41) % 41 := by
  simp [cubicMod41, Nat.add_mod, Nat.mul_mod]

theorem goodCount41_mod (b : ℕ) : goodCount41 b = goodCount41 (b % 41) := by
  unfold goodCount41
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  have h := cubicMod41_bmod x b
  simp only [squareMod41]
  simp [h]

theorem goodCount41_bound (b : ℕ) : goodCount41 b ≤ 27 := by
  rw [goodCount41_mod]
  exact finiteSieve41 (b % 41) (Finset.mem_range.mpr (Nat.mod_lt _ (by decide)))


theorem cubicMod41_xmod (x b : ℕ) :
    cubicMod41 x b % 41 = cubicMod41 (x % 41) b % 41 := by
  simp [cubicMod41, Nat.add_mod, Nat.mul_mod]

noncomputable def windowCandidates41 (u b : ℕ) : Finset ℕ :=
  (Finset.Ico u (u + 41)).filter (fun x => squareMod41 (cubicMod41 x b))

theorem windowCandidates41_bound (u b : ℕ) :
    (windowCandidates41 u b).card ≤ 27 := by
  classical
  have hmap : Set.MapsTo (fun x : ℕ => x % 41)
      (windowCandidates41 u b : Set ℕ)
      ((Finset.range 41).filter (fun x => squareMod41 (cubicMod41 x b)) : Set ℕ) := by
    intro x hx
    have hgood := (Finset.mem_filter.mp (show x ∈ windowCandidates41 u b from hx)).2
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (Nat.mod_lt x (show 0 < 41 by decide))
    · have heq : squareMod41 (cubicMod41 x b) =
          squareMod41 (cubicMod41 (x % 41) b) := by
        unfold squareMod41
        rw [cubicMod41_xmod]
      rw [← heq]
      exact hgood
  have hinj : Set.InjOn (fun x : ℕ => x % 41)
      (windowCandidates41 u b : Set ℕ) := by
    intro x hx y hy hxy
    have hx' := Finset.mem_Ico.mp (Finset.mem_filter.mp (show x ∈ windowCandidates41 u b from hx)).1
    have hy' := Finset.mem_Ico.mp (Finset.mem_filter.mp (show y ∈ windowCandidates41 u b from hy)).1
    change x % 41 = y % 41 at hxy
    omega
  exact (Finset.card_le_card_of_injOn (fun x : ℕ => x % 41) hmap hinj).trans
    (goodCount41_bound b)

#print axioms windowCandidates41_bound

end SparseDeletion

#print axioms SparseDeletion.goodCount41_bound
