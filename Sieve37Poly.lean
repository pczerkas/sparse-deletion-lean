module -- shake: keep-all

public import Sieve37

@[expose] public section

namespace SparseDeletion

theorem cubicMod37_xperiod (x b : ℕ) :
    cubicMod37 (x + 37) b % 37 = cubicMod37 x b % 37 := by
  simp [cubicMod37, Nat.add_mod, Nat.mul_mod]

theorem cubicMod37_bperiod (x b : ℕ) :
    cubicMod37 x (b + 37) % 37 = cubicMod37 x b % 37 := by
  simp [cubicMod37, Nat.add_mod, Nat.mul_mod]

theorem cubicMod37_bmod (x b : ℕ) :
    cubicMod37 x b % 37 = cubicMod37 x (b % 37) % 37 := by
  simp [cubicMod37, Nat.add_mod, Nat.mul_mod]

theorem goodCount37_mod (b : ℕ) : goodCount37 b = goodCount37 (b % 37) := by
  unfold goodCount37
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  have h := cubicMod37_bmod x b
  simp only [squareMod37]
  simp [h]

theorem goodCount37_bound (b : ℕ) : goodCount37 b ≤ 24 := by
  rw [goodCount37_mod]
  exact finiteSieve37 (b % 37) (Finset.mem_range.mpr (Nat.mod_lt _ (by decide)))


theorem cubicMod37_xmod (x b : ℕ) :
    cubicMod37 x b % 37 = cubicMod37 (x % 37) b % 37 := by
  simp [cubicMod37, Nat.add_mod, Nat.mul_mod]

noncomputable def windowCandidates37 (u b : ℕ) : Finset ℕ :=
  (Finset.Ico u (u + 37)).filter (fun x => squareMod37 (cubicMod37 x b))

theorem windowCandidates37_bound (u b : ℕ) :
    (windowCandidates37 u b).card ≤ 24 := by
  classical
  have hmap : Set.MapsTo (fun x : ℕ => x % 37)
      (windowCandidates37 u b : Set ℕ)
      ((Finset.range 37).filter (fun x => squareMod37 (cubicMod37 x b)) : Set ℕ) := by
    intro x hx
    have hgood := (Finset.mem_filter.mp (show x ∈ windowCandidates37 u b from hx)).2
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (Nat.mod_lt x (show 0 < 37 by decide))
    · have heq : squareMod37 (cubicMod37 x b) =
          squareMod37 (cubicMod37 (x % 37) b) := by
        unfold squareMod37
        rw [cubicMod37_xmod]
      rw [← heq]
      exact hgood
  have hinj : Set.InjOn (fun x : ℕ => x % 37)
      (windowCandidates37 u b : Set ℕ) := by
    intro x hx y hy hxy
    have hx' := Finset.mem_Ico.mp (Finset.mem_filter.mp (show x ∈ windowCandidates37 u b from hx)).1
    have hy' := Finset.mem_Ico.mp (Finset.mem_filter.mp (show y ∈ windowCandidates37 u b from hy)).1
    change x % 37 = y % 37 at hxy
    omega
  exact (Finset.card_le_card_of_injOn (fun x : ℕ => x % 37) hmap hinj).trans
    (goodCount37_bound b)

#print axioms windowCandidates37_bound

end SparseDeletion

#print axioms SparseDeletion.goodCount37_bound
