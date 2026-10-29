import Sieve31

namespace SparseDeletion

theorem cubicMod31_xperiod (x b : ℕ) :
    cubicMod31 (x + 31) b % 31 = cubicMod31 x b % 31 := by
  simp [cubicMod31, Nat.add_mod, Nat.mul_mod]

theorem cubicMod31_bperiod (x b : ℕ) :
    cubicMod31 x (b + 31) % 31 = cubicMod31 x b % 31 := by
  simp [cubicMod31, Nat.add_mod, Nat.mul_mod]

theorem cubicMod31_bmod (x b : ℕ) :
    cubicMod31 x b % 31 = cubicMod31 x (b % 31) % 31 := by
  simp [cubicMod31, Nat.add_mod, Nat.mul_mod]

theorem goodCount31_mod (b : ℕ) : goodCount31 b = goodCount31 (b % 31) := by
  unfold goodCount31
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  have h := cubicMod31_bmod x b
  simp only [squareMod31]
  simp [h]

theorem goodCount31_bound (b : ℕ) : goodCount31 b ≤ 21 := by
  rw [goodCount31_mod]
  exact finiteSieve31 (b % 31) (Finset.mem_range.mpr (Nat.mod_lt _ (by decide)))


theorem cubicMod31_xmod (x b : ℕ) :
    cubicMod31 x b % 31 = cubicMod31 (x % 31) b % 31 := by
  simp [cubicMod31, Nat.add_mod, Nat.mul_mod]

noncomputable def windowCandidates31 (u b : ℕ) : Finset ℕ :=
  (Finset.Ico u (u + 31)).filter (fun x => squareMod31 (cubicMod31 x b))

theorem windowCandidates31_bound (u b : ℕ) :
    (windowCandidates31 u b).card ≤ 21 := by
  classical
  have hmap : Set.MapsTo (fun x : ℕ => x % 31)
      (windowCandidates31 u b : Set ℕ)
      ((Finset.range 31).filter (fun x => squareMod31 (cubicMod31 x b)) : Set ℕ) := by
    intro x hx
    have hgood := (Finset.mem_filter.mp (show x ∈ windowCandidates31 u b from hx)).2
    apply Finset.mem_filter.mpr
    constructor
    · exact Finset.mem_range.mpr (Nat.mod_lt x (show 0 < 31 by decide))
    · have heq : squareMod31 (cubicMod31 x b) =
          squareMod31 (cubicMod31 (x % 31) b) := by
        unfold squareMod31
        rw [cubicMod31_xmod]
      rw [← heq]
      exact hgood
  have hinj : Set.InjOn (fun x : ℕ => x % 31)
      (windowCandidates31 u b : Set ℕ) := by
    intro x hx y hy hxy
    have hx' := Finset.mem_Ico.mp (Finset.mem_filter.mp (show x ∈ windowCandidates31 u b from hx)).1
    have hy' := Finset.mem_Ico.mp (Finset.mem_filter.mp (show y ∈ windowCandidates31 u b from hy)).1
    change x % 31 = y % 31 at hxy
    omega
  exact (Finset.card_le_card_of_injOn (fun x : ℕ => x % 31) hmap hinj).trans
    (goodCount31_bound b)

#print axioms windowCandidates31_bound

end SparseDeletion

#print axioms SparseDeletion.goodCount31_bound
