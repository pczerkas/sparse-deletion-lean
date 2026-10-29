import CubicBridge31
import CubicBridge37
import Mathlib.Data.Nat.ModEq

namespace SparseDeletion

theorem crt_mod_inj_window (u : ℕ) :
    Set.InjOn (fun x : ℕ => (x % 31, x % 37))
      ((Finset.Ico u (u + 1147)) : Set ℕ) := by
  intro x hx y hy hxy
  have hx' := Finset.mem_Ico.mp hx
  have hy' := Finset.mem_Ico.mp hy
  have h31 : x % 31 = y % 31 := congrArg Prod.fst hxy
  have h37 : x % 37 = y % 37 := congrArg Prod.snd hxy
  have hc : Nat.Coprime 31 37 := by decide
  have hp : Nat.ModEq (31 * 37) x y :=
    (Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨h31, h37⟩
  change x % (31 * 37) = y % (31 * 37) at hp
  omega

end SparseDeletion

#print axioms SparseDeletion.crt_mod_inj_window

namespace SparseDeletion

noncomputable def crtWindowCandidates (u : ℕ) (b : ℤ) : Finset ℕ := by
  classical
  exact (Finset.Ico u (u + 1147)).filter (fun x =>
    squareMod31 (cubicMod31 x (b : ZMod 31).val) = true ∧
    squareMod37 (cubicMod37 x (b : ZMod 37).val) = true)

theorem crtWindowCandidates_le (u : ℕ) (b : ℤ) :
    (crtWindowCandidates u b).card ≤ 504 := by
  classical
  let A : Finset ℕ := (Finset.range 31).filter
    (fun x => squareMod31 (cubicMod31 x (b : ZMod 31).val))
  let B : Finset ℕ := (Finset.range 37).filter
    (fun x => squareMod37 (cubicMod37 x (b : ZMod 37).val))
  have hmap : Set.MapsTo (fun x : ℕ => (x % 31, x % 37))
      (crtWindowCandidates u b : Set ℕ) ((A.product B) : Set (ℕ × ℕ)) := by
    intro x hx
    have hgood := (Finset.mem_filter.mp
      (show x ∈ crtWindowCandidates u b from hx)).2
    rcases hgood with ⟨hx31, hx37⟩
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by decide)), ?_⟩
      have h : squareMod31 (cubicMod31 x (b : ZMod 31).val) =
          squareMod31 (cubicMod31 (x % 31) (b : ZMod 31).val) := by
        unfold squareMod31
        rw [cubicMod31_xmod]
      exact h ▸ hx31
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by decide)), ?_⟩
      have h : squareMod37 (cubicMod37 x (b : ZMod 37).val) =
          squareMod37 (cubicMod37 (x % 37) (b : ZMod 37).val) := by
        unfold squareMod37
        rw [cubicMod37_xmod]
      exact h ▸ hx37
  have hinj : Set.InjOn (fun x : ℕ => (x % 31, x % 37))
      (crtWindowCandidates u b : Set ℕ) := by
    apply (crt_mod_inj_window u).mono
    intro x hx
    exact (Finset.mem_filter.mp
      (show x ∈ crtWindowCandidates u b from hx)).1
  have hA : A.card ≤ 21 := by
    simpa only [A, goodCount31] using goodCount31_bound (b : ZMod 31).val
  have hB : B.card ≤ 24 := by
    simpa only [B, goodCount37] using goodCount37_bound (b : ZMod 37).val
  calc
    (crtWindowCandidates u b).card ≤ (A.product B).card :=
      Finset.card_le_card_of_injOn (fun x : ℕ => (x % 31, x % 37)) hmap hinj
    _ = A.card * B.card := Finset.card_product A B
    _ ≤ 21 * 24 := Nat.mul_le_mul hA hB
    _ = 504 := by decide

end SparseDeletion

#print axioms SparseDeletion.crtWindowCandidates_le

namespace SparseDeletion

theorem sieveCRT_triangular_interval (u : ℕ) (b : ℤ) :
    (cubicCandidates u 1147 b).card ≤ 504 := by
  classical
  have hsub : cubicCandidates u 1147 b ⊆ crtWindowCandidates u b := by
    intro x hx
    have hx' := Finset.mem_filter.mp (show x ∈ cubicCandidates u 1147 b from hx)
    apply Finset.mem_filter.mpr
    exact ⟨hx'.1,
      triangular_passes_mod31_int x b hx'.2,
      triangular_passes_mod37_int x b hx'.2⟩
  exact (Finset.card_le_card hsub).trans (crtWindowCandidates_le u b)

theorem uniformCubicSieve_two :
    ∃ M : ℕ, 0 < M ∧
      ∀ (u : ℕ) (b : ℤ),
        4 ^ (2 : ℕ) * (cubicCandidates u M b).card ≤ 3 ^ (2 : ℕ) * M := by
  refine ⟨1147, by decide, ?_⟩
  intro u b
  have h := sieveCRT_triangular_interval u b
  norm_num at *
  omega

end SparseDeletion

#print axioms SparseDeletion.sieveCRT_triangular_interval
#print axioms SparseDeletion.uniformCubicSieve_two
