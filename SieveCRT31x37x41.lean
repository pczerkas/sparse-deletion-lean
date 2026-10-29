import SieveCRT31x37
import CubicBridge41
import Mathlib.Data.Nat.ModEq

namespace SparseDeletion

/-- CRT makes the residue triple injective on each interval of 47027 integers. -/
theorem crt_mod_inj_window3 (u : ℕ) :
    Set.InjOn (fun x : ℕ => ((x % 31, x % 37), x % 41))
      ((Finset.Ico u (u + 47027)) : Set ℕ) := by
  intro x hx y hy hxy
  have hx' := Finset.mem_Ico.mp hx
  have hy' := Finset.mem_Ico.mp hy
  have h31 : x % 31 = y % 31 := congrArg (fun p : (ℕ × ℕ) × ℕ => p.1.1) hxy
  have h37 : x % 37 = y % 37 := congrArg (fun p : (ℕ × ℕ) × ℕ => p.1.2) hxy
  have h41 : x % 41 = y % 41 := congrArg (fun p : (ℕ × ℕ) × ℕ => p.2) hxy
  have h31_37 : Nat.ModEq (31 * 37) x y :=
    (Nat.modEq_and_modEq_iff_modEq_mul (show Nat.Coprime 31 37 by decide)).mp
      ⟨h31, h37⟩
  have hprod : Nat.ModEq ((31 * 37) * 41) x y :=
    (Nat.modEq_and_modEq_iff_modEq_mul
      (show Nat.Coprime (31 * 37) 41 by decide)).mp ⟨h31_37, h41⟩
  change x % (31 * 37 * 41) = y % (31 * 37 * 41) at hprod
  omega

noncomputable def crtWindowCandidates3 (u : ℕ) (b : ℤ) : Finset ℕ := by
  classical
  exact (Finset.Ico u (u + 47027)).filter (fun x =>
    squareMod31 (cubicMod31 x (b : ZMod 31).val) = true ∧
    squareMod37 (cubicMod37 x (b : ZMod 37).val) = true ∧
    squareMod41 (cubicMod41 x (b : ZMod 41).val) = true)

theorem crtWindowCandidates3_le (u : ℕ) (b : ℤ) :
    (crtWindowCandidates3 u b).card ≤ 13608 := by
  classical
  let A : Finset ℕ := (Finset.range 31).filter
    (fun x => squareMod31 (cubicMod31 x (b : ZMod 31).val))
  let B : Finset ℕ := (Finset.range 37).filter
    (fun x => squareMod37 (cubicMod37 x (b : ZMod 37).val))
  let C : Finset ℕ := (Finset.range 41).filter
    (fun x => squareMod41 (cubicMod41 x (b : ZMod 41).val))
  have hmap : Set.MapsTo (fun x : ℕ => ((x % 31, x % 37), x % 41))
      (crtWindowCandidates3 u b : Set ℕ)
      (((A.product B).product C) : Set ((ℕ × ℕ) × ℕ)) := by
    intro x hx
    have hgood := (Finset.mem_filter.mp
      (show x ∈ crtWindowCandidates3 u b from hx)).2
    rcases hgood with ⟨hx31, hx37, hx41⟩
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_product.mpr
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
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (Nat.mod_lt _ (by decide)), ?_⟩
      have h : squareMod41 (cubicMod41 x (b : ZMod 41).val) =
          squareMod41 (cubicMod41 (x % 41) (b : ZMod 41).val) := by
        unfold squareMod41
        rw [cubicMod41_xmod]
      exact h ▸ hx41
  have hinj : Set.InjOn (fun x : ℕ => ((x % 31, x % 37), x % 41))
      (crtWindowCandidates3 u b : Set ℕ) := by
    apply (crt_mod_inj_window3 u).mono
    intro x hx
    exact (Finset.mem_filter.mp
      (show x ∈ crtWindowCandidates3 u b from hx)).1
  have hA : A.card ≤ 21 := by
    simpa only [A, goodCount31] using goodCount31_bound (b : ZMod 31).val
  have hB : B.card ≤ 24 := by
    simpa only [B, goodCount37] using goodCount37_bound (b : ZMod 37).val
  have hC : C.card ≤ 27 := by
    simpa only [C, goodCount41] using goodCount41_bound (b : ZMod 41).val
  calc
    (crtWindowCandidates3 u b).card ≤ ((A.product B).product C).card :=
      Finset.card_le_card_of_injOn
        (fun x : ℕ => ((x % 31, x % 37), x % 41)) hmap hinj
    _ = A.card * B.card * C.card := by simp [Finset.card_product]
    _ ≤ 21 * 24 * 27 := Nat.mul_le_mul (Nat.mul_le_mul hA hB) hC
    _ = 13608 := by decide

theorem sieveCRT3_triangular_interval (u : ℕ) (b : ℤ) :
    (cubicCandidates u 47027 b).card ≤ 13608 := by
  classical
  have hsub : cubicCandidates u 47027 b ⊆ crtWindowCandidates3 u b := by
    intro x hx
    have hx' := Finset.mem_filter.mp
      (show x ∈ cubicCandidates u 47027 b from hx)
    apply Finset.mem_filter.mpr
    exact ⟨hx'.1,
      triangular_passes_mod31_int x b hx'.2,
      triangular_passes_mod37_int x b hx'.2,
      triangular_passes_mod41_int x b hx'.2⟩
  exact (Finset.card_le_card hsub).trans (crtWindowCandidates3_le u b)

theorem uniformCubicSieve_three :
    ∃ M : ℕ, 0 < M ∧
      ∀ (u : ℕ) (b : ℤ),
        4 ^ (3 : ℕ) * (cubicCandidates u M b).card ≤ 3 ^ (3 : ℕ) * M := by
  refine ⟨47027, by decide, ?_⟩
  intro u b
  have h := sieveCRT3_triangular_interval u b
  norm_num at *
  omega

end SparseDeletion

#print axioms SparseDeletion.sieveCRT3_triangular_interval
#print axioms SparseDeletion.uniformCubicSieve_three
