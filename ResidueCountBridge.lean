import CubicSumBridge
import Mathlib.Data.ZMod.Basic

namespace SparseDeletion

theorem residue_filter_card_eq_field_count (p : ℕ) [NeZero p]
    (Q : ZMod p → Prop) [DecidablePred Q] :
    ((Finset.range p).filter (fun x : ℕ => Q (x : ZMod p))).card =
      ((Finset.univ : Finset (ZMod p)).filter Q).card := by
  classical
  apply Finset.card_bij (fun (x : ℕ) _ => (x : ZMod p))
  · intro x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩
  · intro x hx y hy heq
    have hmod := congrArg ZMod.val heq
    simp only [ZMod.val_natCast] at hmod
    have hxlt := Finset.mem_range.mp (Finset.mem_filter.mp hx).1
    have hylt := Finset.mem_range.mp (Finset.mem_filter.mp hy).1
    rw [Nat.mod_eq_of_lt hxlt, Nat.mod_eq_of_lt hylt] at hmod
    exact hmod
  · intro z hz
    refine ⟨z.val, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_range.mpr (ZMod.val_lt z)
      · simpa only [ZMod.natCast_zmod_val] using (Finset.mem_filter.mp hz).2
    · exact ZMod.natCast_zmod_val z

#print axioms residue_filter_card_eq_field_count

end SparseDeletion
