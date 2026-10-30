module -- shake: keep-all

public import Mathlib.Data.Nat.Nth
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Tactic.Linarith

@[expose] public section

open Filter

namespace SparseDeletion

/-!
# Generic counting and natural density

No reference to polynomials, triangular numbers or any particular sequence.
-/

noncomputable def countUpTo (P : Set ℕ) (X : ℕ) : ℕ := by
  classical
  exact ((Finset.range X).filter (fun x => x ∈ P)).card

def HasDensityZero (P : Set ℕ) : Prop :=
  Tendsto (fun X : ℕ => (countUpTo P X : ℝ) / (X : ℝ))
    atTop (nhds (0 : ℝ))


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


end SparseDeletion
