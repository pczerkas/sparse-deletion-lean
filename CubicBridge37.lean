module -- shake: keep-all

public import SparseDeletion
public import Sieve37Poly
public import Mathlib.Data.ZMod.Basic

@[expose] public section

namespace SparseDeletion

theorem squareSum_mod37_bridge (x : ℕ) :
    (naturalSquareSum x : ZMod 37) =
      (31 : ZMod 37) * (x : ZMod 37) * ((x : ZMod 37) + 1) *
        (2 * (x : ZMod 37) + 1) := by
  have h := naturalSquareSum_cubic x
  have h' := congrArg (fun k : ℤ => (k : ZMod 37)) h
  push_cast at h'
  have hc : (31 : ZMod 37) * 6 = 1 := by decide
  calc
    (naturalSquareSum x : ZMod 37) =
      31 * (6 * (naturalSquareSum x : ZMod 37)) := by
        calc
          (naturalSquareSum x : ZMod 37) =
              (31 * 6 : ZMod 37) * (naturalSquareSum x : ZMod 37) := by simp [hc]
          _ = _ := by ring
    _ = 31 * (x : ZMod 37) * ((x : ZMod 37) + 1) *
        (2 * (x : ZMod 37) + 1) := by
          rw [h']
          ring

theorem cubicMod37_bridge (x b : ℕ) :
    ((8 * (naturalSquareSum x + (b : ℤ)) + 1 : ℤ) : ZMod 37) =
      (cubicMod37 x b : ZMod 37) := by
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  rw [squareSum_mod37_bridge]
  simp only [cubicMod37, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring


theorem squareMod37_of_cast_square (z k : ℕ)
    (h : (z : ZMod 37) = (k : ZMod 37) ^ 2) :
    squareMod37 z = true := by
  have hm : z % 37 = k ^ 2 % 37 := by
    have hv := congrArg ZMod.val h
    have hk : ((k : ZMod 37) ^ 2).val = k ^ 2 % 37 := by
      rw [← Nat.cast_pow, ZMod.val_natCast]
    rw [hk, ZMod.val_natCast] at hv
    exact hv
  unfold squareMod37
  apply List.any_eq_true.mpr
  refine ⟨k % 37, List.mem_range.mpr (Nat.mod_lt _ (by decide)), ?_⟩
  simpa [Nat.mul_mod, pow_two] using hm.symm

theorem triangular_passes_mod37 (x b : ℕ)
    (h : TriangularInt (naturalSquareSum x + (b : ℤ))) :
    squareMod37 (cubicMod37 x b) = true := by
  obtain ⟨m, hm⟩ := h
  have hSq : (8 * (naturalSquareSum x + (b : ℤ)) + 1 : ℤ) =
      (2 * (m : ℤ) + 1) ^ 2 := by
    nlinarith [hm]
  have hz := congrArg (fun z : ℤ => (z : ZMod 37)) hSq
  have hc := cubicMod37_bridge x b
  push_cast at hz
  apply squareMod37_of_cast_square (cubicMod37 x b) (2 * m + 1)
  rw [← hc]
  convert hz using 1 <;> push_cast <;> ring


theorem cubicMod37_bridge_int (x : ℕ) (b : ℤ) :
    ((8 * (naturalSquareSum x + b) + 1 : ℤ) : ZMod 37) =
      (cubicMod37 x (b : ZMod 37).val : ZMod 37) := by
  let v : ℕ := (b : ZMod 37).val
  have hv : (v : ZMod 37) = (b : ZMod 37) := ZMod.natCast_zmod_val _
  calc
    ((8 * (naturalSquareSum x + b) + 1 : ℤ) : ZMod 37) =
      ((8 * (naturalSquareSum x + (v : ℤ)) + 1 : ℤ) : ZMod 37) := by
        simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
        rw [hv]
    _ = (cubicMod37 x v : ZMod 37) := cubicMod37_bridge x v

theorem triangular_passes_mod37_int (x : ℕ) (b : ℤ)
    (h : TriangularInt (naturalSquareSum x + b)) :
    squareMod37 (cubicMod37 x (b : ZMod 37).val) = true := by
  obtain ⟨m, hm⟩ := h
  have hSq : (8 * (naturalSquareSum x + b) + 1 : ℤ) =
      (2 * (m : ℤ) + 1) ^ 2 := by
    nlinarith [hm]
  have hz := congrArg (fun z : ℤ => (z : ZMod 37)) hSq
  have hc := cubicMod37_bridge_int x b
  push_cast at hz
  apply squareMod37_of_cast_square
      (cubicMod37 x (b : ZMod 37).val) (2 * m + 1)
  rw [← hc]
  convert hz using 1 <;> push_cast <;> ring

#print axioms triangular_passes_mod37_int

end SparseDeletion
