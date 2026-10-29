import SparseDeletion
import Sieve41Poly
import Mathlib.Data.ZMod.Basic

namespace SparseDeletion

theorem squareSum_mod41_bridge (x : ℕ) :
    (naturalSquareSum x : ZMod 41) =
      (7 : ZMod 41) * (x : ZMod 41) * ((x : ZMod 41) + 1) *
        (2 * (x : ZMod 41) + 1) := by
  have h := naturalSquareSum_cubic x
  have h' := congrArg (fun k : ℤ => (k : ZMod 41)) h
  push_cast at h'
  have hc : (7 : ZMod 41) * 6 = 1 := by decide
  calc
    (naturalSquareSum x : ZMod 41) =
      7 * (6 * (naturalSquareSum x : ZMod 41)) := by
        calc
          (naturalSquareSum x : ZMod 41) =
              (7 * 6 : ZMod 41) * (naturalSquareSum x : ZMod 41) := by simp [hc]
          _ = _ := by ring
    _ = 7 * (x : ZMod 41) * ((x : ZMod 41) + 1) *
        (2 * (x : ZMod 41) + 1) := by
          rw [h']
          ring

theorem cubicMod41_bridge (x b : ℕ) :
    ((8 * (naturalSquareSum x + (b : ℤ)) + 1 : ℤ) : ZMod 41) =
      (cubicMod41 x b : ZMod 41) := by
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  rw [squareSum_mod41_bridge]
  simp only [cubicMod41, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring


theorem squareMod41_of_cast_square (z k : ℕ)
    (h : (z : ZMod 41) = (k : ZMod 41) ^ 2) :
    squareMod41 z = true := by
  have hm : z % 41 = k ^ 2 % 41 := by
    have hv := congrArg ZMod.val h
    have hk : ((k : ZMod 41) ^ 2).val = k ^ 2 % 41 := by
      rw [← Nat.cast_pow, ZMod.val_natCast]
    rw [hk, ZMod.val_natCast] at hv
    exact hv
  unfold squareMod41
  apply List.any_eq_true.mpr
  refine ⟨k % 41, List.mem_range.mpr (Nat.mod_lt _ (by decide)), ?_⟩
  simpa [Nat.mul_mod, pow_two] using hm.symm

theorem triangular_passes_mod41 (x b : ℕ)
    (h : TriangularInt (naturalSquareSum x + (b : ℤ))) :
    squareMod41 (cubicMod41 x b) = true := by
  obtain ⟨m, hm⟩ := h
  have hSq : (8 * (naturalSquareSum x + (b : ℤ)) + 1 : ℤ) =
      (2 * (m : ℤ) + 1) ^ 2 := by
    nlinarith [hm]
  have hz := congrArg (fun z : ℤ => (z : ZMod 41)) hSq
  have hc := cubicMod41_bridge x b
  push_cast at hz
  apply squareMod41_of_cast_square (cubicMod41 x b) (2 * m + 1)
  rw [← hc]
  convert hz using 1 <;> push_cast <;> ring


theorem cubicMod41_bridge_int (x : ℕ) (b : ℤ) :
    ((8 * (naturalSquareSum x + b) + 1 : ℤ) : ZMod 41) =
      (cubicMod41 x (b : ZMod 41).val : ZMod 41) := by
  let v : ℕ := (b : ZMod 41).val
  have hv : (v : ZMod 41) = (b : ZMod 41) := ZMod.natCast_zmod_val _
  calc
    ((8 * (naturalSquareSum x + b) + 1 : ℤ) : ZMod 41) =
      ((8 * (naturalSquareSum x + (v : ℤ)) + 1 : ℤ) : ZMod 41) := by
        simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
        rw [hv]
    _ = (cubicMod41 x v : ZMod 41) := cubicMod41_bridge x v

theorem triangular_passes_mod41_int (x : ℕ) (b : ℤ)
    (h : TriangularInt (naturalSquareSum x + b)) :
    squareMod41 (cubicMod41 x (b : ZMod 41).val) = true := by
  obtain ⟨m, hm⟩ := h
  have hSq : (8 * (naturalSquareSum x + b) + 1 : ℤ) =
      (2 * (m : ℤ) + 1) ^ 2 := by
    nlinarith [hm]
  have hz := congrArg (fun z : ℤ => (z : ZMod 41)) hSq
  have hc := cubicMod41_bridge_int x b
  push_cast at hz
  apply squareMod41_of_cast_square
      (cubicMod41 x (b : ZMod 41).val) (2 * m + 1)
  rw [← hc]
  convert hz using 1 <;> push_cast <;> ring

#print axioms triangular_passes_mod41_int

end SparseDeletion
