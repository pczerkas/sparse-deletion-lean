import SparseDeletion
import Sieve31Poly
import Mathlib.Data.ZMod.Basic

namespace SparseDeletion

theorem squareSum_mod31_bridge (x : ℕ) :
    (naturalSquareSum x : ZMod 31) =
      (26 : ZMod 31) * (x : ZMod 31) * ((x : ZMod 31) + 1) *
        (2 * (x : ZMod 31) + 1) := by
  have h := naturalSquareSum_cubic x
  have h' := congrArg (fun k : ℤ => (k : ZMod 31)) h
  push_cast at h'
  have hc : (26 : ZMod 31) * 6 = 1 := by decide
  calc
    (naturalSquareSum x : ZMod 31) =
      26 * (6 * (naturalSquareSum x : ZMod 31)) := by
        calc
          (naturalSquareSum x : ZMod 31) =
              (26 * 6 : ZMod 31) * (naturalSquareSum x : ZMod 31) := by simp [hc]
          _ = _ := by ring
    _ = 26 * (x : ZMod 31) * ((x : ZMod 31) + 1) *
        (2 * (x : ZMod 31) + 1) := by
          rw [h']
          ring

theorem cubicMod31_bridge (x b : ℕ) :
    ((8 * (naturalSquareSum x + (b : ℤ)) + 1 : ℤ) : ZMod 31) =
      (cubicMod31 x b : ZMod 31) := by
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
  rw [squareSum_mod31_bridge]
  simp only [cubicMod31, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring


theorem squareMod31_of_cast_square (z k : ℕ)
    (h : (z : ZMod 31) = (k : ZMod 31) ^ 2) :
    squareMod31 z = true := by
  have hm : z % 31 = k ^ 2 % 31 := by
    have hv := congrArg ZMod.val h
    have hk : ((k : ZMod 31) ^ 2).val = k ^ 2 % 31 := by
      rw [← Nat.cast_pow, ZMod.val_natCast]
    rw [hk, ZMod.val_natCast] at hv
    exact hv
  unfold squareMod31
  apply List.any_eq_true.mpr
  refine ⟨k % 31, List.mem_range.mpr (Nat.mod_lt _ (by decide)), ?_⟩
  simpa [Nat.mul_mod, pow_two] using hm.symm

theorem triangular_passes_mod31 (x b : ℕ)
    (h : TriangularInt (naturalSquareSum x + (b : ℤ))) :
    squareMod31 (cubicMod31 x b) = true := by
  obtain ⟨m, hm⟩ := h
  have hSq : (8 * (naturalSquareSum x + (b : ℤ)) + 1 : ℤ) =
      (2 * (m : ℤ) + 1) ^ 2 := by
    nlinarith [hm]
  have hz := congrArg (fun z : ℤ => (z : ZMod 31)) hSq
  have hc := cubicMod31_bridge x b
  push_cast at hz
  apply squareMod31_of_cast_square (cubicMod31 x b) (2 * m + 1)
  rw [← hc]
  convert hz using 1 <;> push_cast <;> ring


theorem cubicMod31_bridge_int (x : ℕ) (b : ℤ) :
    ((8 * (naturalSquareSum x + b) + 1 : ℤ) : ZMod 31) =
      (cubicMod31 x (b : ZMod 31).val : ZMod 31) := by
  let v : ℕ := (b : ZMod 31).val
  have hv : (v : ZMod 31) = (b : ZMod 31) := ZMod.natCast_zmod_val _
  calc
    ((8 * (naturalSquareSum x + b) + 1 : ℤ) : ZMod 31) =
      ((8 * (naturalSquareSum x + (v : ℤ)) + 1 : ℤ) : ZMod 31) := by
        simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast]
        rw [hv]
    _ = (cubicMod31 x v : ZMod 31) := cubicMod31_bridge x v

theorem triangular_passes_mod31_int (x : ℕ) (b : ℤ)
    (h : TriangularInt (naturalSquareSum x + b)) :
    squareMod31 (cubicMod31 x (b : ZMod 31).val) = true := by
  obtain ⟨m, hm⟩ := h
  have hSq : (8 * (naturalSquareSum x + b) + 1 : ℤ) =
      (2 * (m : ℤ) + 1) ^ 2 := by
    nlinarith [hm]
  have hz := congrArg (fun z : ℤ => (z : ZMod 31)) hSq
  have hc := cubicMod31_bridge_int x b
  push_cast at hz
  apply squareMod31_of_cast_square
      (cubicMod31 x (b : ZMod 31).val) (2 * m + 1)
  rw [← hc]
  convert hz using 1 <;> push_cast <;> ring

#print axioms triangular_passes_mod31_int

end SparseDeletion
