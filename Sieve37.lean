import Mathlib.Data.Nat.Nth

/-!
Finite, kernel-checked quadratic-residue sieve modulo 37.
The cubic uses exact natural division by 6, yielding the square-sum polynomial.
-/

namespace SparseDeletion

def squareMod37 (z : ℕ) : Bool :=
  (List.range 37).any (fun y => decide (y * y % 37 = z % 37))

def cubicMod37 (x b : ℕ) : ℕ :=
  8 * 31 * x * (x + 1) * (2 * x + 1) + 8 * b + 1

def goodCount37 (b : ℕ) : ℕ :=
  ((Finset.range 37).filter
    (fun x => squareMod37 (cubicMod37 x b))).card

theorem finiteSieve37 :
    ∀ b ∈ Finset.range 37, goodCount37 b ≤ 24 := by
  decide

end SparseDeletion

#print axioms SparseDeletion.finiteSieve37
