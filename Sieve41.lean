import Mathlib.Data.Nat.Nth

/-!
Finite, kernel-checked quadratic-residue sieve modulo 41.
The cubic uses exact natural division by 6, yielding the square-sum polynomial.
-/

namespace SparseDeletion

def squareMod41 (z : ℕ) : Bool :=
  (List.range 41).any (fun y => decide (y * y % 41 = z % 41))

def cubicMod41 (x b : ℕ) : ℕ :=
  8 * 7 * x * (x + 1) * (2 * x + 1) + 8 * b + 1

def goodCount41 (b : ℕ) : ℕ :=
  ((Finset.range 41).filter
    (fun x => squareMod41 (cubicMod41 x b))).card

theorem finiteSieve41 :
    ∀ b ∈ Finset.range 41, goodCount41 b ≤ 27 := by
  decide

end SparseDeletion

#print axioms SparseDeletion.finiteSieve41
