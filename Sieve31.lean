import Mathlib.Data.Nat.Nth
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith

/-!
A fully finite, kernel-checkable experiment at q=31.
The modular square predicate is checked for all x,b = 0,...,30.
This is NOT yet the uniform infinite sieve; lifting to arbitrary
integers and CRT is needed separately.
-/

namespace SparseDeletion

def squareMod31 (z : ℕ) : Bool :=
  (List.range 31).any (fun y => decide (y * y % 31 = z % 31))

def cubicMod31 (x b : ℕ) : ℕ :=
  8 * 26 * x * (x + 1) * (2 * x + 1) + 8 * b + 1

def goodCount31 (b : ℕ) : ℕ :=
  ((Finset.range 31).filter
    (fun x => squareMod31 (cubicMod31 x b))).card

theorem finiteSieve31 :
    ∀ b ∈ Finset.range 31, goodCount31 b ≤ 21 := by
  decide

end SparseDeletion

#print axioms SparseDeletion.finiteSieve31
