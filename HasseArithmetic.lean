import QuadraticCharBridge
import Mathlib.Data.Real.Sqrt

namespace SparseDeletion

/-- Purely numeric implication used to convert Hasse's 2√p bound
into the uniform 3/4 sieve bound for primes at least 37.
No elliptic-curve estimate is assumed as a Lean axiom. -/
theorem hasse_sqrt_to_quarter (p : ℕ) (hp : 37 ≤ p) (c : ℤ)
    (hchar : (c : ℝ) ≤ 2 * Real.sqrt (p : ℝ)) :
    2 * c + 6 ≤ (p : ℤ) := by
  have hpR : (37 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hsq : (Real.sqrt (p : ℝ)) ^ 2 = (p : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hpos : 0 ≤ Real.sqrt (p : ℝ) := Real.sqrt_nonneg _
  have hroot : (6 : ℝ) ≤ Real.sqrt (p : ℝ) := by
    nlinarith
  have hmul : 0 ≤ Real.sqrt (p : ℝ) * (Real.sqrt (p : ℝ) - 6) :=
    mul_nonneg hpos (sub_nonneg.mpr hroot)
  have hreal : (2 : ℝ) * (c : ℝ) + 6 ≤ (p : ℝ) := by
    nlinarith
  exact_mod_cast hreal

#print axioms hasse_sqrt_to_quarter

end SparseDeletion
