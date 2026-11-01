module -- shake: keep-all

public import WeilConditionalLogRate
public import HasseWeil.SparseDeletion.PrimePolyBridge

@[expose] public section

/-!
# Unconditional discharge of the original cubic Weil premise

This file MUST compile in the joint AINTLIB (Lean 4.36.0-rc2) environment
with the unchanged source files from our original project copied in.
It cannot be imported by the original Lean 4.35 build.

We identify the original primeCubicPoly with the exact polynomial
used by the independently certified AINTLIB bridge, then discharge
CubicWeilCharacterUpper, and finally instantiate the entire
original conditional 3/4 CRT/logarithmic proof chain.
-/

namespace SparseDeletion

/-- Identical polynomial coefficients: this is a definitional equality,
not a comparison of finitely many evaluations. -/
theorem primeCubicPoly_eq_aintlib
    (p : ℕ) [Fact p.Prime] (b : ZMod p) :
    primeCubicPoly p b =
      AINTLIBBridge.matchingPrimeCubicPoly p b := by
  rfl

/-- The previously conditional hypothesis is discharged by the actual
Hasse theorem of AINTLIB, with the singular case handled separately. -/
theorem cubicWeilCharacterUpper_from_AINTLIB :
    CubicWeilCharacterUpper := by
  intro r b
  letI : Fact (largePrime r).Prime := ⟨largePrime_prime r⟩
  have h := AINTLIBBridge.matchingPrimeCubicPoly_character_upper
    (largePrime r) (largePrime_ge r) (b : ZMod (largePrime r))
  simpa only [primeCubicPoly_eq_aintlib] using h

/-- This 3/4 local-sieve log/loglog rate no longer requires a Weil
hypothesis once both formalization projects are compiled together. -/
theorem quantitative_weil_value_loglog_unconditional
    (E : Set ℕ) (N : ℕ) (hN : 0 < N)
    (hQ : 2048 ≤ Real.log ((N : ℝ) / (countUpTo E N + 1))) :
    let L := Real.log ((N : ℝ) / (countUpTo E N + 1))
    ((countUpTo (hitSet E) N : ℝ) / (N : ℝ)) ≤
      (8 / 3 : ℝ) * Real.exp
        (-(Real.log ((4 : ℝ) / 3)) * (L / (2 * Real.log L))) :=
  quantitative_weil_value_loglog_bound
    cubicWeilCharacterUpper_from_AINTLIB E N hN hQ

/-- Same unconditional rate for hits indexed by the surviving sequence. -/
theorem quantitative_weil_index_loglog_unconditional
    (E : Set ℕ) (hInf : (Set.ofPred (keptPred E)).Infinite)
    (N : ℕ) (hNth : keptNth E N < 2 * N + 2)
    (hQ : 2048 ≤ Real.log
      (((2 * N + 2 : ℕ) : ℝ) /
        (countUpTo E (2 * N + 2) + 1))) :
    let L := Real.log
      (((2 * N + 2 : ℕ) : ℝ) / (countUpTo E (2 * N + 2) + 1))
    ((countUpTo (indexHitSet E) (N + 1) : ℝ) /
        ((2 * N + 2 : ℕ) : ℝ)) ≤
      (8 / 3 : ℝ) * Real.exp
        (-(Real.log ((4 : ℝ) / 3)) * (L / (2 * Real.log L))) :=
  quantitative_weil_index_loglog_bound
    cubicWeilCharacterUpper_from_AINTLIB E hInf N hNth hQ

end SparseDeletion

/-- info: 'SparseDeletion.primeCubicPoly_eq_aintlib' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SparseDeletion.primeCubicPoly_eq_aintlib
/-- info: 'SparseDeletion.cubicWeilCharacterUpper_from_AINTLIB' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SparseDeletion.cubicWeilCharacterUpper_from_AINTLIB
/-- info: 'SparseDeletion.quantitative_weil_value_loglog_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SparseDeletion.quantitative_weil_value_loglog_unconditional
/-- info: 'SparseDeletion.quantitative_weil_index_loglog_unconditional' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms SparseDeletion.quantitative_weil_index_loglog_unconditional
