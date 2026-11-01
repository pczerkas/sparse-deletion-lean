module -- shake: keep-all

public import WeilConditionalSieve

@[expose] public section

namespace SparseDeletion

open Polynomial

attribute [local instance] Classical.propDecidable

/-!
# Cubic roots: an elementary, unconditional component of Weil refinement

A cubic polynomial with nonzero leading coefficient has at most
three distinct roots. This file specializes that fact to our
explicit cubic polynomial over ZMod p.

No character-sum estimate or Hasse-Weil theorem is used.
-/

/-- Any cubic over a field, with nonzero cubic coefficient,
has at most three distinct roots. -/
theorem cubic_polynomial_zeros_le_three
    (F : Type*) [Field F] [Fintype F] [DecidableEq F]
    (a b c d : F) (ha : a ≠ 0) :
    ((Finset.univ : Finset F).filter
      (fun x => (cubicShape a b c d).eval x = 0)).card ≤ 3 := by
  classical
  let P : Polynomial F := cubicShape a b c d
  have hdeg : P.natDegree = 3 := by
    dsimp [P, cubicShape]
    compute_degree!
  have hP : P ≠ 0 := by
    intro heq
    simp [heq] at hdeg
  have hsubset :
      ((Finset.univ : Finset F).filter
        (fun x => P.eval x = 0)).val ⊆ P.roots := by
    intro x hx
    have hz : P.eval x = 0 := (Finset.mem_filter.mp hx).2
    exact (Polynomial.mem_roots hP).2 (by simpa [Polynomial.IsRoot] using hz)
  have hc := Polynomial.card_le_degree_of_subset_roots hsubset
  simpa only [P, hdeg] using hc

/-- The concrete triangular-prefix cubic has degree exactly three
over all primes in the project's prime family. -/
theorem primeCubicPoly_zeros_le_three (r : ℕ) (b : ℤ) :
    letI : Fact (largePrime r).Prime := ⟨largePrime_prime r⟩
    ((Finset.univ : Finset (ZMod (largePrime r))).filter
      (fun x => (primeCubicPoly (largePrime r)
        (b : ZMod (largePrime r))).eval x = 0)).card ≤ 3 := by
  classical
  let p := largePrime r
  letI : Fact p.Prime := ⟨largePrime_prime r⟩
  have hp : 37 ≤ p := largePrime_ge r
  have h16 : (16 : ZMod p) ≠ 0 := by
    intro hz
    have hdiv : p ∣ 16 := (ZMod.natCast_eq_zero_iff 16 p).mp hz
    have hle : p ≤ 16 := Nat.le_of_dvd (by decide) hdiv
    omega
  have h6 : (6 : ZMod p) ≠ 0 := prime_h6 p hp
  have ha : (16 * (6 : ZMod p)⁻¹) ≠ 0 :=
    mul_ne_zero h16 (inv_ne_zero h6)
  have hroots := cubic_polynomial_zeros_le_three (ZMod p)
    (16 * (6 : ZMod p)⁻¹) (24 * (6 : ZMod p)⁻¹)
    (8 * (6 : ZMod p)⁻¹) (8 * (b : ZMod p) + 1) ha
  simpa [p, primeCubicPoly, cubicShape] using hroots

end SparseDeletion
