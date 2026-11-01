module -- shake: keep-all

public import WeilCubicRoots

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-!
# Reduce the conditional Weil hypothesis to one precise missing inequality

Polynomial root counting was proved separately in WeilCubicRoots.
Hence only the *upper* (one-sided) character-sum estimate remains
as a hypothesis. The mathematical literature supplies this via
Weil's bound; the theorem itself is not yet in the pinned Mathlib.
-/

/-- The precise remaining character-sum inequality; explicitly a
hypothesis, not a global axiom or a Lean-proved Weil theorem. -/
def CubicWeilCharacterUpper : Prop :=
  ∀ (r : ℕ) (b : ℤ),
    letI : Fact (largePrime r).Prime := ⟨largePrime_prime r⟩
    (((∑ x : ZMod (largePrime r),
      quadraticCharFun (ZMod (largePrime r))
        ((primeCubicPoly (largePrime r)
          (b : ZMod (largePrime r))).eval x)) : ℤ) : ℝ) ≤
      2 * Real.sqrt (largePrime r : ℝ)

/-- The cubic root bound is now proved unconditionally,
so the only premise needed for the 3/4 sieve is the character-sum
estimate. -/
theorem cubic_weil_local_input_of_character_upper
    (hchar : CubicWeilCharacterUpper) : CubicWeilLocalInput := by
  intro r b
  letI : Fact (largePrime r).Prime := ⟨largePrime_prime r⟩
  exact ⟨hchar r b, primeCubicPoly_zeros_le_three r b⟩

/-- All remaining CRT arithmetic is kernel-verified,
assuming solely the explicit Weil character bound. -/
theorem quantitative_weil_value_bound_of_character_upper
    (hchar : CubicWeilCharacterUpper) (E : Set ℕ) (r N : ℕ) :
    4 ^ r * countUpTo (hitSet E) N ≤
      3 ^ r * N +
        4 ^ r * (16 * (r + 50) ^ 2) ^ r *
          (countUpTo E N + 1) :=
  quantitative_weil_value_bound
    (cubic_weil_local_input_of_character_upper hchar) E r N

/-- Retained-index form, conditional only on Weil's character bound
and the same explicit N-th-survivor growth condition as before. -/
theorem quantitative_weil_index_bound_of_character_upper
    (hchar : CubicWeilCharacterUpper)
    (E : Set ℕ) (hInf : (Set.ofPred (keptPred E)).Infinite)
    (r N : ℕ) (hNth : keptNth E N < 2 * N + 2) :
    4 ^ r * countUpTo (indexHitSet E) (N + 1) ≤
      3 ^ r * (2 * N + 2) +
        4 ^ r * (16 * (r + 50) ^ 2) ^ r *
          (countUpTo E (2 * N + 2) + 1) :=
  quantitative_weil_index_bound
    (cubic_weil_local_input_of_character_upper hchar) E hInf r N hNth

end SparseDeletion
