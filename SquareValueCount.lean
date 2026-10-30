module -- shake: keep-all

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Tactic

@[expose] public section

namespace SparseDeletion

open Finset

attribute [local instance] Classical.propDecidable

section Squares
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- Exactly (q + 1)/2 elements of an odd-cardinality finite field are
squares, including zero. This is the only character identity needed
by the main sieve: no Weil, Hasse or character-sum estimates. -/
theorem card_square_values_exact (hF : ringChar F ≠ 2) :
    2 * ((Finset.univ : Finset F).filter IsSquare).card =
      Fintype.card F + 1 := by
  have hpoint (x : F) :
      2 * (if IsSquare x then (1 : ℤ) else 0) =
        quadraticChar F x + 1 + (if x = 0 then 1 else 0) := by
    by_cases hx : x = 0
    · subst x
      simp
    · by_cases hs : IsSquare x
      · have hχ : quadraticChar F x = 1 :=
          (quadraticChar_one_iff_isSquare hx).mpr hs
        simp [hx, hs, hχ]
      · have hχ : quadraticChar F x = -1 :=
          quadraticChar_neg_one_iff_not_isSquare.mpr hs
        simp [hx, hs, hχ]
  have hχsum : (∑ x : F, quadraticChar F x) = 0 :=
    quadraticChar_sum_zero (F := F) hF
  have hzeros : (∑ x : F, (if x = 0 then (1 : ℤ) else 0)) = 1 := by
    simp
  have hind :
      (∑ x : F, 2 * (if IsSquare x then (1 : ℤ) else 0)) =
        ∑ x : F, (quadraticChar F x + 1 + (if x = 0 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact hpoint x
  have hsum : (2 : ℤ) * ((Finset.univ : Finset F).filter IsSquare).card =
      (Fintype.card F : ℤ) + 1 := by
    calc
      _ = 2 * (∑ x : F, if IsSquare x then (1 : ℤ) else 0) := by
        simp
      _ = ∑ x : F, 2 * (if IsSquare x then (1 : ℤ) else 0) :=
        by rw [Finset.mul_sum]
      _ = ∑ x : F, (quadraticChar F x + 1 + (if x = 0 then 1 else 0)) := hind
      _ = (Fintype.card F : ℤ) + 1 := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hχsum, hzeros]
        simp
  exact_mod_cast hsum

#print axioms card_square_values_exact

end Squares
end SparseDeletion
