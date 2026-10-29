import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.Tactic

namespace SparseDeletion

open scoped BigOperators

section AbstractQuadratic

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def squareIndicator (a : F) : ℤ := by
  classical
  exact if IsSquare a then 1 else 0

noncomputable def zeroIndicator (a : F) : ℤ := by
  classical
  exact if a = 0 then 1 else 0

theorem square_indicator_character (hF : ringChar F ≠ 2) (a : F) :
    2 * squareIndicator a =
      quadraticChar F a + 1 + zeroIndicator a := by
  classical
  by_cases ha : a = 0
  · subst a
    simp [squareIndicator, zeroIndicator, quadraticChar_zero]
  · by_cases hs : IsSquare a
    · have hchi : quadraticChar F a = 1 :=
        (quadraticChar_one_iff_isSquare ha).mpr hs
      simp [squareIndicator, zeroIndicator, ha, hs, hchi]
    · have hchi : quadraticChar F a = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr hs
      simp [squareIndicator, zeroIndicator, ha, hs, hchi]

noncomputable def squareInputCount (f : F → F) : ℤ := by
  classical
  exact ∑ x : F, squareIndicator (f x)

noncomputable def zeroInputCount (f : F → F) : ℤ := by
  classical
  exact ∑ x : F, zeroIndicator (f x)

noncomputable def quadraticCharSum (f : F → F) : ℤ := by
  classical
  exact ∑ x : F, quadraticChar F (f x)

/-- Exact character-sum identity, including all zeroes of f.
No Hasse/Weil bound is assumed or used. -/
theorem two_mul_square_count (hF : ringChar F ≠ 2) (f : F → F) :
    2 * squareInputCount f =
      (Fintype.card F : ℤ) + quadraticCharSum f + zeroInputCount f := by
  classical
  unfold squareInputCount quadraticCharSum zeroInputCount
  rw [Finset.mul_sum]
  have hh : (∑ x : F, 2 * squareIndicator (f x)) =
      (∑ x : F, (quadraticChar F (f x) + 1 + zeroIndicator (f x))) := by
    apply Finset.sum_congr rfl
    intro x hx
    exact square_indicator_character hF (f x)
  rw [hh]
  simp only [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  ring


/-- The indicator sum counts precisely the square-valued inputs. -/
theorem squareInputCount_eq_card (f : F → F) :
    squareInputCount f =
      (((Finset.univ : Finset F).filter (fun x => IsSquare (f x))).card : ℤ) := by
  classical
  simp [squareInputCount, squareIndicator, Finset.sum_ite]

theorem zeroInputCount_eq_card (f : F → F) :
    zeroInputCount f =
      (((Finset.univ : Finset F).filter (fun x => f x = 0)).card : ℤ) := by
  classical
  simp [zeroInputCount, zeroIndicator, Finset.sum_ite]

/-- An entirely elementary final algebraic reduction: a cubic with <= 3 roots
and a suitable character-sum bound passes at most 3/4 of all inputs. -/
theorem square_count_le_three_quarters (hF : ringChar F ≠ 2) (f : F → F)
    (hroots : zeroInputCount f ≤ 3)
    (hchar : 2 * quadraticCharSum f + 6 ≤ (Fintype.card F : ℤ)) :
    4 * squareInputCount f ≤ 3 * (Fintype.card F : ℤ) := by
  have h := two_mul_square_count hF f
  omega

theorem square_card_le_three_quarters (hF : ringChar F ≠ 2) (f : F → F)
    (hroots : (((Finset.univ : Finset F).filter
      (fun x => f x = 0)).card : ℤ) ≤ 3)
    (hchar : 2 * quadraticCharSum f + 6 ≤ (Fintype.card F : ℤ)) :
    4 * ((Finset.univ : Finset F).filter
      (fun x => IsSquare (f x))).card ≤ 3 * Fintype.card F := by
  have h := square_count_le_three_quarters hF f
    (by simpa only [zeroInputCount_eq_card] using hroots) hchar
  rw [squareInputCount_eq_card] at h
  exact_mod_cast h

#print axioms squareInputCount_eq_card
#print axioms zeroInputCount_eq_card
#print axioms square_count_le_three_quarters
#print axioms square_card_le_three_quarters

#print axioms square_indicator_character
#print axioms two_mul_square_count

end AbstractQuadratic
end SparseDeletion
