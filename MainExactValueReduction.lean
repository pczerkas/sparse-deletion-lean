import MainValueSetReduction
import SquareValueCount
import MainHasseReduction

namespace SparseDeletion

open Finset Polynomial

attribute [local instance] Classical.propDecidable

/-- For every chosen prime, the only remaining arithmetic hypothesis:
    t ↦ t³−t takes at least (2p−1)/3 distinct values. -/
def CubicValueLowerBound : Prop :=
  ∀ (r : ℕ),
    letI : Fact (largePrime r).Prime := ⟨largePrime_prime r⟩
    2 * largePrime r ≤
      3 * ((Finset.univ : Finset (ZMod (largePrime r))).image
        (fun t : ZMod (largePrime r) => t ^ 3 - t)).card + 1

/-- Full target assuming ONLY the classical cubic value-set lower bound.
    No Hasse, Weil, elliptic curves, or character-sum assumptions. -/
theorem main_of_cubic_value_bound
    (hvalue : CubicValueLowerBound)
    (E : Set ℕ) (hE : HasDensityZero E) :
    HasDensityZero {n : ℕ | Triangular (keptIndexPrefix E n)} := by
  classical
  apply zeroDensityByIndex_of_modular_family67
    largePrime primeSquarePass largePrime_positive largePrime_coprime_previous
  · intro r b x
    exact primeSquarePass_periodic r b x
  · intro r b
    letI : Fact (largePrime r).Prime := ⟨largePrime_prime r⟩
    let p := largePrime r
    have hp : 37 ≤ p := largePrime_ge r
    have h2 : (2 : ZMod p) ≠ 0 := by
      intro hz
      have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp hz
      have hle : p ≤ 2 := Nat.le_of_dvd (by omega) hdvd
      omega
    have h3 : (3 : ZMod p) ≠ 0 := by
      intro hz
      have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp hz
      have hle : p ≤ 3 := Nat.le_of_dvd (by omega) hdvd
      omega
    have himage : 2 * Fintype.card (ZMod p) ≤
        3 * ((Finset.univ : Finset (ZMod p)).image
          (fun z : ZMod p => (primeCubicPoly p (b : ZMod p)).eval z)).card + 1 := by
      have hcard :
          ((Finset.univ : Finset (ZMod p)).image
            (fun z : ZMod p => (primeCubicPoly p (b : ZMod p)).eval z)).card =
          ((Finset.univ : Finset (ZMod p)).image
            (fun t : ZMod p => t ^ 3 - t)).card := by
        exact cubicShape_image_card_eq_xcube_sub_x (b : ZMod p) h2 h3
      rw [hcard, ZMod.card]
      exact hvalue r
    have hsquares :
        2 * ((Finset.univ : Finset (ZMod p)).filter IsSquare).card ≤
          Fintype.card (ZMod p) + 1 :=
      (card_square_values_exact (prime_char_not_two p hp)).le
    have hfield : 7 * ((Finset.univ : Finset (ZMod p)).filter
        (fun z => IsSquare ((primeCubicPoly p (b : ZMod p)).eval z))).card ≤
        6 * Fintype.card (ZMod p) :=
      six_sevenths_of_cubic_image_bound
        (fun z : ZMod p => (primeCubicPoly p (b : ZMod p)).eval z)
        (by simpa only [ZMod.card] using (show 35 ≤ p by omega)) himage hsquares
    have hpred (x : ℕ) : primeSquarePass r b x ↔
        IsSquare ((primeCubicPoly p (b : ZMod p)).eval (x : ZMod p)) := by
      unfold primeSquarePass
      rfl
    have heq : ((Finset.range (largePrime r)).filter (primeSquarePass r b)) =
        ((Finset.range p).filter
          (fun x : ℕ => IsSquare ((primeCubicPoly p (b : ZMod p)).eval (x : ZMod p)))) := by
      ext x
      simp only [Finset.mem_filter, hpred]
      rfl
    rw [heq]
    have hc := residue_filter_card_eq_field_count p
      (fun z : ZMod p => IsSquare ((primeCubicPoly p (b : ZMod p)).eval z))
    rw [hc]
    simpa only [ZMod.card, p] using hfield
  · intro r b x ht
    exact primeSquarePass_of_triangular r b x ht
  · exact hE

#print axioms CubicValueLowerBound
#print axioms main_of_cubic_value_bound

end SparseDeletion
