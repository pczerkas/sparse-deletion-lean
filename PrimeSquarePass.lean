module -- shake: keep-all

public import PrimeCubicPoly
public import PrimeFamily

@[expose] public section

namespace SparseDeletion

noncomputable def primeSquarePass (r : ℕ) (b : ℤ) (x : ℕ) : Prop := by
  letI : Fact (largePrime r).Prime := ⟨largePrime_prime r⟩
  exact IsSquare ((primeCubicPoly (largePrime r) (b : ZMod (largePrime r))).eval
    (x : ZMod (largePrime r)))

theorem primeSquarePass_periodic (r : ℕ) (b : ℤ) (x : ℕ) :
    primeSquarePass r b (x % largePrime r) ↔ primeSquarePass r b x := by
  unfold primeSquarePass
  simp only [ZMod.natCast_mod]

set_option linter.style.haveILetI false in
theorem primeSquarePass_of_triangular (r : ℕ) (b : ℤ) (x : ℕ)
    (ht : TriangularInt (naturalSquareSum x + b)) :
    primeSquarePass r b x := by
  letI : Fact (largePrime r).Prime := ⟨largePrime_prime r⟩
  have hp : 37 ≤ largePrime r := largePrime_ge r
  obtain ⟨m, hm⟩ := ht
  have hs : (8 * (naturalSquareSum x + b) + 1 : ℤ) =
      (2 * (m : ℤ) + 1) ^ 2 := by
    nlinarith [hm]
  have hz := congrArg (fun t : ℤ => (t : ZMod (largePrime r))) hs
  have hev := primeCubicPoly_eval_nat (largePrime r) hp
    (b : ZMod (largePrime r)) x
  unfold primeSquarePass
  rw [hev]
  refine ⟨(2 * (m : ℤ) + 1 : ZMod (largePrime r)), ?_⟩
  push_cast at hz
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat,
    Int.cast_natCast, pow_two] using hz


#print axioms primeSquarePass_periodic
#print axioms primeSquarePass_of_triangular

end SparseDeletion
