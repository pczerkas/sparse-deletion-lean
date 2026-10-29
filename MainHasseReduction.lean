import HasseCubicBridge
import PrimeFamily
import MainReduction

namespace SparseDeletion

noncomputable def primeSquarePass (r : ℕ) (b : ℤ) (x : ℕ) : Prop := by
  letI : Fact (largePrime r).Prime := ⟨largePrime_prime r⟩
  exact IsSquare ((primeCubicPoly (largePrime r) (b : ZMod (largePrime r))).eval
    (x : ZMod (largePrime r)))

theorem primeSquarePass_periodic (r : ℕ) (b : ℤ) (x : ℕ) :
    primeSquarePass r b (x % largePrime r) ↔ primeSquarePass r b x := by
  unfold primeSquarePass
  simp only [ZMod.natCast_mod]

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

/-- All logical and CRT steps are verified. The only remaining assumption is
the uniform cubic-character Hasse bound for this concrete prime family. -/
theorem main_of_concrete_hasse_bound
    (E : Set ℕ) (hE : HasDensityZero E)
    (hhasse : ∀ (r : ℕ) (b : ℤ),
      letI : Fact (largePrime r).Prime := ⟨largePrime_prime r⟩
      (quadraticCharSum
          (fun z : ZMod (largePrime r) =>
            (primeCubicPoly (largePrime r) (b : ZMod (largePrime r))).eval z) : ℝ) ≤
        2 * Real.sqrt (largePrime r : ℝ)) :
    HasDensityZero { n : ℕ | Triangular (keptIndexPrefix E n) } := by
  classical
  apply zeroDensityByIndex_of_modular_family
    largePrime primeSquarePass largePrime_positive largePrime_coprime_previous
  · intro r b x
    exact primeSquarePass_periodic r b x
  · intro r b
    letI : Fact (largePrime r).Prime := ⟨largePrime_prime r⟩
    have hprime := primeCubic_sieve_of_hasse (largePrime r) (largePrime_ge r)
      (b : ZMod (largePrime r)) (hhasse r b)
    have hpred (x : ℕ) : primeSquarePass r b x ↔
        IsSquare ((primeCubicPoly (largePrime r)
          (b : ZMod (largePrime r))).eval (x : ZMod (largePrime r))) := by
      unfold primeSquarePass
      rfl
    have heq : ((Finset.range (largePrime r)).filter (primeSquarePass r b)) =
        ((Finset.range (largePrime r)).filter
          (fun x : ℕ => IsSquare ((primeCubicPoly (largePrime r)
            (b : ZMod (largePrime r))).eval (x : ZMod (largePrime r))))) := by
      ext x
      simp only [Finset.mem_filter, hpred]
    rw [heq]
    exact hprime
  · intro r b x ht
    exact primeSquarePass_of_triangular r b x ht
  · exact hE

#print axioms primeSquarePass_periodic
#print axioms primeSquarePass_of_triangular
#print axioms main_of_concrete_hasse_bound

end SparseDeletion
