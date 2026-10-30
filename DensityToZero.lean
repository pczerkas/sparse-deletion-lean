module -- shake: keep-all

public import KeptSquaresBridge
public import SparseDeletion
public import SparsePerturbation

@[expose] public section

namespace SparseDeletion

/-- The arithmetic sieve specializes the generic sparse-perturbation theorem
to the cubic sum of consecutive squares and triangular target values. -/
theorem zeroDensityByValue_of_uniform_ratio_sieves
    (numer denom : ℕ) (hnum : 0 < numer) (hfrac : numer < denom)
    (E : Set ℕ)
    (hE : HasDensityZero E)
    (hsieves : ∀ r : ℕ, ∃ M : ℕ, 0 < M ∧
       ∀ (u : ℕ) (b : ℤ),
          denom ^ r * (cubicCandidates u M b).card ≤ numer ^ r * M) :
    HasDensityZero (hitSet E) := by
  have hstep : ∀ n : ℕ, n + 1 ∉ E →
      (-removedSquareSum E (n + 1)) = -removedSquareSum E n := by
    intro n hnot
    rw [removedSquareSum_succ]
    simp [removedTerm, hnot]
  have hsieves' : ∀ r : ℕ, ∃ M : ℕ, 0 < M ∧
      ∀ (u : ℕ) (b : ℤ),
        denom ^ r *
          (perturbCandidates naturalSquareSum {z : ℤ | TriangularInt z}
            u M b).card ≤ numer ^ r * M := by
    intro r
    obtain ⟨M, hM, hsieve⟩ := hsieves r
    refine ⟨M, hM, ?_⟩
    intro u b
    change denom ^ r * (cubicCandidates u M b).card ≤ numer ^ r * M
    exact hsieve u b
  have hgeneric :=
    sparsePerturbation_zeroDensity_of_uniform_ratio_sieves
      numer denom hnum hfrac
      naturalSquareSum (fun n => -removedSquareSum E n)
      {z : ℤ | TriangularInt z}
      E hE hstep hsieves'
  have heq :
      perturbHitSet naturalSquareSum (fun n => -removedSquareSum E n)
        {z : ℤ | TriangularInt z} = hitSet E := by
    ext n
    change TriangularInt (naturalSquareSum n + -removedSquareSum E n) ↔
      Triangular (keptSquaresUpTo E n)
    rw [triangular_iff_triangularInt_cast, keptSquaresUpTo_cast_eq_shiftedRemaining]
    rfl
  rwa [heq] at hgeneric

end SparseDeletion

#print axioms SparseDeletion.zeroDensityByValue_of_uniform_ratio_sieves
