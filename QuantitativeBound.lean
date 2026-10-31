module -- shake: keep-all

public import IndexTransfer

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-!
# Quantitative upper bounds for triangular square-prefix hits

These estimates reuse the existing uniform shifted sieve and sparse-variation
lemma. Unlike a density theorem, they hold at each fixed finite N.
-/

/-- Finite upper bound for hits indexed by the original positive-integer value. -/
theorem quantitative_value_hit_bound
    (E : Set ℕ) (M C N : ℕ) (hM : 0 < M)
    (hsieve : ∀ (u : ℕ) (b : ℤ),
      (cubicCandidates u M b).card ≤ C) :
    countUpTo (hitSet E) N ≤
      C * (N / M) + M * countUpTo E N + N % M := by
  have hstep : ∀ n : ℕ, n + 1 ∉ E →
      (-removedSquareSum E (n + 1)) = -removedSquareSum E n := by
    intro n hnot
    rw [removedSquareSum_succ]
    simp [removedTerm, hnot]
  have hsieve' : ∀ (u : ℕ) (b : ℤ),
      (perturbCandidates naturalSquareSum
        {z : ℤ | TriangularInt z} u M b).card ≤ C := by
    intro u b
    change (cubicCandidates u M b).card ≤ C
    exact hsieve u b
  have hbound := perturb_count_bound naturalSquareSum
    (fun n => -removedSquareSum E n)
    {z : ℤ | TriangularInt z}
    E hstep M C N hM hsieve'
  have heq :
      perturbHitSet naturalSquareSum
        (fun n => -removedSquareSum E n)
        {z : ℤ | TriangularInt z} = hitSet E := by
    ext n
    change TriangularInt (naturalSquareSum n + -removedSquareSum E n) ↔
      Triangular (keptSquaresUpTo E n)
    rw [triangular_iff_triangularInt_cast,
      keptSquaresUpTo_cast_eq_shiftedRemaining]
    rfl
  rw [heq] at hbound
  exact hbound

/-- Finite bound for hits indexed by the surviving sequence. -/
theorem quantitative_index_hit_bound
    (E : Set ℕ) (hInf : (Set.ofPred (keptPred E)).Infinite)
    (N M C : ℕ) (hNth : keptNth E N < 2 * N + 2)
    (hM : 0 < M)
    (hsieve : ∀ (u : ℕ) (b : ℤ),
      (cubicCandidates u M b).card ≤ C) :
    countUpTo (indexHitSet E) (N + 1) ≤
      C * ((2 * N + 2) / M) +
        M * countUpTo E (2 * N + 2) +
        (2 * N + 2) % M := by
  exact (indexHit_count_le_value_count E hInf N hNth).trans
    (quantitative_value_hit_bound E M C (2 * N + 2) hM hsieve)

/-- Weaker but more convenient upper bound without the remainder. -/
theorem quantitative_value_hit_bound_simplified
    (E : Set ℕ) (M C N : ℕ) (hM : 0 < M)
    (hsieve : ∀ (u : ℕ) (b : ℤ),
      (cubicCandidates u M b).card ≤ C) :
    countUpTo (hitSet E) N ≤
      C * (N / M) + M * (countUpTo E N + 1) := by
  have h := quantitative_value_hit_bound E M C N hM hsieve
  have hrem : N % M ≤ M := (Nat.mod_lt N hM).le
  nlinarith


end SparseDeletion
