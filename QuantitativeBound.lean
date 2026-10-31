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


/-- A scaled finite-N inequality. The modular sieve needs only a
uniform bound `denom * C ≤ numer * M`; no density assumption. -/
theorem quantitative_value_hit_bound_scaled
    (E : Set ℕ) (numer denom M C N : ℕ) (hM : 0 < M)
    (hsieve : ∀ (u : ℕ) (b : ℤ),
      (cubicCandidates u M b).card ≤ C)
    (hratio : denom * C ≤ numer * M) :
    denom * countUpTo (hitSet E) N ≤
      numer * N + denom * M * (countUpTo E N + 1) := by
  have hb := quantitative_value_hit_bound E M C N hM hsieve
  have hdiv : M * (N / M) ≤ N := by
    simpa [mul_comm] using Nat.div_mul_le_self N M
  have hrem : N % M ≤ M := (Nat.mod_lt N hM).le
  have hterm : (denom * C) * (N / M) ≤ (numer * M) * (N / M) :=
    Nat.mul_le_mul_right (N / M) hratio
  have hlast : denom * (N % M) ≤ denom * M :=
    Nat.mul_le_mul_left denom hrem
  have hfirst : numer * (M * (N / M)) ≤ numer * N :=
    Nat.mul_le_mul_left numer hdiv
  calc
    denom * countUpTo (hitSet E) N ≤
        denom * (C * (N / M) + M * countUpTo E N + N % M) :=
      Nat.mul_le_mul_left denom hb
    _ = (denom * C) * (N / M) +
        denom * M * countUpTo E N + denom * (N % M) := by ring
    _ ≤ (numer * M) * (N / M) +
        denom * M * countUpTo E N + denom * M := by
      exact Nat.add_le_add (Nat.add_le_add hterm (le_refl _)) hlast
    _ = numer * (M * (N / M)) +
        denom * M * (countUpTo E N + 1) := by ring
    _ ≤ numer * N + denom * M * (countUpTo E N + 1) :=
      Nat.add_le_add_right hfirst _

/-- From a scaled modular candidate bound to a numerical count of hits. -/
theorem quantitative_value_hit_bound_of_scaled_sieve
    (E : Set ℕ) (numer denom M N : ℕ)
    (hM : 0 < M) (hdenom : 0 < denom)
    (hsieve : ∀ (u : ℕ) (b : ℤ),
      denom * (cubicCandidates u M b).card ≤ numer * M) :
    denom * countUpTo (hitSet E) N ≤
      numer * N + denom * M * (countUpTo E N + 1) := by
  let C : ℕ := numer * M / denom
  have hC : ∀ (u : ℕ) (b : ℤ),
      (cubicCandidates u M b).card ≤ C := by
    intro u b
    apply (Nat.le_div_iff_mul_le hdenom).2
    simpa only [C, mul_comm] using hsieve u b
  have hratio : denom * C ≤ numer * M := by
    dsimp [C]
    simpa [mul_comm] using Nat.div_mul_le_self (numer * M) denom
  exact quantitative_value_hit_bound_scaled E numer denom M C N hM hC hratio

/-- A uniform family of modular sieves yields a family of finite-N
upper bounds; the modulus may grow with the number of sieves. -/
theorem quantitative_value_hit_bound_of_sieve_family
    (E : Set ℕ) (numer denom : ℕ) (hdenom : 0 < denom)
    (hsieves : ∀ r : ℕ, ∃ M : ℕ, 0 < M ∧
      ∀ (u : ℕ) (b : ℤ),
        denom ^ r * (cubicCandidates u M b).card ≤ numer ^ r * M)
    (r N : ℕ) :
    ∃ M : ℕ, 0 < M ∧
      denom ^ r * countUpTo (hitSet E) N ≤
        numer ^ r * N + denom ^ r * M * (countUpTo E N + 1) := by
  obtain ⟨M, hM, hsieve⟩ := hsieves r
  exact ⟨M, hM,
    quantitative_value_hit_bound_of_scaled_sieve
      E (numer ^ r) (denom ^ r) M N hM (pow_pos hdenom r) hsieve⟩

/-- Finite-N modular bound transported from value indices to indices in
the surviving sequence. The survivor growth hypothesis is explicit. -/
theorem quantitative_index_hit_bound_of_scaled_sieve
    (E : Set ℕ) (hInf : (Set.ofPred (keptPred E)).Infinite)
    (numer denom M N : ℕ)
    (hNth : keptNth E N < 2 * N + 2)
    (hM : 0 < M) (hdenom : 0 < denom)
    (hsieve : ∀ (u : ℕ) (b : ℤ),
      denom * (cubicCandidates u M b).card ≤ numer * M) :
    denom * countUpTo (indexHitSet E) (N + 1) ≤
      numer * (2 * N + 2) +
        denom * M * (countUpTo E (2 * N + 2) + 1) := by
  have hcount := indexHit_count_le_value_count E hInf N hNth
  have hb := quantitative_value_hit_bound_of_scaled_sieve
    E numer denom M (2 * N + 2) hM hdenom hsieve
  exact (Nat.mul_le_mul_left denom hcount).trans hb


end SparseDeletion
