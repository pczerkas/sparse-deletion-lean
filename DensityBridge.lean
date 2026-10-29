import GeneralBlocks
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.OrderClosed

open Filter

namespace SparseDeletion

/-- General finite bound after clearing the modulus denominator. -/
theorem hit_count_bound_scaled (E : Set ℕ) (M C N : ℕ)
    (hM : 0 < M)
    (hsieve : ∀ v : ℕ, ∀ b : ℤ, (cubicCandidates v M b).card ≤ C) :
    M * countUpTo (hitSet E) N ≤
      C * N + M * M * countUpTo E N + M * M := by
  have hb := hit_count_bound_general E M C N hM hsieve
  have hdiv : M * (N / M) ≤ N := by
    simpa [mul_comm] using Nat.div_mul_le_self N M
  have hrem : N % M ≤ M := (Nat.mod_lt N hM).le
  have hfloor : C * (M * (N / M)) ≤ C * N :=
    Nat.mul_le_mul_left C hdiv
  have hrest : M * (N % M) ≤ M * M :=
    Nat.mul_le_mul_left M hrem
  calc
    M * countUpTo (hitSet E) N ≤
      M * (C * (N / M) + M * countUpTo E N + N % M) :=
        Nat.mul_le_mul_left M hb
    _ = C * (M * (N / M)) + M * M * countUpTo E N +
        M * (N % M) := by ring
    _ ≤ C * N + M * M * countUpTo E N + M * M := by omega

theorem hit_ratio_bound (E : Set ℕ) (M C N : ℕ)
    (hM : 0 < M) (hN : 0 < N)
    (hsieve : ∀ v : ℕ, ∀ b : ℤ, (cubicCandidates v M b).card ≤ C) :
    (countUpTo (hitSet E) N : ℝ) / (N : ℝ) ≤
      (C : ℝ) / (M : ℝ) +
      (M : ℝ) * ((countUpTo E N : ℝ) / (N : ℝ)) +
      (M : ℝ) / (N : ℝ) := by
  have hnat := hit_count_bound_scaled E M C N hM hsieve
  have hs : (M : ℝ) * (countUpTo (hitSet E) N : ℝ) ≤
      (C : ℝ) * (N : ℝ) +
      (M : ℝ) * (M : ℝ) * (countUpTo E N : ℝ) +
      (M : ℝ) * (M : ℝ) := by
    exact_mod_cast hnat
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  -- The following is multiplication of both sides by the positive product M*N.
  apply (div_le_iff₀ hn).2
  have heq : ((C : ℝ) / M +
       (M : ℝ) * ((countUpTo E N : ℝ) / N) +
       (M : ℝ) / N) * N * M =
       (C : ℝ) * N + (M : ℝ) * M * (countUpTo E N : ℝ) +
       (M : ℝ) * M := by
    field_simp [ne_of_gt hm, ne_of_gt hn]
  have hsub : (countUpTo (hitSet E) N : ℝ) * M ≤
      (((C : ℝ) / M +
       (M : ℝ) * ((countUpTo E N : ℝ) / N) +
       (M : ℝ) / N) * N) * M := by
    rw [heq]
    nlinarith [hs]
  exact (le_of_mul_le_mul_right hsub hm)


/-- Every uniform finite sieve yields an asymptotic upper-density bound. -/
theorem eventually_hit_ratio_le (E : Set ℕ) (hE : HasDensityZero E)
    (M C : ℕ) (hM : 0 < M)
    (hsieve : ∀ v : ℕ, ∀ b : ℤ, (cubicCandidates v M b).card ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (countUpTo (hitSet E) N : ℝ) / (N : ℝ) ≤
        (C : ℝ) / (M : ℝ) + ε := by
  have hmul : Tendsto
      (fun N : ℕ => (M : ℝ) * ((countUpTo E N : ℝ) / (N : ℝ)))
      atTop (nhds (0 : ℝ)) := by
    simpa using hE.const_mul (M : ℝ)
  have htail : Tendsto (fun N : ℕ => (M : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat (M : ℝ)
  have hsum : Tendsto (fun N : ℕ =>
      (M : ℝ) * ((countUpTo E N : ℝ) / (N : ℝ)) +
      (M : ℝ) / (N : ℝ)) atTop (nhds (0 : ℝ)) := by
    convert hmul.add htail using 1 <;> simp
  have hlt : ∀ᶠ N : ℕ in atTop,
      (M : ℝ) * ((countUpTo E N : ℝ) / (N : ℝ)) +
      (M : ℝ) / (N : ℝ) < ε :=
    hsum.eventually (eventually_lt_nhds hε)
  filter_upwards [hlt, eventually_gt_atTop (0 : ℕ)] with N hsmall hN
  have hbound := hit_ratio_bound E M C N hM hN hsieve
  linarith

end SparseDeletion

#print axioms SparseDeletion.hit_ratio_bound
#print axioms SparseDeletion.eventually_hit_ratio_le
