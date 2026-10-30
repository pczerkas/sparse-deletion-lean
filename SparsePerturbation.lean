module -- shake: keep-all

public import CountingDensity
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.OrderClosed

@[expose] public section

open Filter

namespace SparseDeletion

/-!
# Sparse perturbations of a uniformly rare sequence

The target set `A` and base function `f` are arbitrary. A perturbation
`d` may have large values; its only regularity is that it is locally constant
away from a set `E` of density zero.

No polynomial, triangular number, finite-field or CRT assumption occurs
in this theorem. These enter only when instantiating the uniform sieve.
-/

def perturbHitSet (f d : ℕ → ℤ) (A : Set ℤ) : Set ℕ :=
  {n : ℕ | f n + d n ∈ A}

noncomputable def perturbCandidates (f : ℕ → ℤ) (A : Set ℤ)
    (u M : ℕ) (b : ℤ) : Finset ℕ := by
  classical
  exact (Finset.Ico u (u + M)).filter (fun n => f n + b ∈ A)

theorem perturb_constant_on_clean (d : ℕ → ℤ) (E : Set ℕ)
    (hstep : ∀ n : ℕ, n + 1 ∉ E → d (n + 1) = d n)
    (u x : ℕ) (hux : u ≤ x)
    (hclean : ∀ k : ℕ, u < k → k ≤ x → k ∉ E) :
    d x = d u := by
  induction x, hux using Nat.le_induction with
  | base => rfl
  | succ n hle ih =>
    have hprev : ∀ k : ℕ, u < k → k ≤ n → k ∉ E := by
      intro k hk hk'
      exact hclean k hk (by omega)
    have hnot : n + 1 ∉ E := hclean (n + 1) (by omega) (by omega)
    rw [hstep n hnot, ih hprev]

theorem perturb_clean_block (f d : ℕ → ℤ) (A : Set ℤ)
    (E : Set ℕ) (hstep : ∀ n : ℕ, n + 1 ∉ E → d (n + 1) = d n)
    (u M C : ℕ)
    (hclean : ∀ k : ℕ, u < k → k < u + M → k ∉ E)
    (hsieve : ∀ v : ℕ, ∀ b : ℤ,
      (perturbCandidates f A v M b).card ≤ C) :
    selectedCount (perturbHitSet f d A) u (u + M) ≤ C := by
  classical
  have hsub : ((Finset.Ico u (u + M)).filter
    (fun n => n ∈ perturbHitSet f d A)) ⊆
      perturbCandidates f A u M (d u) := by
    intro n hn
    obtain ⟨hinterval, hhit⟩ := Finset.mem_filter.mp hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ico.mp hinterval
    have hd : d n = d u :=
      perturb_constant_on_clean d E hstep u n hlo (by
        intro k hk hk'
        exact hclean k hk (by omega))
    exact Finset.mem_filter.mpr ⟨hinterval, by
      change f n + d n ∈ A at hhit
      simpa only [hd] using hhit⟩
  change (((Finset.Ico u (u + M)).filter
    (fun n => n ∈ perturbHitSet f d A)).card) ≤ C
  exact (Finset.card_le_card hsub).trans (hsieve u (d u))

theorem perturb_block_bound (f d : ℕ → ℤ) (A : Set ℤ)
    (E : Set ℕ) (hstep : ∀ n : ℕ, n + 1 ∉ E → d (n + 1) = d n)
    (M C u : ℕ)
    (hsieve : ∀ v : ℕ, ∀ b : ℤ,
      (perturbCandidates f A v M b).card ≤ C) :
    selectedCount (perturbHitSet f d A) u (u + M) ≤
      C + M * selectedCount E u (u + M) := by
  classical
  by_cases hn : selectedCount E u (u + M) = 0
  · have hclean : ∀ k : ℕ, u < k → k < u + M → k ∉ E := by
      intro k hu hk hmem
      have hfin : k ∈ (Finset.Ico u (u + M)).filter
          (fun x => x ∈ E) :=
        Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, hk⟩, hmem⟩
      have hpos : 0 < selectedCount E u (u + M) :=
        Finset.card_pos.mpr ⟨k, hfin⟩
      omega
    have hb := perturb_clean_block f d A E hstep u M C hclean hsieve
    omega
  · have hpos : 1 ≤ selectedCount E u (u + M) := by omega
    have hbound : selectedCount (perturbHitSet f d A) u (u + M) ≤ M := by
      unfold selectedCount
      exact (Finset.card_filter_le _ _).trans (by simp)
    have hmul : M ≤ M * selectedCount E u (u + M) := by
      simpa using Nat.mul_le_mul_left M hpos
    omega

theorem perturb_count_mul (f d : ℕ → ℤ) (A : Set ℤ)
    (E : Set ℕ) (hstep : ∀ n : ℕ, n + 1 ∉ E → d (n + 1) = d n)
    (M C k : ℕ)
    (hsieve : ∀ v : ℕ, ∀ b : ℤ,
      (perturbCandidates f A v M b).card ≤ C) :
    countUpTo (perturbHitSet f d A) (M * k) ≤
      C * k + M * countUpTo E (M * k) := by
  induction k with
  | zero => simp [countUpTo]
  | succ k ih =>
    have hmul : M * (k + 1) = M * k + M := by ring
    have hH : countUpTo (perturbHitSet f d A) (M * (k + 1)) =
      countUpTo (perturbHitSet f d A) (M * k) +
        selectedCount (perturbHitSet f d A) (M * k) (M * k + M) := by
      rw [hmul, countUpTo_eq_selectedCount, countUpTo_eq_selectedCount]
      exact selectedCount_add (perturbHitSet f d A) (M * k) M
    have hE : countUpTo E (M * (k + 1)) =
      countUpTo E (M * k) + selectedCount E (M * k) (M * k + M) := by
      rw [hmul, countUpTo_eq_selectedCount, countUpTo_eq_selectedCount]
      exact selectedCount_add E (M * k) M
    have hb := perturb_block_bound f d A E hstep M C (M * k) hsieve
    rw [hH, hE]
    calc
      countUpTo (perturbHitSet f d A) (M * k) +
          selectedCount (perturbHitSet f d A) (M * k) (M * k + M) ≤
          (C * k + M * countUpTo E (M * k)) +
          (C + M * selectedCount E (M * k) (M * k + M)) :=
        Nat.add_le_add ih hb
      _ = C * (k + 1) +
          M * (countUpTo E (M * k) +
            selectedCount E (M * k) (M * k + M)) := by ring

theorem perturb_count_bound (f d : ℕ → ℤ) (A : Set ℤ)
    (E : Set ℕ) (hstep : ∀ n : ℕ, n + 1 ∉ E → d (n + 1) = d n)
    (M C N : ℕ) (_hM : 0 < M)
    (hsieve : ∀ v : ℕ, ∀ b : ℤ,
      (perturbCandidates f A v M b).card ≤ C) :
    countUpTo (perturbHitSet f d A) N ≤
      C * (N / M) + M * countUpTo E N + N % M := by
  classical
  let k := N / M
  let r := N % M
  have hN : M * k + r = N := by
    dsimp [k, r]
    simpa [add_comm] using Nat.mod_add_div N M
  have hbase := perturb_count_mul f d A E hstep M C k hsieve
  have hH : countUpTo (perturbHitSet f d A) N =
      countUpTo (perturbHitSet f d A) (M * k) +
        selectedCount (perturbHitSet f d A) (M * k) N := by
    calc
      countUpTo (perturbHitSet f d A) N =
        selectedCount (perturbHitSet f d A) 0 (M * k + r) := by
          rw [hN]; exact countUpTo_eq_selectedCount _ _
      _ = selectedCount (perturbHitSet f d A) 0 (M * k) +
            selectedCount (perturbHitSet f d A) (M * k) (M * k + r) :=
        selectedCount_add (perturbHitSet f d A) (M * k) r
      _ = countUpTo (perturbHitSet f d A) (M * k) +
            selectedCount (perturbHitSet f d A) (M * k) N := by
        rw [countUpTo_eq_selectedCount, hN]
  have hE : countUpTo E N =
      countUpTo E (M * k) + selectedCount E (M * k) N := by
    calc
      countUpTo E N = selectedCount E 0 (M * k + r) := by
        rw [hN]; exact countUpTo_eq_selectedCount _ _
      _ = selectedCount E 0 (M * k) +
            selectedCount E (M * k) (M * k + r) :=
        selectedCount_add E (M * k) r
      _ = countUpTo E (M * k) +
            selectedCount E (M * k) N := by
        rw [countUpTo_eq_selectedCount, hN]
  have hTail : selectedCount (perturbHitSet f d A) (M * k) N ≤ r := by
    unfold selectedCount
    calc
      ((Finset.Ico (M * k) N).filter (fun x => x ∈ perturbHitSet f d A)).card ≤
          (Finset.Ico (M * k) N).card :=
            Finset.card_filter_le _ _
      _ = r := by
        simp only [Nat.card_Ico]
        omega
  change countUpTo (perturbHitSet f d A) N ≤
    C * k + M * countUpTo E N + r
  rw [hH, hE]
  calc
    countUpTo (perturbHitSet f d A) (M * k) +
        selectedCount (perturbHitSet f d A) (M * k) N ≤
        (C * k + M * countUpTo E (M * k)) + r :=
      Nat.add_le_add hbase hTail
    _ ≤ C * k + M *
          (countUpTo E (M * k) + selectedCount E (M * k) N) + r := by
      have hmono : M * countUpTo E (M * k) ≤
          M * (countUpTo E (M * k) + selectedCount E (M * k) N) :=
        Nat.mul_le_mul_left M (Nat.le_add_right _ _)
      omega


theorem perturb_count_bound_scaled (f d : ℕ → ℤ) (A : Set ℤ)
    (E : Set ℕ) (hstep : ∀ n : ℕ, n + 1 ∉ E → d (n + 1) = d n)
    (M C N : ℕ) (hM : 0 < M)
    (hsieve : ∀ v : ℕ, ∀ b : ℤ,
      (perturbCandidates f A v M b).card ≤ C) :
    M * countUpTo (perturbHitSet f d A) N ≤
      C * N + M * M * countUpTo E N + M * M := by
  have hb := perturb_count_bound f d A E hstep M C N hM hsieve
  have hdiv : M * (N / M) ≤ N := by
    simpa [mul_comm] using Nat.div_mul_le_self N M
  have hrem : N % M ≤ M := (Nat.mod_lt N hM).le
  have hfloor : C * (M * (N / M)) ≤ C * N :=
    Nat.mul_le_mul_left C hdiv
  have hrest : M * (N % M) ≤ M * M :=
    Nat.mul_le_mul_left M hrem
  calc
    M * countUpTo (perturbHitSet f d A) N ≤
      M * (C * (N / M) + M * countUpTo E N + N % M) :=
        Nat.mul_le_mul_left M hb
    _ = C * (M * (N / M)) + M * M * countUpTo E N +
        M * (N % M) := by ring
    _ ≤ C * N + M * M * countUpTo E N + M * M := by omega

theorem perturb_ratio_bound (f d : ℕ → ℤ) (A : Set ℤ)
    (E : Set ℕ) (hstep : ∀ n : ℕ, n + 1 ∉ E → d (n + 1) = d n)
    (M C N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (hsieve : ∀ v : ℕ, ∀ b : ℤ,
      (perturbCandidates f A v M b).card ≤ C) :
    (countUpTo (perturbHitSet f d A) N : ℝ) / (N : ℝ) ≤
      (C : ℝ) / (M : ℝ) +
      (M : ℝ) * ((countUpTo E N : ℝ) / (N : ℝ)) +
      (M : ℝ) / (N : ℝ) := by
  have hnat := perturb_count_bound_scaled f d A E hstep M C N hM hsieve
  have hs : (M : ℝ) * (countUpTo (perturbHitSet f d A) N : ℝ) ≤
      (C : ℝ) * (N : ℝ) +
      (M : ℝ) * (M : ℝ) * (countUpTo E N : ℝ) +
      (M : ℝ) * (M : ℝ) := by
    exact_mod_cast hnat
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  apply (div_le_iff₀ hn).2
  have heq : ((C : ℝ) / M +
       (M : ℝ) * ((countUpTo E N : ℝ) / N) +
       (M : ℝ) / N) * N * M =
       (C : ℝ) * N + (M : ℝ) * M * (countUpTo E N : ℝ) +
       (M : ℝ) * M := by
    field_simp [ne_of_gt hm, ne_of_gt hn]
  have hsub : (countUpTo (perturbHitSet f d A) N : ℝ) * M ≤
      (((C : ℝ) / M +
       (M : ℝ) * ((countUpTo E N : ℝ) / N) +
       (M : ℝ) / N) * N) * M := by
    rw [heq]
    nlinarith [hs]
  exact le_of_mul_le_mul_right hsub hm

/-- For a fixed uniform sieve, the perturbed hit ratio is eventually at most
the clean-block hit ratio plus any positive error. -/
theorem eventually_perturb_ratio_le (f d : ℕ → ℤ) (A : Set ℤ)
    (E : Set ℕ) (hE : HasDensityZero E)
    (hstep : ∀ n : ℕ, n + 1 ∉ E → d (n + 1) = d n)
    (M C : ℕ) (hM : 0 < M)
    (hsieve : ∀ v : ℕ, ∀ b : ℤ,
      (perturbCandidates f A v M b).card ≤ C)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (countUpTo (perturbHitSet f d A) N : ℝ) / (N : ℝ) ≤
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
    convert hmul.add htail using 1; simp
  have hlt : ∀ᶠ N : ℕ in atTop,
      (M : ℝ) * ((countUpTo E N : ℝ) / (N : ℝ)) +
      (M : ℝ) / (N : ℝ) < ε :=
    hsum.eventually (eventually_lt_nhds hε)
  filter_upwards [hlt, eventually_gt_atTop (0 : ℕ)] with N hsmall hN
  have hbound := perturb_ratio_bound f d A E hstep M C N hM hN hsieve
  linarith

/-- Minimal abstract density transfer: for every epsilon, a common finite block
length has uniformly less than epsilon fraction of shifted hits.
The perturbation values themselves are unrestricted, but its jumps are sparse. -/
theorem sparsePerturbation_zeroDensity_of_uniform_small_blocks
    (f d : ℕ → ℤ) (A : Set ℤ)
    (E : Set ℕ) (hE : HasDensityZero E)
    (hstep : ∀ n : ℕ, n + 1 ∉ E → d (n + 1) = d n)
    (hsieves : ∀ ε : ℝ, 0 < ε → ∃ M C : ℕ, 0 < M ∧
       (C : ℝ) / (M : ℝ) < ε ∧
       ∀ (u : ℕ) (b : ℤ), (perturbCandidates f A u M b).card ≤ C) :
    HasDensityZero (perturbHitSet f d A) := by
  unfold HasDensityZero
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun N => by
      have hnonneg : 0 ≤
          (countUpTo (perturbHitSet f d A) N : ℝ) / (N : ℝ) :=
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      exact lt_of_lt_of_le ha hnonneg)
  · intro a ha
    obtain ⟨M, C, hM, hratio, hsieve⟩ := hsieves (a / 2) (by linarith)
    have happrox :=
      eventually_perturb_ratio_le f d A E hE hstep M C hM hsieve
        (a / 2) (by linarith)
    filter_upwards [happrox] with N hbound
    linarith

/-- The geometric CRT contraction is a sufficient criterion for the
minimal uniform-small-blocks hypothesis. -/
theorem sparsePerturbation_zeroDensity_of_uniform_ratio_sieves
    (numer denom : ℕ) (hnum : 0 < numer) (hfrac : numer < denom)
    (f d : ℕ → ℤ) (A : Set ℤ)
    (E : Set ℕ) (hE : HasDensityZero E)
    (hstep : ∀ n : ℕ, n + 1 ∉ E → d (n + 1) = d n)
    (hsieves : ∀ r : ℕ, ∃ M : ℕ, 0 < M ∧
       ∀ (u : ℕ) (b : ℤ),
          denom ^ r * (perturbCandidates f A u M b).card ≤ numer ^ r * M) :
    HasDensityZero (perturbHitSet f d A) := by
  apply sparsePerturbation_zeroDensity_of_uniform_small_blocks
    f d A E hE hstep
  intro ε hε
  have hdenom_pos : (0 : ℝ) < (denom : ℝ) := by
    exact_mod_cast (lt_trans hnum hfrac)
  have hfracR : (numer : ℝ) < (denom : ℝ) := by
    exact_mod_cast hfrac
  have hratioNonneg : 0 ≤ (numer : ℝ) / (denom : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hdenom_pos.le
  have hratioLt : (numer : ℝ) / (denom : ℝ) < 1 :=
    (div_lt_one hdenom_pos).2 hfracR
  have hgeo : Tendsto (fun r : ℕ => ((numer : ℝ) / denom) ^ r)
      atTop (nhds (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hratioNonneg hratioLt
  have hev : ∀ᶠ r : ℕ in atTop, ((numer : ℝ) / denom) ^ r < ε :=
    hgeo.eventually (eventually_lt_nhds hε)
  obtain ⟨r, hr⟩ := hev.exists
  obtain ⟨M, hM, hsieve⟩ := hsieves r
  let C : ℕ := (numer ^ r * M) / (denom ^ r)
  have hC : ∀ (u : ℕ) (b : ℤ),
      (perturbCandidates f A u M b).card ≤ C := by
    intro u b
    apply (Nat.le_div_iff_mul_le (pow_pos (lt_trans hnum hfrac) r)).2
    simpa only [C, mul_comm] using hsieve u b
  have hCscaled : denom ^ r * C ≤ numer ^ r * M := by
    dsimp [C]
    simpa [mul_comm] using Nat.div_mul_le_self (numer ^ r * M) (denom ^ r)
  have hreal : (denom : ℝ) ^ r * (C : ℝ) ≤
      (numer : ℝ) ^ r * (M : ℝ) := by
    exact_mod_cast hCscaled
  have hposM : (0 : ℝ) < M := by exact_mod_cast hM
  have hposDenom : (0 : ℝ) < (denom : ℝ) ^ r := pow_pos hdenom_pos _
  have hratio : (C : ℝ) / (M : ℝ) ≤ ((numer : ℝ) / denom) ^ r := by
    rw [div_pow]
    apply (div_le_div_iff₀ hposM hposDenom).2
    nlinarith [hreal]
  exact ⟨M, C, hM, lt_of_le_of_lt hratio hr, hC⟩

#print axioms sparsePerturbation_zeroDensity_of_uniform_small_blocks

#print axioms sparsePerturbation_zeroDensity_of_uniform_ratio_sieves

#print axioms perturb_count_bound

end SparseDeletion
