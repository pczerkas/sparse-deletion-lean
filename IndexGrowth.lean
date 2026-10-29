import IndexBridge
import Mathlib.Analysis.SpecificLimits.Basic

open Filter

namespace SparseDeletion

noncomputable def excludedCount (E : Set ℕ) (N : ℕ) : ℕ := by
  classical
  exact Nat.count (fun x => x ∈ E) N

noncomputable def excludedOne (E : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact if n ∈ E then 1 else 0

noncomputable def keptOne (E : Set ℕ) (n : ℕ) : ℕ := by
  classical
  exact if keptPred E n then 1 else 0

theorem countUpTo_eq_excludedCount (E : Set ℕ) (N : ℕ) :
    countUpTo E N = excludedCount E N := by
  classical
  simp [countUpTo, excludedCount, Nat.count_eq_card_filter_range]

theorem countUpTo_succ (E : Set ℕ) (n : ℕ) :
    countUpTo E (n + 1) = countUpTo E n + excludedOne E n := by
  classical
  rw [countUpTo_eq_excludedCount, countUpTo_eq_excludedCount]
  simpa only [excludedCount, excludedOne] using
    Nat.count_succ (fun x => x ∈ E) n

theorem keptCount_succ (E : Set ℕ) (n : ℕ) :
    keptCount E (n + 1) = keptCount E n + keptOne E n := by
  classical
  simpa only [keptCount, keptOne] using Nat.count_succ (keptPred E) n

/-- 0 is the only natural possibly counted by neither E nor the kept positives. -/
theorem kept_count_partition (E : Set ℕ) (N : ℕ) :
    N ≤ countUpTo E N + keptCount E N + 1 := by
  induction N with
  | zero =>
      simp [countUpTo, keptCount]
  | succ n ih =>
      rw [countUpTo_succ, keptCount_succ]
      by_cases hz : n = 0
      · subst n
        simp [keptPred, excludedOne, keptOne, countUpTo, keptCount]
      · by_cases he : n ∈ E
        · have hp : ¬keptPred E n := by simp [keptPred, he]
          simp only [excludedOne, keptOne, if_pos he, if_neg hp, add_zero]
          omega
        · have hp : keptPred E n := by simp [keptPred, he, Nat.pos_of_ne_zero hz]
          simp only [excludedOne, keptOne, if_neg he, if_pos hp, add_zero]
          omega

/-- A zero-density deletion removes less than a quarter of the first N
integers, for all sufficiently large positive N. -/
theorem eventually_removed_quarter (E : Set ℕ) (hE : HasDensityZero E) :
    ∀ᶠ N : ℕ in atTop, 4 * countUpTo E N ≤ N := by
  have hlt : ∀ᶠ N : ℕ in atTop,
      (countUpTo E N : ℝ) / (N : ℝ) < (1 : ℝ) / 4 :=
    hE.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hlt, eventually_gt_atTop (0 : ℕ)] with N hlt hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hh : (4 : ℝ) * (countUpTo E N : ℝ) < (N : ℝ) := by
    have := (div_lt_iff₀ hNr).1 hlt
    nlinarith
  exact_mod_cast (le_of_lt hh)

/-- Near N=2n+2, more than n positive integers survive sparse deletion. -/
theorem eventually_keptCount_gt (E : Set ℕ) (hE : HasDensityZero E) :
    ∀ᶠ n : ℕ in atTop, n < keptCount E (2 * n + 2) := by
  obtain ⟨T, hT⟩ :=
    Filter.eventually_atTop.1 (eventually_removed_quarter E hE)
  apply Filter.eventually_atTop.2
  refine ⟨max T 2, ?_⟩
  intro n hn
  have hlarge : T ≤ 2 * n + 2 := by omega
  have hsmall : 4 * countUpTo E (2 * n + 2) ≤ 2 * n + 2 :=
    hT (2 * n + 2) hlarge
  have hpart := kept_count_partition E (2 * n + 2)
  omega

/-- The positive integers outside a zero-density set form an infinite set. -/
theorem keptPred_infinite (E : Set ℕ) (hE : HasDensityZero E) :
    (Set.ofPred (keptPred E)).Infinite := by
  classical
  intro hf
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 (eventually_keptCount_gt E hE)
  let n := max T hf.toFinset.card
  have hn : n < keptCount E (2 * n + 2) := hT n (le_max_left _ _)
  have hbound : keptCount E (2 * n + 2) ≤ hf.toFinset.card := by
    simpa [keptCount] using Nat.count_le_card hf (2 * n + 2)
  have hlarge : hf.toFinset.card ≤ n := le_max_right _ _
  omega

/-- Every sufficiently large index n has its n-th retained positive
integer below 2n+2. -/
theorem eventually_keptNth_lt_twice (E : Set ℕ) (hE : HasDensityZero E) :
    ∀ᶠ n : ℕ in atTop, keptNth E n < 2 * n + 2 := by
  classical
  have he := eventually_removed_quarter E hE
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.1 he
  apply Filter.eventually_atTop.2
  refine ⟨max T 2, ?_⟩
  intro n hn
  let X := 2 * n + 2
  have hlarge : T ≤ X := by dsimp [X]; omega
  have hsmall : 4 * countUpTo E X ≤ X := hT X hlarge
  have hpart := kept_count_partition E X
  have hcount : n < keptCount E X := by
    dsimp [X] at *
    omega
  have hlt' : Nat.nth (keptPred E) n < X := by
    apply Nat.nth_lt_of_lt_count
    simpa [keptCount] using hcount
  simpa only [keptNth_eq_nth] using hlt'

end SparseDeletion

#print axioms SparseDeletion.kept_count_partition
#print axioms SparseDeletion.eventually_keptNth_lt_twice
#print axioms SparseDeletion.keptPred_infinite
