module -- shake: keep-all

public import MainUnconditionalValueSet
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace SparseDeletion

open Filter

attribute [local instance] Classical.propDecidable

def nonComposites : Set ℕ := {n : ℕ | n = 1 ∨ Nat.Prime n}

theorem prime_count_le_pi (N : ℕ) :
    countUpTo {n : ℕ | Nat.Prime n} N ≤ Nat.primeCounting N := by
  rw [countUpTo, Nat.primeCounting, Nat.primeCounting',
    Nat.count_eq_card_filter_range]
  exact Finset.card_le_card (by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn ⊢
    exact ⟨Nat.lt_succ_of_lt hn.1, hn.2⟩)

theorem prime_set_hasDensityZero :
    HasDensityZero {n : ℕ | Nat.Prime n} := by
  unfold HasDensityZero
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto
      (fun N : ℕ => (Real.log 4 + 1) / Real.log (N : ℝ))
      atTop (nhds (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hlog
  have hbound_real :
      ∀ᶠ N : ℕ in atTop,
        ((Nat.primeCounting N : ℝ) : ℝ) ≤
        (Real.log 4 + 1) * (N : ℝ) / Real.log (N : ℝ) := by
    have hh := Chebyshev.eventually_primeCounting_le (ε := (1 : ℝ)) (by positivity)
    have hc := tendsto_natCast_atTop_atTop.eventually hh
    filter_upwards [hc] with N hN
    simpa only [Nat.floor_natCast] using hN
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun N => by
      have hnn : (0 : ℝ) ≤ (countUpTo {n : ℕ | Nat.Prime n} N : ℝ) / (N : ℝ) :=
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      exact lt_of_lt_of_le ha hnn)
  · intro a ha
    have hlim := hsmall.eventually (eventually_lt_nhds ha)
    filter_upwards [hlim, hbound_real,
      eventually_gt_atTop (1 : ℕ)] with N hlim hb hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hpn : (countUpTo {n : ℕ | Nat.Prime n} N : ℝ) ≤ (Nat.primeCounting N : ℝ) := by
      exact_mod_cast prime_count_le_pi N
    calc
      (countUpTo {n : ℕ | Nat.Prime n} N : ℝ) / (N : ℝ) ≤
          (Nat.primeCounting N : ℝ) / (N : ℝ) :=
        div_le_div_of_nonneg_right hpn hNpos.le
      _ ≤ (Real.log 4 + 1) / Real.log (N : ℝ) := by
        have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
        apply (div_le_iff₀ hNpos).2
        calc
          (Nat.primeCounting N : ℝ) ≤
              (Real.log 4 + 1) * (N : ℝ) / Real.log (N : ℝ) := hb
          _ = ((Real.log 4 + 1) / Real.log (N : ℝ)) * (N : ℝ) := by ring
      _ < a := hlim

theorem nonComposites_count_le (N : ℕ) :
    countUpTo nonComposites N ≤
      countUpTo {n : ℕ | Nat.Prime n} N + 1 := by
  classical
  let A := (Finset.range N).filter (fun n : ℕ => n = 1)
  let B := (Finset.range N).filter (fun n : ℕ => Nat.Prime n)
  have hA : A.card ≤ 1 := by
    have ha : A ⊆ ({1} : Finset ℕ) := by
      intro n hn
      have h := (Finset.mem_filter.mp hn).2
      simp [h]
    simpa using Finset.card_le_card ha
  have heq : (Finset.range N).filter
      (fun n : ℕ => n = 1 ∨ Nat.Prime n) = A ∪ B := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, A, B]
    tauto
  have hAB := Finset.card_union_le A B
  have hc : ((Finset.range N).filter
      (fun n : ℕ => n = 1 ∨ Nat.Prime n)).card ≤ B.card + 1 := by
    rw [heq]
    omega
  simpa only [countUpTo, nonComposites, B, Set.mem_setOf_eq] using hc

theorem nonComposites_hasDensityZero :
    HasDensityZero nonComposites := by
  unfold HasDensityZero
  have hP := prime_set_hasDensityZero
  unfold HasDensityZero at hP
  have h1 : Tendsto (fun N : ℕ => (1 : ℝ) / (N : ℝ))
      atTop (nhds (0 : ℝ)) :=
    tendsto_const_div_atTop_nhds_zero_nat 1
  have hupper : Tendsto
      (fun N : ℕ => (countUpTo {n : ℕ | Nat.Prime n} N : ℝ) / (N : ℝ) +
        (1 : ℝ) / (N : ℝ)) atTop (nhds (0 : ℝ)) := by
    convert hP.add h1 using 1; simp
  apply tendsto_order.2
  constructor
  · intro a ha
    exact Filter.Eventually.of_forall (fun N => by
      have hnn : (0 : ℝ) ≤ (countUpTo nonComposites N : ℝ) / (N : ℝ) :=
        div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      exact lt_of_lt_of_le ha hnn)
  · intro a ha
    have hlim := hupper.eventually (eventually_lt_nhds ha)
    filter_upwards [hlim, eventually_gt_atTop (0 : ℕ)] with N hlim hN
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hbound : (countUpTo nonComposites N : ℝ) ≤
        (countUpTo {n : ℕ | Nat.Prime n} N : ℝ) + 1 := by
      exact_mod_cast nonComposites_count_le N
    calc
      (countUpTo nonComposites N : ℝ) / (N : ℝ) ≤
          ((countUpTo {n : ℕ | Nat.Prime n} N : ℝ) + 1) / (N : ℝ) :=
        div_le_div_of_nonneg_right hbound hNpos.le
      _ = (countUpTo {n : ℕ | Nat.Prime n} N : ℝ) / (N : ℝ) +
            (1 : ℝ) / (N : ℝ) := by ring
      _ < a := hlim

/-- The specific corollary for ascending composite numbers. -/
theorem composite_square_prefix_triangular_density_zero :
    HasDensityZero { n : ℕ |
      Triangular (keptIndexPrefix nonComposites n) } :=
  main_sparse_deletion_unconditional nonComposites nonComposites_hasDensityZero

#print axioms prime_set_hasDensityZero
#print axioms nonComposites_hasDensityZero
#print axioms composite_square_prefix_triangular_density_zero

end SparseDeletion
