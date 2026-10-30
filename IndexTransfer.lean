module -- shake: keep-all

public import IndexGrowth
public import AsymptoticThree
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

open Filter

namespace SparseDeletion

/-- Map index 0 to the value 0, and index (n+1) to the n-th surviving positive integer. -/
noncomputable def indexToValue (E : Set ℕ) (n : ℕ) : ℕ :=
  match n with
  | 0 => 0
  | k + 1 => keptNth E k

theorem indexToValue_zero (E : Set ℕ) : indexToValue E 0 = 0 := rfl

theorem indexToValue_succ (E : Set ℕ) (n : ℕ) :
    indexToValue E (n + 1) = keptNth E n := rfl

theorem indexToValue_injective (E : Set ℕ)
    (hInf : (Set.ofPred (keptPred E)).Infinite) :
    Function.Injective (indexToValue E) := by
  intro n m h
  cases n with
  | zero =>
      cases m with
      | zero => rfl
      | succ m =>
          have hm : keptPred E (keptNth E m) := by
            rw [keptNth_eq_nth]
            exact Nat.nth_mem_of_infinite hInf m
          simp only [indexToValue_zero, indexToValue_succ] at h
          have hp : 0 < keptNth E m := hm.1
          omega
  | succ n =>
      cases m with
      | zero =>
          have hn : keptPred E (keptNth E n) := by
            rw [keptNth_eq_nth]
            exact Nat.nth_mem_of_infinite hInf n
          simp only [indexToValue_zero, indexToValue_succ] at h
          have hp : 0 < keptNth E n := hn.1
          omega
      | succ m =>
          simp only [indexToValue_succ] at h
          have hinj : Function.Injective (Nat.nth (keptPred E)) :=
            Nat.nth_injective hInf
          have h' : Nat.nth (keptPred E) n = Nat.nth (keptPred E) m := by
            exact h
          exact congrArg Nat.succ (hinj h')

theorem indexToValue_lt (E : Set ℕ)
    (hInf : (Set.ofPred (keptPred E)).Infinite)
    (N : ℕ) (hbound : keptNth E N < 2 * N + 2) :
    ∀ n < N + 1, indexToValue E n < 2 * N + 2 := by
  intro n hn
  cases n with
  | zero => simp [indexToValue_zero]
  | succ k =>
      rw [indexToValue_succ]
      have hk : k ≤ N := by omega
      have hmono : Monotone (Nat.nth (keptPred E)) :=
        (Nat.nth_strictMono hInf).monotone
      have hle : keptNth E k ≤ keptNth E N := by
        exact hmono hk
      exact lt_of_le_of_lt hle hbound

theorem indexToValue_hits (E : Set ℕ)
    (hInf : (Set.ofPred (keptPred E)).Infinite) (n : ℕ) :
    Triangular (keptIndexPrefix E n) →
      indexToValue E n ∈ hitSet E := by
  intro hn
  cases n with
  | zero =>
      simp only [indexToValue_zero, hitSet]
      simp [keptSquaresUpTo, Triangular]
  | succ k =>
      simp only [indexToValue_succ, hitSet]
      rw [keptIndexPrefix_succ_eq_keptSquaresUpTo E hInf] at hn
      exact hn

/-! An exact injection from triangular index hits into triangular value hits. -/
def indexHitSet (E : Set ℕ) : Set ℕ :=
  {n | Triangular (keptIndexPrefix E n)}

theorem indexHit_count_le_value_count
    (E : Set ℕ) (hInf : (Set.ofPred (keptPred E)).Infinite)
    (N : ℕ) (hbound : keptNth E N < 2 * N + 2) :
    countUpTo (indexHitSet E) (N + 1) ≤
      countUpTo (hitSet E) (2 * N + 2) := by
  classical
  unfold countUpTo
  apply Finset.card_le_card_of_injOn (indexToValue E)
  · intro n hn
    obtain ⟨hmem, hhit⟩ := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      apply indexToValue_lt E hInf N hbound
      exact Finset.mem_range.mp hmem
    · exact indexToValue_hits E hInf n hhit
  · intro n _ m _ hnm
    exact indexToValue_injective E hInf hnm


/-- The index-value bridge: zero density among values implies zero density
among enumeration indices. No polynomial sieve is assumed here. -/
theorem zeroDensityByIndex_of_value_density
    (E : Set ℕ) (hE : HasDensityZero E)
    (hV : HasDensityZero (hitSet E)) :
    HasDensityZero (indexHitSet E) := by
  have hInf := keptPred_infinite E hE
  have hbound := eventually_keptNth_lt_twice E hE
  have hmap : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    filter_upwards [eventually_ge_atTop B] with n hn
    omega
  have hval : Tendsto
      (fun n : ℕ =>
        (countUpTo (hitSet E) (2 * (n + 1)) : ℝ) / (2 * (n + 1) : ℕ))
      atTop (nhds (0 : ℝ)) := hV.comp hmap
  have hupper : Tendsto
      (fun n : ℕ => (2 : ℝ) *
        ((countUpTo (hitSet E) (2 * (n + 1)) : ℝ) / (2 * (n + 1) : ℕ)))
      atTop (nhds (0 : ℝ)) := by
    simpa using hval.const_mul (2 : ℝ)
  have hle : ∀ᶠ n : ℕ in atTop,
      (countUpTo (indexHitSet E) (n + 1) : ℝ) / (n + 1 : ℕ) ≤
        (2 : ℝ) *
          ((countUpTo (hitSet E) (2 * (n + 1)) : ℝ) /
            (2 * (n + 1) : ℕ)) := by
    filter_upwards [hbound] with n hn
    have hc : countUpTo (indexHitSet E) (n + 1) ≤
        countUpTo (hitSet E) (2 * (n + 1)) := by
      simpa only [show 2 * n + 2 = 2 * (n + 1) by omega] using
        indexHit_count_le_value_count E hInf n hn
    have hcast : (countUpTo (indexHitSet E) (n + 1) : ℝ) ≤
        (countUpTo (hitSet E) (2 * (n + 1)) : ℝ) := by
      exact_mod_cast hc
    have hnpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    calc
      (countUpTo (indexHitSet E) (n + 1) : ℝ) / (n + 1 : ℕ) ≤
          (countUpTo (hitSet E) (2 * (n + 1)) : ℝ) / (n + 1 : ℕ) :=
        div_le_div_of_nonneg_right hcast hnpos.le
      _ = (2 : ℝ) *
            ((countUpTo (hitSet E) (2 * (n + 1)) : ℝ) /
             (2 * (n + 1) : ℕ)) := by
        push_cast
        field_simp
  have hshift : Tendsto
      (fun n : ℕ =>
        (countUpTo (indexHitSet E) (n + 1) : ℝ) / (n + 1 : ℕ))
      atTop (nhds (0 : ℝ)) := by
    apply tendsto_order.2
    constructor
    · intro a ha
      exact Filter.Eventually.of_forall (fun n => by
        have hh : (0 : ℝ) ≤
            (countUpTo (indexHitSet E) (n + 1) : ℝ) / (n + 1 : ℕ) :=
          div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
        exact lt_of_lt_of_le ha hh)
    · intro a ha
      have hsmall : ∀ᶠ n : ℕ in atTop,
          (2 : ℝ) *
            ((countUpTo (hitSet E) (2 * (n + 1)) : ℝ) /
              (2 * (n + 1) : ℕ)) < a :=
        hupper.eventually (eventually_lt_nhds ha)
      filter_upwards [hle, hsmall] with n hn hsmall
      exact lt_of_le_of_lt hn hsmall
  exact (tendsto_add_atTop_iff_nat 1).mp hshift

#print axioms zeroDensityByIndex_of_value_density

/-- Any fixed CRT contraction numer/denom < 1 forces zero density of
    triangular hits after arbitrary density-zero deletion. -/
theorem zeroDensityByIndex_of_uniform_ratio_sieves
    (numer denom : ℕ) (hnum : 0 < numer) (hfrac : numer < denom)
    (E : Set ℕ) (hE : HasDensityZero E)
    (hsieves : ∀ r : ℕ, ∃ M : ℕ, 0 < M ∧
      ∀ (u : ℕ) (b : ℤ),
        denom ^ r * (cubicCandidates u M b).card ≤ numer ^ r * M) :
    HasDensityZero { n : ℕ | Triangular (keptIndexPrefix E n) } := by
  change HasDensityZero (indexHitSet E)
  exact zeroDensityByIndex_of_value_density E hE
    (zeroDensityByValue_of_uniform_ratio_sieves numer denom
      hnum hfrac E hE hsieves)

#print axioms zeroDensityByIndex_of_uniform_ratio_sieves

/-- Unconditional quantitative bound on triangular hits by enumeration index,
using the three explicitly checked primes 31, 37 and 41. -/
theorem eventually_index_count_bound_three (E : Set ℕ)
    (hE : HasDensityZero E) :
    ∀ᶠ n : ℕ in atTop,
      countUpTo (indexHitSet E) (n + 1) ≤
        13608 * ((2 * n + 2) / 47027) +
        47027 * countUpTo E (2 * n + 2) +
        (2 * n + 2) % 47027 := by
  have hInf := keptPred_infinite E hE
  filter_upwards [eventually_keptNth_lt_twice E hE] with n hn
  calc
    countUpTo (indexHitSet E) (n + 1) ≤
        countUpTo (hitSet E) (2 * n + 2) :=
      indexHit_count_le_value_count E hInf n hn
    _ ≤ 13608 * ((2 * n + 2) / 47027) +
        47027 * countUpTo E (2 * n + 2) +
        (2 * n + 2) % 47027 :=
      hit_count_bound E (2 * n + 2)

#print axioms eventually_index_count_bound_three


/-- A fully verified nontrivial asymptotic upper-density bound for index
hits.  The factor 2 comes from a coarse bound on the n-th surviving value. -/
theorem eventually_index_density_le_three
    (E : Set ℕ) (hE : HasDensityZero E)
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      (countUpTo (indexHitSet E) N : ℝ) / (N : ℝ) ≤
      2 * ((13608 : ℝ) / 47027) + ε := by
  have hInf := keptPred_infinite E hE
  have hmap : Tendsto (fun n : ℕ => 2 * (n + 1)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    filter_upwards [eventually_ge_atTop B] with n hn
    omega
  have hval : ∀ᶠ n : ℕ in atTop,
      (countUpTo (hitSet E) (2 * (n + 1)) : ℝ) /
        (2 * (n + 1) : ℕ) ≤
        (13608 : ℝ) / 47027 + ε / 2 :=
    hmap.eventually (eventually_hit_density_le_three E hE (ε / 2)
      (by linarith))
  have hshift : ∀ᶠ n : ℕ in atTop,
      (countUpTo (indexHitSet E) (n + 1) : ℝ) / (n + 1 : ℕ) ≤
        2 * ((13608 : ℝ) / 47027) + ε := by
    filter_upwards [eventually_keptNth_lt_twice E hE, hval] with n hb hv
    have hcount : countUpTo (indexHitSet E) (n + 1) ≤
        countUpTo (hitSet E) (2 * (n + 1)) := by
      simpa only [show 2 * n + 2 = 2 * (n + 1) by omega] using
        indexHit_count_le_value_count E hInf n hb
    have hc : (countUpTo (indexHitSet E) (n + 1) : ℝ) ≤
        (countUpTo (hitSet E) (2 * (n + 1)) : ℝ) := by
      exact_mod_cast hcount
    have hpos : (0 : ℝ) < (n + 1 : ℕ) := by positivity
    have hratio :
        (countUpTo (indexHitSet E) (n + 1) : ℝ) / (n + 1 : ℕ) ≤
          (2 : ℝ) *
            ((countUpTo (hitSet E) (2 * (n + 1)) : ℝ) /
               (2 * (n + 1) : ℕ)) := by
      calc
        _ ≤ (countUpTo (hitSet E) (2 * (n + 1)) : ℝ) / (n + 1 : ℕ) :=
          div_le_div_of_nonneg_right hc hpos.le
        _ = _ := by push_cast; field_simp
    linarith
  have hfull : ∀ᶠ N : ℕ in Filter.map (fun n : ℕ => n + 1) atTop,
      (countUpTo (indexHitSet E) N : ℝ) / (N : ℝ) ≤
        2 * ((13608 : ℝ) / 47027) + ε := hshift
  simpa only [Filter.map_add_atTop_eq_nat] using hfull

#print axioms eventually_index_density_le_three


end SparseDeletion
