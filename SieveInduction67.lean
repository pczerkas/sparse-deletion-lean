module -- shake: keep-all

public import SieveInduction

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-- Arbitrarily long products of uniformly 6/7-good periodic tests are
at most (6/7)^r dense over a complete product period, by CRT alone. -/
theorem crt_sieve_product_count67 (q : ℕ → ℕ) (P : ℕ → ℤ → ℕ → Prop)
    (hq : ∀ r, 0 < q r)
    (hcop : ∀ r, Nat.Coprime (modulusProd q r) (q r))
    (hper : ∀ r b x, P r b (x % q r) ↔ P r b x)
    (hgood : ∀ r b, 7 * ((Finset.range (q r)).filter (P r b)).card ≤ 6 * q r)
    (r : ℕ) (b : ℤ) :
    7 ^ r * ((Finset.range (modulusProd q r)).filter
      (passesProd P b r)).card ≤ 6 ^ r * modulusProd q r := by
  classical
  induction r with
  | zero =>
    have h := Finset.card_filter_le (Finset.range 1) (passesProd P b 0)
    simpa [modulusProd] using h
  | succ r ih =>
    let m := modulusProd q r
    let n := q r
    let A := ((Finset.range m).filter (passesProd P b r))
    let B := ((Finset.range n).filter (P r b))
    have hc :
        ((Finset.range (m * n)).filter
          (fun x => passesProd P b r x ∧ P r b x)).card ≤
          A.card * B.card := by
      have h := crt_periodic_intersection_bound m n 0
        (hcop r) (modulusProd_pos q hq r) (hq r)
        (passesProd P b r) (P r b)
        (by intro x hx; exact (passesProd_periodic q P hper r b x).mpr hx)
        (by intro x hx; exact (hper r b x).mpr hx)
      simpa only [Nat.zero_add, Nat.Ico_zero_eq_range, A, B] using h
    have ih' : 7 ^ r * A.card ≤ 6 ^ r * m := ih
    have hn : 7 * B.card ≤ 6 * n := hgood r b
    have hf :
        ((Finset.range (modulusProd q (r + 1))).filter
          (passesProd P b (r + 1))) =
        ((Finset.range (m * n)).filter
          (fun x => passesProd P b r x ∧ P r b x)) := by
      have hP : passesProd P b (r + 1) =
          (fun x => passesProd P b r x ∧ P r b x) := rfl
      have hM : modulusProd q (r + 1) = m * n := rfl
      rw [hP, hM]
      ext x
      simp only [Finset.mem_filter]
    rw [hf]
    change 7 ^ (r + 1) *
      ((Finset.range (m * n)).filter
        (fun x => passesProd P b r x ∧ P r b x)).card ≤
        6 ^ (r + 1) * (m * n)
    calc
      _ ≤ 7 ^ (r + 1) * (A.card * B.card) :=
        Nat.mul_le_mul_left _ hc
      _ = (7 ^ r * A.card) * (7 * B.card) := by
        rw [pow_succ]; ring
      _ ≤ (6 ^ r * m) * (6 * n) := Nat.mul_le_mul ih' hn
      _ = 6 ^ (r + 1) * (m * n) := by
        rw [pow_succ]; ring

/-- The abstract CRT iteration supplies the complete uniform cubic sieve
from a sequence of independently certified periodic modular obstructions. -/
theorem uniformCubicSieve67_of_modular_family
    (q : ℕ → ℕ) (P : ℕ → ℤ → ℕ → Prop)
    (hq : ∀ r, 0 < q r)
    (hcop : ∀ r, Nat.Coprime (modulusProd q r) (q r))
    (hper : ∀ r b x, P r b (x % q r) ↔ P r b x)
    (hgood : ∀ r b, 7 * ((Finset.range (q r)).filter (P r b)).card ≤ 6 * q r)
    (htri : ∀ r b x, TriangularInt (naturalSquareSum x + b) → P r b x)
    (r : ℕ) :
    ∃ M : ℕ, 0 < M ∧
      ∀ (u : ℕ) (b : ℤ),
        7 ^ r * (cubicCandidates u M b).card ≤ 6 ^ r * M := by
  classical
  refine ⟨modulusProd q r, modulusProd_pos q hq r, ?_⟩
  intro u b
  let M := modulusProd q r
  have hbound := crt_sieve_product_count67 q P hq hcop hper hgood r b
  have hpass :
      (cubicCandidates u M b).card ≤
       ((Finset.Ico u (u + M)).filter (passesProd P b r)).card := by
    apply Finset.card_le_card
    intro x hx
    obtain ⟨hxi, htriX⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr
      ⟨hxi, passesProd_of_triangular P htri r b x htriX⟩
  have hperiod :
      ((Finset.Ico u (u + M)).filter (passesProd P b r)).card ≤
        ((Finset.range M).filter (passesProd P b r)).card := by
    have h := crt_periodic_intersection_bound M 1 u
      (by simp : Nat.Coprime M 1) (modulusProd_pos q hq r) (by decide)
      (passesProd P b r) (fun _ => True)
      (by
        intro x hx
        exact (passesProd_periodic q P hper r b x).mpr hx)
      (by intro x hx; exact hx)
    simpa only [Nat.mul_one, and_true, Finset.filter_true,
      Finset.card_range, mul_one] using h
  calc
    7 ^ r * (cubicCandidates u M b).card ≤
        7 ^ r * ((Finset.Ico u (u + M)).filter (passesProd P b r)).card :=
      Nat.mul_le_mul_left _ hpass
    _ ≤ 7 ^ r * ((Finset.range M).filter (passesProd P b r)).card :=
      Nat.mul_le_mul_left _ hperiod
    _ ≤ 6 ^ r * M := hbound


#print axioms crt_sieve_product_count67
#print axioms uniformCubicSieve67_of_modular_family

end SparseDeletion
