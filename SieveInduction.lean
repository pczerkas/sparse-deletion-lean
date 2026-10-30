module -- shake: keep-all

public import CRTGeneral
public import SparseDeletion

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-!
An abstract infinite CRT sieve. All finite sieve iteration is formalized here.
The *only* arithmetic input still needed is an unbounded sequence of
coprime moduli carrying uniformly good quadratic-residue certificates.
-/

def modulusProd (q : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 => modulusProd q r * q r

def passesProd (P : ℕ → ℤ → ℕ → Prop) (b : ℤ) : ℕ → ℕ → Prop
  | 0, _ => True
  | r + 1, x => passesProd P b r x ∧ P r b x

theorem modulusProd_pos (q : ℕ → ℕ) (hq : ∀ r, 0 < q r) (r : ℕ) :
    0 < modulusProd q r := by
  induction r with
  | zero => simp [modulusProd]
  | succ r ih =>
    simpa only [modulusProd] using Nat.mul_pos ih (hq r)

theorem passesProd_periodic (q : ℕ → ℕ) (P : ℕ → ℤ → ℕ → Prop)
    (hper : ∀ r b x, P r b (x % q r) ↔ P r b x)
    (r : ℕ) (b : ℤ) (x : ℕ) :
    passesProd P b r (x % modulusProd q r) ↔ passesProd P b r x := by
  induction r generalizing x with
  | zero => simp [passesProd]
  | succ r ih =>
    let M := modulusProd q (r + 1)
    have hprev : (x % M) % modulusProd q r = x % modulusProd q r := by
      apply Nat.mod_mod_of_dvd
      dsimp [M, modulusProd]
      exact dvd_mul_right _ _
    have hatom : (x % M) % q r = x % q r := by
      apply Nat.mod_mod_of_dvd
      dsimp [M, modulusProd]
      exact dvd_mul_left _ _
    have h1 : passesProd P b r (x % M) ↔ passesProd P b r x := by
      have ha := ih (x % M)
      have hb := ih x
      rw [hprev] at ha
      exact ha.symm.trans hb
    have h2 : P r b (x % M) ↔ P r b x := by
      have ha := hper r b (x % M)
      have hb := hper r b x
      rw [hatom] at ha
      exact ha.symm.trans hb
    change (passesProd P b r (x % M) ∧ P r b (x % M)) ↔
      (passesProd P b r x ∧ P r b x)
    exact and_congr h1 h2

theorem passesProd_of_triangular
    (P : ℕ → ℤ → ℕ → Prop)
    (htri : ∀ r b x, TriangularInt (naturalSquareSum x + b) → P r b x)
    (r : ℕ) (b : ℤ) (x : ℕ)
    (hx : TriangularInt (naturalSquareSum x + b)) :
    passesProd P b r x := by
  induction r with
  | zero => trivial
  | succ r ih => exact ⟨ih, htri r b x hx⟩

/-! ## A single parametric CRT counting theorem

The coefficients numer and denom are arbitrary natural numbers here. Strict
contraction (numer < denom) is only needed to deduce density zero.
-/

theorem crt_sieve_product_count_param (numer denom : ℕ) (q : ℕ → ℕ) (P : ℕ → ℤ → ℕ → Prop)
    (hq : ∀ r, 0 < q r)
    (hcop : ∀ r, Nat.Coprime (modulusProd q r) (q r))
    (hper : ∀ r b x, P r b (x % q r) ↔ P r b x)
    (hgood : ∀ r b, denom * ((Finset.range (q r)).filter (P r b)).card ≤ numer * q r)
    (r : ℕ) (b : ℤ) :
    denom ^ r * ((Finset.range (modulusProd q r)).filter
      (passesProd P b r)).card ≤ numer ^ r * modulusProd q r := by
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
    have ih' : denom ^ r * A.card ≤ numer ^ r * m := ih
    have hn : denom * B.card ≤ numer * n := hgood r b
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
    change denom ^ (r + 1) *
      ((Finset.range (m * n)).filter
        (fun x => passesProd P b r x ∧ P r b x)).card ≤
        numer ^ (r + 1) * (m * n)
    calc
      _ ≤ denom ^ (r + 1) * (A.card * B.card) :=
        Nat.mul_le_mul_left _ hc
      _ = (denom ^ r * A.card) * (denom * B.card) := by
        rw [pow_succ]; ring
      _ ≤ (numer ^ r * m) * (numer * n) := Nat.mul_le_mul ih' hn
      _ = numer ^ (r + 1) * (m * n) := by
        rw [pow_succ]; ring

/-- Parametric finite sieve with uniform ratio numer/denom. -/
theorem uniformCubicSieve_of_modular_family_param
    (numer denom : ℕ)
    (q : ℕ → ℕ) (P : ℕ → ℤ → ℕ → Prop)
    (hq : ∀ r, 0 < q r)
    (hcop : ∀ r, Nat.Coprime (modulusProd q r) (q r))
    (hper : ∀ r b x, P r b (x % q r) ↔ P r b x)
    (hgood : ∀ r b, denom * ((Finset.range (q r)).filter (P r b)).card ≤ numer * q r)
    (htri : ∀ r b x, TriangularInt (naturalSquareSum x + b) → P r b x)
    (r : ℕ) :
    ∃ M : ℕ, 0 < M ∧
      ∀ (u : ℕ) (b : ℤ),
        denom ^ r * (cubicCandidates u M b).card ≤ numer ^ r * M := by
  classical
  refine ⟨modulusProd q r, modulusProd_pos q hq r, ?_⟩
  intro u b
  let M := modulusProd q r
  have hbound := crt_sieve_product_count_param numer denom q P hq hcop hper hgood r b
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
    denom ^ r * (cubicCandidates u M b).card ≤
        denom ^ r * ((Finset.Ico u (u + M)).filter (passesProd P b r)).card :=
      Nat.mul_le_mul_left _ hpass
    _ ≤ denom ^ r * ((Finset.range M).filter (passesProd P b r)).card :=
      Nat.mul_le_mul_left _ hperiod
    _ ≤ numer ^ r * M := hbound

#print axioms SparseDeletion.crt_sieve_product_count_param
#print axioms SparseDeletion.uniformCubicSieve_of_modular_family_param

end SparseDeletion
