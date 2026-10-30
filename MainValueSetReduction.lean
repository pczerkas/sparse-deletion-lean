module -- shake: keep-all

public import MainReduction
public import SieveInduction67
public import AffineValueBridge

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-- Two tests with survival 6/7 each beat one test with survival 3/4:
    (6/7)^2 = 36/49 ≤ 3/4. -/
theorem six_sevenths_twice_le_three_quarters (r : ℕ) :
    4 ^ r * 6 ^ (2 * r) ≤ 3 ^ r * 7 ^ (2 * r) := by
  have h : (4 * 6 ^ 2 : ℕ) ^ r ≤ (3 * 7 ^ 2 : ℕ) ^ r :=
    Nat.pow_le_pow_left (by norm_num) r
  have hleft : 4 ^ r * 6 ^ (2 * r) = (4 * 6 ^ 2 : ℕ) ^ r := by
    rw [mul_pow, pow_mul]
  have hright : 3 ^ r * 7 ^ (2 * r) = (3 * 7 ^ 2 : ℕ) ^ r := by
    rw [mul_pow, pow_mul]
  simpa only [hleft, hright] using h

/-- An infinite supply of uniformly 6/7-good CRT moduli suffices for
    the already proved index-density theorem. -/
theorem zeroDensityByIndex_of_modular_family67
    (q : ℕ → ℕ) (P : ℕ → ℤ → ℕ → Prop)
    (hq : ∀ r, 0 < q r)
    (hcop : ∀ r, Nat.Coprime (modulusProd q r) (q r))
    (hper : ∀ r b x, P r b (x % q r) ↔ P r b x)
    (hgood : ∀ r b,
      7 * ((Finset.range (q r)).filter (P r b)).card ≤ 6 * q r)
    (htri : ∀ r b x,
      TriangularInt (naturalSquareSum x + b) → P r b x)
    (E : Set ℕ) (hE : HasDensityZero E) :
    HasDensityZero { n : ℕ | Triangular (keptIndexPrefix E n) } := by
  apply zeroDensityByIndex_of_all_sieves E hE
  intro r
  obtain ⟨M, hM, hcount⟩ :=
    uniformCubicSieve67_of_modular_family
      q P hq hcop hper hgood htri (2 * r)
  refine ⟨M, hM, ?_⟩
  intro u b
  have hc := hcount u b
  have hs : 7 ^ (2 * r) *
        (cubicCandidates u M b).card ≤ 6 ^ (2 * r) * M := hc
  have hpow := six_sevenths_twice_le_three_quarters r
  have hstrong :
      7 ^ (2 * r) * (4 ^ r * (cubicCandidates u M b).card) ≤
        7 ^ (2 * r) * (3 ^ r * M) := by
    calc
      _ = 4 ^ r * (7 ^ (2 * r) * (cubicCandidates u M b).card) := by ring
      _ ≤ 4 ^ r * (6 ^ (2 * r) * M) := Nat.mul_le_mul_left _ hs
      _ = (4 ^ r * 6 ^ (2 * r)) * M := by ring
      _ ≤ (3 ^ r * 7 ^ (2 * r)) * M :=
        Nat.mul_le_mul_right M hpow
      _ = 7 ^ (2 * r) * (3 ^ r * M) := by ring
  exact Nat.le_of_mul_le_mul_left hstrong (pow_pos (by decide) _)

#print axioms six_sevenths_twice_le_three_quarters
#print axioms zeroDensityByIndex_of_modular_family67

end SparseDeletion
