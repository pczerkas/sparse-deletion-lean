module -- shake: keep-all

public import MainReduction
public import SieveInduction67
public import AffineValueBridge

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-- The generic end-to-end CRT criterion. Any fixed contraction
    numer/denom < 1 suffices, without changing the sieve exponent. -/
theorem zeroDensityByIndex_of_modular_family_param
    (numer denom : ℕ) (hnum : 0 < numer) (hfrac : numer < denom)
    (q : ℕ → ℕ) (P : ℕ → ℤ → ℕ → Prop)
    (hq : ∀ r, 0 < q r)
    (hcop : ∀ r, Nat.Coprime (modulusProd q r) (q r))
    (hper : ∀ r b x, P r b (x % q r) ↔ P r b x)
    (hgood : ∀ r b,
      denom * ((Finset.range (q r)).filter (P r b)).card ≤ numer * q r)
    (htri : ∀ r b x,
      TriangularInt (naturalSquareSum x + b) → P r b x)
    (E : Set ℕ) (hE : HasDensityZero E) :
    HasDensityZero { n : ℕ | Triangular (keptIndexPrefix E n) } := by
  apply zeroDensityByIndex_of_uniform_ratio_sieves
    numer denom hnum hfrac E hE
  intro r
  exact uniformCubicSieve_of_modular_family_param
    numer denom q P hq hcop hper hgood htri r

/-- Compatibility interface for the original 6/7 modular family.
    It now applies the direct 6/7 estimate rather than pairing two
    tests to manufacture a 3/4 estimate. -/
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
    HasDensityZero { n : ℕ | Triangular (keptIndexPrefix E n) } :=
  zeroDensityByIndex_of_modular_family_param
    6 7 (by decide) (by decide) q P hq hcop hper hgood htri E hE

#print axioms zeroDensityByIndex_of_modular_family_param
#print axioms zeroDensityByIndex_of_modular_family67

end SparseDeletion
