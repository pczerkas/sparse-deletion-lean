module -- shake: keep-all

public import IndexTransfer
public import SieveInduction

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-!
The abstract end-to-end CRT reduction. Any infinite family of pairwise
CRT-compatible modular obstructions with a fixed contraction
`0 < numer < denom` implies zero density of triangular prefix hits
after deleting an arbitrary density-zero subset of positive integers.
The arithmetic work consists in constructing such a modular family.
-/

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

#print axioms zeroDensityByIndex_of_modular_family_param

end SparseDeletion
