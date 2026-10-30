module -- shake: keep-all

public import SieveInduction

@[expose] public section

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-- Compatibility specialization: independent periodic tests retain at most 6/7. -/
theorem crt_sieve_product_count67 (q : ℕ → ℕ) (P : ℕ → ℤ → ℕ → Prop)
    (hq : ∀ r, 0 < q r)
    (hcop : ∀ r, Nat.Coprime (modulusProd q r) (q r))
    (hper : ∀ r b x, P r b (x % q r) ↔ P r b x)
    (hgood : ∀ r b, 7 * ((Finset.range (q r)).filter (P r b)).card ≤ 6 * q r)
    (r : ℕ) (b : ℤ) :
    7 ^ r * ((Finset.range (modulusProd q r)).filter
      (passesProd P b r)).card ≤ 6 ^ r * modulusProd q r :=
  crt_sieve_product_count_param 6 7 q P hq hcop hper hgood r b

/-- Compatibility specialization for the original 6/7 finite sieve. -/
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
        7 ^ r * (cubicCandidates u M b).card ≤ 6 ^ r * M :=
  uniformCubicSieve_of_modular_family_param 6 7 q P hq hcop hper hgood htri r

#print axioms crt_sieve_product_count67
#print axioms uniformCubicSieve67_of_modular_family

end SparseDeletion
