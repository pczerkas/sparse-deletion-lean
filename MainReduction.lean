module -- shake: keep-all

public import IndexTransfer
public import SieveInduction

@[expose] public section

open Filter

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-!
The precise remaining analytic number theory task:
construct a sequence of pairwise CRT-compatible moduli q(r) and their
quadratic-residue predicates P(r,b,x), such that every residue shift b
loses at least a quarter of all x-residues at each step.

Given these five properties, the general sparse-deletion theorem follows
with no other assumptions and with no sorryAx.
-/

/-- Complete zero-density result *conditional on an infinite, uniform,
independent sequence of modular obstruction certificates*. -/
theorem zeroDensityByIndex_of_modular_family
    (q : ℕ → ℕ) (P : ℕ → ℤ → ℕ → Prop)
    (hq : ∀ r, 0 < q r)
    (hcop : ∀ r, Nat.Coprime (modulusProd q r) (q r))
    (hper : ∀ r b x, P r b (x % q r) ↔ P r b x)
    (hgood : ∀ r b,
      4 * ((Finset.range (q r)).filter (P r b)).card ≤ 3 * q r)
    (htri : ∀ r b x,
      TriangularInt (naturalSquareSum x + b) → P r b x)
    (E : Set ℕ) (hE : HasDensityZero E) :
    HasDensityZero { n : ℕ | Triangular (keptIndexPrefix E n) } := by
  apply zeroDensityByIndex_of_all_sieves E hE
  intro r
  exact uniformCubicSieve_of_modular_family
    q P hq hcop hper hgood htri r

#print axioms zeroDensityByIndex_of_modular_family

end SparseDeletion
