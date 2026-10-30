module -- shake: keep-all

public import SieveInduction
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.Data.Nat.GCD.BigOperators

@[expose] public section

namespace SparseDeletion

/-! The CRT-compatible moduli needed in the general sieve can be chosen
concretely as distinct primes ≥ 37. No character bound is used here. -/

def largePrimePred (p : ℕ) : Prop := p.Prime ∧ 37 ≤ p

theorem largePrimePred_infinite : (Set.ofPred largePrimePred).Infinite := by
  apply Set.infinite_iff_exists_gt.mpr
  intro n
  obtain ⟨p, hpn, hprime⟩ := Nat.exists_infinite_primes (max n 37 + 1)
  refine ⟨p, ?_, ?_⟩
  · exact ⟨hprime, by omega⟩
  · omega

noncomputable def largePrime (r : ℕ) : ℕ :=
  Nat.nth largePrimePred r

theorem largePrime_prime (r : ℕ) : (largePrime r).Prime := by
  exact (Nat.nth_mem_of_infinite largePrimePred_infinite r).1

theorem largePrime_ge (r : ℕ) : 37 ≤ largePrime r := by
  exact (Nat.nth_mem_of_infinite largePrimePred_infinite r).2

theorem largePrime_strictMono : StrictMono largePrime :=
  Nat.nth_strictMono largePrimePred_infinite

theorem modulusProd_eq_range_prod (q : ℕ → ℕ) (r : ℕ) :
    modulusProd q r = ∏ i ∈ Finset.range r, q i := by
  induction r with
  | zero => simp [modulusProd]
  | succ r ih =>
    rw [modulusProd, ih, Finset.prod_range_succ]

theorem largePrime_coprime_previous (r : ℕ) :
    Nat.Coprime (modulusProd largePrime r) (largePrime r) := by
  rw [modulusProd_eq_range_prod, Nat.coprime_prod_left_iff]
  intro i hi
  exact (Nat.coprime_primes (largePrime_prime i) (largePrime_prime r)).mpr
    ((largePrime_strictMono (Finset.mem_range.mp hi)).ne)

theorem largePrime_positive (r : ℕ) : 0 < largePrime r := by
  have h := largePrime_ge r
  omega

#print axioms largePrimePred_infinite
#print axioms largePrime_coprime_previous
#print axioms largePrime_positive

end SparseDeletion
