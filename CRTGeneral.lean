module -- shake: keep-all

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Nth

@[expose] public section

namespace SparseDeletion

theorem crt_mod_inj_general (m n u : ℕ)
    (hc : Nat.Coprime m n) (hm : 0 < m) (hn : 0 < n) :
    Set.InjOn (fun x : ℕ => (x % m, x % n))
      ((Finset.Ico u (u + m * n)) : Set ℕ) := by
  intro x hx y hy hxy
  have hx' := Finset.mem_Ico.mp hx
  have hy' := Finset.mem_Ico.mp hy
  have h₁ : x % m = y % m := congrArg Prod.fst hxy
  have h₂ : x % n = y % n := congrArg Prod.snd hxy
  have hp : Nat.ModEq (m * n) x y :=
    (Nat.modEq_and_modEq_iff_modEq_mul hc).mp ⟨h₁, h₂⟩
  by_cases hle : x ≤ y
  · obtain ⟨t, ht⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hp
    by_cases hz : t = 0
    · simp [hz] at ht
      omega
    · have ht1 : 1 ≤ t := by omega
      have hmul : m * n ≤ (m * n) * t := by
        calc
          m * n = (m * n) * 1 := by simp
          _ ≤ (m * n) * t := Nat.mul_le_mul_left _ ht1
      omega
  · have hle' : y ≤ x := by omega
    obtain ⟨t, ht⟩ := (Nat.modEq_iff_exists_eq_add hle').mp hp.symm
    by_cases hz : t = 0
    · simp [hz] at ht
      omega
    · have ht1 : 1 ≤ t := by omega
      have hmul : m * n ≤ (m * n) * t := by
        calc
          m * n = (m * n) * 1 := by simp
          _ ≤ (m * n) * t := Nat.mul_le_mul_left _ ht1
      omega


/-- Abstract two-modulus CRT sieve bound.
For periodic tests P mod m and Q mod n, the number of simultaneous
passes in any block of length m*n is at most the product of their
residue counts. The theorem knows nothing about elliptic curves. -/
theorem crt_periodic_intersection_bound
    (m n u : ℕ) (hcop : Nat.Coprime m n)
    (hm : 0 < m) (hn : 0 < n)
    (P Q : ℕ → Prop) [DecidablePred P] [DecidablePred Q]
    (hP : ∀ x, P x → P (x % m))
    (hQ : ∀ x, Q x → Q (x % n)) :
    ((Finset.Ico u (u + m*n)).filter (fun x => P x ∧ Q x)).card ≤
      ((Finset.range m).filter P).card *
        ((Finset.range n).filter Q).card := by
  classical
  let S : Finset ℕ := (Finset.Ico u (u + m*n)).filter (fun x => P x ∧ Q x)
  let A : Finset ℕ := (Finset.range m).filter P
  let B : Finset ℕ := (Finset.range n).filter Q
  have hmap : Set.MapsTo (fun x : ℕ => (x % m, x % n))
      (S : Set ℕ) (A.product B : Set (ℕ × ℕ)) := by
    intro x hx
    obtain ⟨_, hp, hq⟩ := Finset.mem_filter.mp hx
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.mod_lt _ hm), hP x hp⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (Nat.mod_lt _ hn), hQ x hq⟩
  have hinj : Set.InjOn (fun x : ℕ => (x % m, x % n)) (S : Set ℕ) := by
    intro x hx y hy heq
    apply crt_mod_inj_general m n u hcop hm hn
    · exact (Finset.mem_filter.mp hx).1
    · exact (Finset.mem_filter.mp hy).1
    · exact heq
  have hcount := Finset.card_le_card_of_injOn
    (s := S) (t := A.product B) (fun x : ℕ => (x % m, x % n)) hmap hinj
  simpa [S, A, B, Finset.card_product] using hcount

#print axioms crt_periodic_intersection_bound


end SparseDeletion

#print axioms SparseDeletion.crt_mod_inj_general
