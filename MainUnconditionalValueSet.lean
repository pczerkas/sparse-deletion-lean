import CubicConicInjection

namespace SparseDeletion

attribute [local instance] Classical.propDecidable

/-- A proof of the exact missing cubic-value bound for our infinite prime
    family. It uses only finite fields and elementary conic geometry. -/
theorem cubicValueLowerBound_proved : CubicValueLowerBound := by
  intro r
  letI : Fact (largePrime r).Prime := ⟨largePrime_prime r⟩
  have h3 : (3 : ZMod (largePrime r)) ≠ 0 := by
    intro hz
    have h6 := prime_h6 (largePrime r) (largePrime_ge r)
    apply h6
    calc
      (6 : ZMod (largePrime r)) = 2 * 3 := by norm_num
      _ = 0 := by rw [hz]; ring
  have hbound := cubic_value_set_lower_bound (F := ZMod (largePrime r)) h3
  simpa only [ZMod.card] using hbound

/-- Unconditional and sorry-free: deleting any natural-density-zero subset
    of the positive integers leaves a sequence whose square-sum triangular
    hit indices have natural density zero. -/
theorem main_sparse_deletion_unconditional
    (E : Set ℕ) (hE : HasDensityZero E) :
    HasDensityZero { n : ℕ | Triangular (keptIndexPrefix E n) } := by
  exact main_of_cubic_value_bound cubicValueLowerBound_proved E hE

#print axioms cubicValueLowerBound_proved
#print axioms main_sparse_deletion_unconditional

end SparseDeletion
