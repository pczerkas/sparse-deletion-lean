module -- shake: keep-all

public import QuantitativeSieve

@[expose] public section

/-!
Independent verification entry point for finite-N quantitative hit bounds.
The original main theorem is not modified by this optional extension.
-/

#print axioms SparseDeletion.quantitative_value_hit_bound
#print axioms SparseDeletion.quantitative_index_hit_bound
#print axioms SparseDeletion.quantitative_value_hit_bound_simplified

#print axioms SparseDeletion.quantitative_prime_modular_bound
#print axioms SparseDeletion.quantitative_cubic_sieve_family
#print axioms SparseDeletion.quantitative_value_bound_unconditional
#print axioms SparseDeletion.quantitative_index_bound_unconditional
