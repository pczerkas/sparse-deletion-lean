module -- shake: keep-all

public import SparsePerturbation

@[expose] public section

/-!
Independent formal certificate for the abstract sparse-perturbation lemma.
The imported theorem mentions no prime, polynomial, square or triangular number.
-/

#print axioms SparseDeletion.perturb_count_bound
#print axioms SparseDeletion.sparsePerturbation_zeroDensity_of_uniform_small_blocks
#print axioms SparseDeletion.sparsePerturbation_zeroDensity_of_uniform_ratio_sieves
