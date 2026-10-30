# Verified proof architecture (minimal logical route)

## Two distinct mathematical layers

The density theorem is a composition of a **generic sparse perturbation lemma**
and an **arithmetic uniform sieve**. The formal names below are checked
against Lean 4.35.0 / Mathlib v4.35.0.

### Layer I: generic, no number theory

```text
CountingDensity.lean
   └── SparsePerturbation.lean
         ├── perturb_constant_on_clean
         ├── perturb_count_bound
         ├── eventually_perturb_ratio_le
         ├── sparsePerturbation_zeroDensity_of_uniform_small_blocks
         └── sparsePerturbation_zeroDensity_of_uniform_ratio_sieves
               └── VerifiedPerturbation.lean (independent certificate)
```

Given `f d : ℕ → ℤ`, `A : Set ℤ`, and density-zero `E : Set ℕ`,
the only constraint on `d` is

```lean
∀ n : ℕ, n + 1 ∉ E → d (n + 1) = d n
```

The **minimal** uniform-hit hypothesis is: for every real `ε > 0`,
there are `M > 0` and `C` with `C / M < ε`, and **every** block of
length `M` has at most `C` indices `n` with `f n + b ∈ A`,
uniformly in its start and in the integer shift `b`. Then the indices
for which `f n + d n ∈ A` have natural density zero.

The geometric-ratio wrapper (`numer / denom < 1`) is a corollary used
by the CRT sieve. It is deliberately not part of the minimal hypothesis.

The generic proof applies to **any** `f` and `A`. Neither the
magnitudes of `d` nor the sizes of its jumps are bounded.

### Layer II: arithmetic specialization and enumeration indices

```text
naturalSquareSum, removedSquareSum, TriangularInt
   └── DensityToZero.lean
         └── zeroDensityByValue_of_uniform_ratio_sieves
               (now a specialization of the generic lemma)
                     └── IndexTransfer.lean
                           └── zeroDensityByIndex_of_uniform_ratio_sieves
                                 └── MainReduction.lean
                                       └── zeroDensityByIndex_of_modular_family_param
```

The substitution in `DensityToZero` is:

```text
f(n) = 0² + 1² + ... + n²
d(n) = -∑_{k≤n, k∈E} k²
A    = { triangular integers }
```

The `hstep` hypothesis follows immediately from
`removedSquareSum_succ`. The original cubic CRT candidate bound is
definitionally equal to the generic shifted-hit candidate bound.
The `keptSquaresUpTo_cast_eq_shiftedRemaining` lemma identifies the
perturbation's hit set with the original natural-number triangular hit set.

### Layer III: finite-field input to the sieve

```text
CubicCollisionBridge
   └── ConicPointBound
         └── CubicRepresentative
               └── CubicConicInjection
                     └── cubic_value_set_lower_bound
                           └── MainUnconditionalValueSet
                                 └── cubicValueLowerBound_proved
                                       └── main_sparse_deletion_unconditional
```

`MainExactValueReduction` connects this value-set bound to the modular
family and the generic CRT step. `SieveInduction` supplies the uniform
family of long-block obstructions.

The **exact** conic count (`CubicConicExact`,
`ConicExactCount`, `VerifiedExactValueSet`) is a separate,
stronger classical theorem. It is not needed for the main sparse-deletion
density proof; the elementary lower bound suffices and keeps the
arithmetic argument shorter.

### Historical modules and import boundaries

The repository retains earlier explicit-prime sieves, finite block
checks, and a conditional Hasse/Weil approach for reproducibility.
They are *not mathematical hypotheses* of the unconditional main
theorem. Some historical modules remain in the transitive **file import**
graph of older bridge modules. A physical import graph is not the same
as a proof-term dependency cone.

`CountingDensity` and `SparsePerturbation` now import **none** of
those historical arithmetic modules. `DensityToZero` also no longer
imports the old `DensityBridge` directly. Existing legacy results are
left available and still compile.

## Verification

```sh
lake build VerifiedPerturbation
lake build VerifiedCompleteProof VerifiedExactValueSet CompositeCorollary
lake env lean VerifiedPerturbation.lean
lake env lean VerifiedCompleteProof.lean
```

For the abstract lemma, the exact cubic count, and the main theorem
`#print axioms` reports only `propext`, `Classical.choice`, and
`Quot.sound` (not `sorryAx`). This is a mathematical
formalization, **not** a claim that either theorem was first discovered here.

The main theorem is about **density zero**, not finitely many hits.
It also does **not** apply directly to prime-square prefixes because
the complementary set of nonprimes has density one.
