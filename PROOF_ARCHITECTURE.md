# Proof architecture and dependency audit

This document describes the **active repository** after dependency clean-up.
All named `.lean` files below are present in the current tree.
Lean and Mathlib are both pinned to `v4.35.0`.

## Result and proof skeleton

`main_sparse_deletion_unconditional` asserts that if `E ⊆ ℕ`
has natural density zero, then triangular prefix sums of the squares
of increasingly enumerated positive integers outside `E` occur at
indices of natural density zero.

The logical argument consists of:

1. **Finite fields:** the cubic map `x ↦ x³−x` takes at least
   `(2q−1)/3` values for any finite field of characteristic ≠3.
   A conic-collision injection proves this without the Weil bound.
2. **Elementary finite-field sieve:** the value-set lower bound, the
   elementary count of squares, and an affine change of variables
   give a uniform `6/7` upper bound for modular passing residues.
3. **CRT:** independent coprime moduli give an upper density factor
   `(6/7)^r` for `r` tests, uniformly over shifted intervals.
4. **Sparse perturbation:** subtracting the squares at deleted
   indices changes the shift only at a density-zero set. The
   abstract uniform-block lemma proves zero density of triangular
   hits when indexed by the original *value* `n`.
5. **Index transfer:** the `n`-th retained integer is `n+o(n)`
   (a coarse bound `< 2n+2` suffices), transferring zero density
   from original values to retained-sequence indices.

The main theorem is **not** a finiteness result and does not apply
directly to prime-square prefix sums.

## Physical imports: three verified targets

### Generic mathematical layer — independently importable

```text
CountingDensity.lean
  └── SparsePerturbation.lean
        └── VerifiedPerturbation.lean
```

The central theorem is
`sparsePerturbation_zeroDensity_of_uniform_small_blocks`.
For `f d : ℕ → ℤ`, `A ⊆ ℤ` and density-zero `E ⊆ ℕ`, assume

```lean
∀ n : ℕ, n + 1 ∉ E → d (n + 1) = d n
```

and, for each real `ε > 0`, the existence of a **common**
`M > 0` and `C : ℕ` with `(C : ℝ)/M < ε` such that

```text
#{ n ∈ [u,u+M) : f(n)+b ∈ A } ≤ C
```

for **every** starting index `u` and integer shift `b`.
It follows that `{n : ℕ | f(n)+d(n) ∈ A}` has density zero.

The variation of `d` can be arbitrarily large. Only its **locations
of change** are constrained. The geometric-contraction version
`sparsePerturbation_zeroDensity_of_uniform_ratio_sieves` is a
corollary of this more general theorem.

### Arithmetic and density layer — main theorem

```text
CountingDensity ─┬─ SparseDeletionBase ─┬─ SparseDeletion
                 │                      └─ RemovedSquares
                 │                           └─ KeptSquaresBridge
                 └─ SparsePerturbation          └─ IndexBridge
                       │                            └─ IndexGrowth
                       └─ DensityToZero <───────────┘
                            └─ IndexTransfer
                                  └─ MainReduction ← SieveInduction ← CRTGeneral
                                        └─ MainExactValueReduction
                                               └─ MainUnconditionalValueSet
                                                     └─ VerifiedCompleteProof
```

The diagram is a **conceptual summary**, not a complete directed
import graph: `MainExactValueReduction` also receives the
finite-field inputs listed below; `MainReduction` uses both
`IndexTransfer` and `SieveInduction`; `SieveInduction` also
imports `SparseDeletion`.

The sparse-deletion specialization uses

```text
f(n) = ∑_{k=0}^n k²
d(n) = −∑_{0≤k≤n, k∈E} k²
A    = {z ∈ ℤ : z is triangular}.
```

The elementary identity `removedSquareSum_succ` proves the sparse
jump condition for `d`, while
`keptSquaresUpTo_cast_eq_shiftedRemaining` connects the integer
formula to the original natural-number prefix sum.

The retained-index transfer is in `IndexTransfer.lean`;
`IndexGrowth.lean` proves the retained integers are sufficiently
dense. The geometric `6/7` ratio comes from
`MainExactValueReduction.lean`.

### The finite-field input

```text
CubicCollisionBridge → ConicPointBound → CubicRepresentative
                                       → CubicConicInjection
```

This is the elementary collision-conic lower bound for `x³−x`.

The modular proof also imports the following active modules:

```text
CubicShape → CubicSumBridge → PrimeCubicPoly → PrimeSquarePass
CRTGeneral → SieveInduction → PrimeFamily
AffineValueBridge, ImageBoundBridge, ResidueCountBridge,
SquareValueCount, MainExactValueReduction
```

`AffineValueBridge` handles the affine cubic value-set equivalence.
`SquareValueCount` proves the exact number of squares in an
odd-characteristic finite field using a **basic quadratic-character
sum identity** already in Mathlib. This is not an assumption of, or
an appeal to, Weil's or Hasse's estimates.

`PrimeSquarePass` characterizes the periodic modular predicate;
`PrimeFamily` constructs the coprime sequence of primes ≥37.
`SieveInduction` then iterates the CRT bound.

### Independent exact value-set result

```text
CubicConicInjection → CubicConicExact → ConicExactCount
                                         └─ VerifiedExactValueSet
```

This stronger result counts all points of
`x²+xy+y²=1` and establishes the exact classical value-set
formula for `x³−x`. It does **not** lie in the main density theorem's
import graph. The weaker lower bound is enough for the sieve and makes
the main proof smaller.

### Additional corollary

`CompositeCorollary.lean` imports `MainUnconditionalValueSet.lean`
and a Mathlib proof that primes have natural density zero. It is
verified separately as one of the default build targets.

## Removed alternatives

The working tree no longer contains the historical fixed-prime
sieve experiments or the conditional curve-character/Hasse route.
Those experiments can be inspected in older Git commits and are
**not needed to verify any current theorem**.

This distinction matters: a conditional reduction that assumes a
strong character-sum estimate is not a proof of that estimate.
The present unconditional theorem uses only elementary conic
geometry, basic finite-field cardinalities, and CRT.

The abstract module `SparsePerturbation.lean` imports only
`CountingDensity.lean`, not any arithmetic module.

## Verification and maintenance

```sh
lake exe cache get
lake build
lake env lean VerifiedPerturbation.lean
lake env lean VerifiedExactValueSet.lean
lake env lean VerifiedCompleteProof.lean
```

`lake build` builds all four maintained verification entry points.
All reported axioms are among `propext`, `Classical.choice`,
`Quot.sound`; there is no `sorryAx` in their proof terms.

When a module is renamed or removed, update **both** this document,
`README.md`, `lakefile.toml`, and the GitHub Actions workflow.
Do not claim publication novelty solely because a formula has been
formalized.
