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

## Physical imports and verification targets

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

### Optional quantitative extension

`QuantitativeBound.lean` imports `IndexTransfer.lean` and proves
finite-N upper bounds by specializing the *existing* `perturb_count_bound`.
Its statements hold for any finite N and any uniform shifted modular
block sieve. The enumeration-index estimate additionally assumes a
bound on the N-th retained integer.

```text
IndexTransfer ──→ QuantitativeBound ──→ QuantitativeSieve
                                               └──→ QuantitativeEffective
                                                           └──→ QuantitativeSharper
                                                                      └──→ VerifiedQuantitativeBound
```

`QuantitativeSieve.lean` also imports `MainUnconditionalValueSet.lean` to
reuse the proven cubic value-set bound. It establishes for every depth `r`
a concrete CRT bound with contraction `(6/7)^r`, with no assumption that
the deleted set has zero density. The multiplier modulus `M_r` depends
on `r`. These optional files do **not** feed back into the main theorem.
The optional module `QuantitativeEffective.lean` imports Mathlib's
Bertrand postulate and proves the loose elementary modulus bound
`M_r ≤ 37^r * 2^(r*r)`, yielding explicit finite-N bounds in terms
of the deletion count, both for value indices and for retained-sequence
indices under the stated survivor-growth hypothesis. These optional results do not use five-square
representations or assume a decay rate for the deleted-set density.
`QuantitativeSharper.lean` additionally improves the modulus bound to
`37^r * 2^(r*(r-1)/2)`, using the exact triangular exponent sum.
The additional corollaries remain outside the main proof graph.
The additional optional `PrimePolynomialBound.lean` imports `QuantitativeSharper`
and Mathlib's elementary Chebyshev lower bound for prime counting;
its quadratic bound `largePrime r ≤ 64*(r+50)^2` was verified by
GitHub Actions run `41236892361`, commit `67fa5d4`. The companion
`QuantitativePolynomial.lean` multiplies the bounds to obtain the
explicit CRT modulus bound `(64*(r+50)^2)^r` and the two finite-N
hit-count estimates. The companion module passed GitHub Actions run
`41237410122` (commit `a0862e0`), with no `sorryAx`. It is not a dependency of the main theorem.
The improved certificate passed GitHub Actions run `41236256862`
(commit `4b65c88`) with only the standard Lean axioms.

### Additional corollary

`CompositeCorollary.lean` imports `MainUnconditionalValueSet.lean`
and a Mathlib proof that primes have natural density zero. It is
verified separately as one of the default build targets.

### Optional explicit rate (finite-budget form)

`QuantitativeRate.lean` imports only `QuantitativePolynomial.lean`.
It proves a fully explicit threshold:
`(448*(r+50)^2)^r*(e(N)+1) ≤ N` implies
`7^r*H_E(N) ≤ 2*6^r*N`, and its retained-index counterpart.
The final choice of `r` via real logarithms is not yet formalized.
The finite budget module passed GitHub Actions run `41238649297`,
commit `ab671d6`, with only the standard axioms.

### Optional real ratio bridge

`QuantitativeReal.lean` imports `QuantitativeRate.lean` and
uses exact casts and positive denominators to turn the finite
integer threshold into an upper bound on real frequencies. This
is separate from the final logarithmic optimization, which has
not yet been formalized. The real-ratio bridge passed GitHub
Actions run `41238649297` (commit `ab671d6`, no `sorryAx`).

### Optional logarithmic depth (CI pending)

`QuantitativeLogChoice.lean` imports `QuantitativeReal.lean` and
attempts to prove that `log Q ≥ 2048` makes the choice
`r=floor(log Q/(8 loglog Q))` satisfy the integer sieve budget.
The final log/loglog frequency bound remains a separate corollary.
No changes to the import graph of the main theorem.

### Optional final log/loglog rate (CI pending)

`QuantitativeLogRate.lean` imports `QuantitativeLogChoice.lean`
and translates its certified integer budget into explicit
log/loglog decay of real frequencies. The threshold `log Q≥2048`
is deliberately conservative. The extra module remains outside
the main theorem's import graph.

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
lake env lean VerifiedQuantitativeBound.lean
```

`lake build` includes four original verification entry points and the
optional quantitative certificate. The previous axiom audit covered the
original four certificates (`propext`, `Classical.choice`, `Quot.sound`;
no `sorryAx`). The optional certificate was successfully built and independently
checked in GitHub Actions run `41234713571` (2026-10-31, commit
`4629474`), reporting only the same three standard axioms.

When a module is renamed or removed, update **both** this document,
`README.md`, `lakefile.toml`, and the GitHub Actions workflow.
Do not claim publication novelty solely because a formula has been
formalized.
