# Sparse Deletion and Triangular Prefix Sums

A Lean 4 + Mathlib formalization of a density theorem for prefix sums of squares after deleting an arbitrary set of natural density zero.

## Author

Przemysław Czerkas

## Main theorem

Let `E ⊆ ℕ` have natural density zero. Enumerate the positive integers not belonging to `E` increasingly as

```text
a₀ < a₁ < a₂ < ⋯ .
```

Then the set of indices `n` for which the prefix sum

```text
a₀² + a₁² + ⋯ + aₙ₋₁²
```

is triangular has natural density zero.

In the formalization, the theorem is:

```lean
theorem SparseDeletion.main_sparse_deletion_unconditional
    (E : Set ℕ) (hE : HasDensityZero E) :
    HasDensityZero { n : ℕ | Triangular (keptIndexPrefix E n) }
```

The principal definitions are:

- `Triangular s`: `s` is a triangular number;
- `HasDensityZero E`: the counting function of `E`, divided by `X`, tends to zero;
- `keptNth E n`: the `n`-th positive integer outside `E`;
- `keptIndexPrefix E n`: the sum of the squares of the first `n` retained integers.

The indexing starts at `0`, so `keptIndexPrefix E n` is the sum over `i < n`.

## Formal verification

The end-to-end verification entry point is:

```text
VerifiedCompleteProof.lean
```

To build and inspect the final certificate:

```sh
lake build VerifiedCompleteProof
lake env lean VerifiedCompleteProof.lean
```

To build the main theorem together with the composite-number corollary:

```sh
lake build VerifiedCompleteProof CompositeCorollary
```

The expected result is a successful build. The certificate prints the axioms used by the principal declarations.

For the main theorem, Lean reports only:

```text
propext
Classical.choice
Quot.sound
```

In particular, the final dependency cone contains no `sorryAx`.

This means that the final theorem is checked by the Lean kernel without an unproved theorem placeholder in its dependency chain. As usual, the result is conditional on the correctness of the Lean kernel, the pinned Mathlib dependencies, and the correspondence between the formal statement and the intended mathematical statement.

## Proof architecture

The proof has two main parts.

### 1. Finite-field value-set estimate

The difficult arithmetic component concerns the cubic map

```text
x ↦ x³ − x
```

over finite fields. The formalization proves a lower bound for its value set by constructing a three-to-one injection into points on a conic.

The main files are:

```text
CubicCollisionBridge.lean
ConicPointBound.lean
CubicRepresentative.lean
CubicConicInjection.lean
```

### Exact cubic value-set/conic identity

The optional `CubicConicExact.lean` module strengthens the conic injection
to a bijection. For **every finite field** `F` (including characteristics
2 and 3), it verifies the exact identity

```text
3 * |F| = 3 * |{x³ - x : x ∈ F}| + |{(x,y) ∈ F² : x² + xy + y² = 1}|.
```

The key additional lemma is `cubicCode_surj_conic`; the final theorem is
`cubic_value_set_conic_exact`. These proofs use no `sorryAx`.
The follow-up module `ConicExactCount.lean` completes the elementary count
without character sums or the Weil bound. For every finite field `F` with
`(3 : F) ≠ 0`, it proves

```text
|{(x,y) ∈ F² : x² + xy + y² = 1}| + |{t ∈ F : t² + t + 1 = 0}| = |F| + 1.
```

It then proves the quadratic has either zero or two roots, derives the
conic point count for `|F| % 3 = 1` and `|F| % 3 = 2`, and finally proves
**the exact classical cubic value-set formula**:

```text
|{x³ - x : x ∈ F}| = (2*|F|+1)/3  if |F| % 3 = 1;
|{x³ - x : x ∈ F}| = (2*|F|-1)/3  if |F| % 3 = 2.
```

`cubic_value_set_card_prime` specializes this to all prime fields `ZMod p`
with `p ≥ 5`, including a proof that the two congruence cases are exhaustive.
The exact counting modules are optional and are not needed for the existing
main density theorem. The result is classical, not a novelty claim.

Verify with `lake build VerifiedExactValueSet VerifiedCompleteProof CompositeCorollary`.
All printed axioms are the standard Lean axioms, with no `sorryAx`.

### Abstract sparse-perturbation theorem (independently verified)

The main density argument is now a **specialization** of the reusable theorem
`sparsePerturbation_zeroDensity_of_uniform_small_blocks` in
`SparsePerturbation.lean`. It assumes only that:

- the integer-valued perturbation `d` is constant across each step whose
  destination is outside a density-zero set `E`;
- for every `ε > 0`, some fixed block length `M > 0` has a uniformly
  small ratio `C/M < ε` of indices with `f(n) + b ∈ A`, for **all**
  starting points and all integer shifts `b`.

It concludes that `{n | f(n) + d(n) ∈ A}` has natural density zero.
No assumption bounds the perturbation's size or jump magnitudes.

`sparsePerturbation_zeroDensity_of_uniform_ratio_sieves` is the
convenient geometric-contraction corollary used by `DensityToZero.lean`.
The abstract theorem imports only `CountingDensity.lean` and Mathlib,
not the historic finite-prime sieve. The older bounds remain available.

See [PROOF_ARCHITECTURE.md](PROOF_ARCHITECTURE.md) for the minimal
logical proof path, its limitations, and how it relates to the exact conic
point count.

Verify the new theorem separately with:

```sh
lake build VerifiedPerturbation
lake env lean VerifiedPerturbation.lean
```

### Generic CRT contraction (refactored)

The CRT sieve is proved once for arbitrary natural-number coefficients
`numer` and `denom`:

```lean
crt_sieve_product_count_param
uniformCubicSieve_of_modular_family_param
```

If the surviving fraction for every pairwise-coprime modulus is at most
`numer / denom`, with `0 < numer < denom`, the iterated sieve has
survival fraction at most `(numer / denom)^r`. The density-zero transfer
is also parametric:

```lean
zeroDensityByValue_of_uniform_ratio_sieves
zeroDensityByIndex_of_uniform_ratio_sieves
zeroDensityByIndex_of_modular_family_param
```

The actual proof uses `numer = 6` and `denom = 7` directly, without
grouping pairs of modular tests to obtain a weaker `3/4` estimate.
The Hasse-based `3/4` path and the unconditional value-set `6/7` path
both call the same parametric interface directly. The obsolete fixed-ratio
compatibility wrappers have been removed. No additional libraries are needed.

### 2. Transfer to sparse deletion

The finite-field estimate is transferred to the original problem through:

```text
MainReduction.lean
MainExactValueReduction.lean
MainUnconditionalValueSet.lean
```

The final theorem is exposed by:

```text
VerifiedCompleteProof.lean
```

The foundational definitions and elementary lemmas are separated into:

```text
SparseDeletionBase.lean
```

The sorry-free candidate-set interface is in:

```text
SparseDeletion.lean
```

## Corollary for composite integers

The repository also contains the following unconditional corollary.

Let

```text
E = { n ∈ ℕ | n = 1 or n is prime }.
```

The complement consists of the composite positive integers. The theorem implies that the indices for which the prefix sum of the squares of successive composite integers is triangular have natural density zero.

The formal statement is:

```lean
theorem SparseDeletion.composite_square_prefix_triangular_density_zero :
  HasDensityZero { n : ℕ |
    Triangular (keptIndexPrefix nonComposites n) }
```

It is verified with:

```sh
lake build CompositeCorollary
```

## Reproducible environment

The project pins the Lean toolchain in:

```text
lean-toolchain
```

Current toolchain:

```text
leanprover/lean4:v4.35.0
```

The exact Mathlib revision and other dependencies are pinned in:

```text
lake-manifest.json
```

The project can be checked independently on another machine with:

```sh
git clone https://github.com/pczerkas/sparse-deletion-lean.git
cd sparse-deletion-lean
lake build VerifiedCompleteProof
lake env lean VerifiedCompleteProof.lean
```

The first build may download Lean and Mathlib dependencies.

## Scope of the result

The theorem concerns natural density of the set of triangular-hit indices.

It does not claim that:

- there are only finitely many triangular hits;
- there are no triangular hits after some point;
- the triangular-hit set is empty;
- the undeleted case has density-zero hits for the same reason.

The undeleted case `E = ∅` reduces to the classical square-pyramidal sequence

```text
1² + 2² + ⋯ + n² = n(n+1)(2n+1)/6.
```

The intersection of square-pyramidal and triangular numbers is a separate classical Diophantine problem.

## Relation to prior literature

The repository is intended as a formal verification artifact. A preliminary literature search found related work on:

- square-pyramidal numbers and their intersections with triangular numbers;
- equidistribution questions for square-pyramidal numbers;
- sums of squares and triangular numbers;
- perfect powers in polynomial value sets;
- density-zero results for special values of other arithmetic sequences;
- general asymptotic density and sparse-sequence theory.

The following sources are particularly relevant:

- E. W. Weisstein, “Square Pyramidal Number,” MathWorld:  
  <https://mathworld.wolfram.com/SquarePyramidalNumber.html>
- OEIS A000330, “Square pyramidal numbers”:  
  <https://oeis.org/A000330>
- J. Cilleruelo and F. Luca, “On the Sum of the First n Primes,” *The Quarterly Journal of Mathematics* 59 (2008), 475–486:  
  <https://doi.org/10.1093/qmath/ham055>
- A. Dong, K. Saettone, K. Song, and A. Zaharescu, “An Equidistribution Result for Differences Associated with Square Pyramidal Numbers”:  
  <https://arxiv.org/abs/2412.10097>
- A. Dong, K. Saettone, K. Song, and A. Zaharescu, “An Equidistribution Result for Differences Associated to Square Pyramidal Numbers II”:  
  <https://arxiv.org/abs/2505.04166>
- B. Kane and Z.-W. Sun, “On Almost Universal Mixed Sums of Squares and Triangular Numbers”:  
  <https://arxiv.org/abs/0808.2761>
- A. Akbary and Z. S. Aygin, “Sums of triangular numbers and sums of squares”:  
  <https://arxiv.org/abs/2107.00787>
- A. Ostafe, L. Pottmeyer, and I. E. Shparlinski, “Perfect powers in value sets and orbits of polynomials”:  
  <https://nyjm.albany.edu/j/2021/27-35p.pdf>
- I. Niven, “The Asymptotic Density of Sequences”:  
  <https://www.ams.org/journals/bull/1951-57-06/S0002-9904-1951-09543-9/S0002-9904-1951-09543-9.pdf>

Based on the searches performed so far, we have not identified a published result with the exact combination:

```text
arbitrary density-zero deletion
→ increasing enumeration of the complement
→ prefix sums of squares
→ triangular values of density zero.
```

This is not a proof that no such result exists. We are not aware of a previous result proving this statement for arbitrary density-zero deletions.

## AI assistance

The author used OpenAI ChatGPT to assist in mathematical exploration, proof development, and Lean formalization. The author takes full responsibility for the results and their correctness.

## License

This project is released under the MIT License. See [LICENSE](LICENSE).

If this work is submitted to arXiv, the arXiv submission will be distributed under the perpetual, non-exclusive license granted to arXiv under its submission terms.
