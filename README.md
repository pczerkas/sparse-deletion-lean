# Sparse Deletion and Triangular Prefix Sums

A Lean 4 / Mathlib formalization of a natural-density theorem, with a reusable
sparse-perturbation lemma and an independent elementary finite-field calculation.

**Author:** Przemysław Czerkas

## Main theorem

Let `E ⊆ ℕ` have natural density zero, and enumerate the **positive**
integers outside `E` increasingly as `a₀ < a₁ < a₂ < ···`. Then the
indices `n` for which

```text
a₀² + a₁² + ... + aₙ₋₁²
```

is a triangular number have natural density zero.

The exact Lean theorem, in `MainUnconditionalValueSet.lean`, is:

```lean
theorem SparseDeletion.main_sparse_deletion_unconditional
    (E : Set ℕ) (hE : HasDensityZero E) :
    HasDensityZero { n : ℕ | Triangular (keptIndexPrefix E n) }
```

The statement covers **arbitrary** density-zero deleted sets, with no
regularity assumption on the positions or sizes of their elements. It
does **not** claim finitely many triangular hits or an eventual absence
of hits. It does **not** apply directly to sums of the squares of the
initial primes, since removing nonprimes is a density-one deletion.

## Reproduce the verification

The project pins Lean `v4.35.0` via `lean-toolchain`, Mathlib
`v4.35.0` via `lakefile.toml`, and the exact package revisions
via `lake-manifest.json`.

On a machine with Lean/Lake installed:

```sh
git clone https://github.com/pczerkas/sparse-deletion-lean.git
cd sparse-deletion-lean
lake exe cache get
lake build
```

You can instead run the tracked `./setup_and_check.sh` bootstrap script.
The four original verification certificates and the new quantitative certificate
are the default build targets:

- `VerifiedCompleteProof.lean` — unconditional density theorem;
- `CompositeCorollary.lean` — density theorem for composite squares;
- `VerifiedExactValueSet.lean` — exact finite-field formula;
- `VerifiedPerturbation.lean` — independent generic perturbation lemma;
- `VerifiedQuantitativeBound.lean` — finite-N upper bounds for triangular hits
  after sparse deletions (GitHub Actions run 41234713571 passed).

To inspect the printed axioms, run:

```sh
lake env lean VerifiedCompleteProof.lean
lake env lean VerifiedExactValueSet.lean
lake env lean VerifiedPerturbation.lean
lake env lean VerifiedQuantitativeBound.lean
```

All key theorems use only the standard Lean axioms `propext`,
`Classical.choice`, and `Quot.sound`; **none depend on `sorryAx`**.
Formal correctness is relative to the Lean kernel, pinned Mathlib code,
and accuracy of the formal mathematical statement.

## Proof components

The active proof is divided into two independent inputs and a short
specialization/transfer layer.

**Generic sparse perturbations:**
`CountingDensity.lean` → `SparsePerturbation.lean`.

The principal reusable theorem is
`sparsePerturbation_zeroDensity_of_uniform_small_blocks`. Given arbitrary
`f d : ℕ → ℤ` and `A : Set ℤ`, assume the jumps of `d` occur only
on a density-zero set `E`, and that for each `ε > 0` a common block
length `M > 0` bounds the shifted hits `f(n)+b ∈ A` by
`C < ε M`, uniformly in the starting index and integer shift `b`.
Then `{n | f(n)+d(n) ∈ A}` has natural density zero.

**Arithmetic sieve:**
`CRTGeneral.lean` → `SieveInduction.lean`, with the concrete
coprime-prime family in `PrimeFamily.lean`.
The geometric-contraction wrapper
`sparsePerturbation_zeroDensity_of_uniform_ratio_sieves` supplies the
interface between CRT and the generic perturbation theorem.

**Elementary cubic value-set input:**
`CubicCollisionBridge.lean` → `ConicPointBound.lean` →
`CubicRepresentative.lean` → `CubicConicInjection.lean`.
These establish the lower bound for the image of `x ↦ x³ − x` using
a collision conic and elementary finite-set counting, *without* Weil's
bound. The main arithmetic reduction also uses
`CubicShape.lean`, `CubicSumBridge.lean`, `PrimeCubicPoly.lean`,
`PrimeSquarePass.lean`, `AffineValueBridge.lean`,
`ImageBoundBridge.lean`, `ResidueCountBridge.lean`, and
`SquareValueCount.lean`. The last of these uses the standard elementary
quadratic-character identity to count squares, **not** a Weil/Hasse bound.

**Transfer to the theorem:**
`SparseDeletionBase.lean`, `RemovedSquares.lean`, and
`KeptSquaresBridge.lean` express the deleted-square prefix as a
piecewise-constant perturbation. `DensityToZero.lean` applies the generic
lemma, `IndexBridge.lean` / `IndexGrowth.lean` /
`IndexTransfer.lean` transfer from value indices to enumeration indices,
and `MainReduction.lean` / `MainExactValueReduction.lean` /
`MainUnconditionalValueSet.lean` finish the proof.

The full physical dependency and logical explanation are in
[PROOF_ARCHITECTURE.md](PROOF_ARCHITECTURE.md).
The separate mathematical and assumption-level review is in
[ASSUMPTION_AUDIT.md](ASSUMPTION_AUDIT.md), including the limitations
of the last clean-build verification attempt.

## Quantitative finite-N bounds (feature branch)

The optional module `QuantitativeBound.lean` reuses the *existing* shifted
uniform sieve and counting lemma. For every fixed block length `M > 0`
and uniform bound `C` for the number of shifted candidates in a block,
it proves (with `countUpTo` counting indices below `N`):

```text
#value-hits below N <= C * (N / M) + M * #deleted-below-N + (N % M).
```

It also transfers this bound to enumeration indices if the `N`-th
retained integer is less than `2*N+2`, and proves a simplified variant.
No zero-density hypothesis is required for the finite value-index bound;
its hypotheses are the uniform shifted block estimate and `M > 0`.
The index bound additionally requires infinitude of retained positives
and the explicit upper bound on their `N`-th element.

The companion module `QuantitativeSieve.lean` reuses the same elementary
prime-field estimate and CRT to establish, for every `r, N` and every deleted
set `E`, the existence of a positive modulus `M_r` satisfying:

```text
7^r * H_E(N) <= 6^r * N + 7^r * M_r * (e_E(N) + 1).
```

This is an unconditional **finite** inequality (no density assumption on E)
and is also available after transferring to retained-sequence indices,
provided an explicit upper bound on the N-th survivor is supplied.
The modulus depends on the sieve depth; the displayed inequality must not
be interpreted as an effective N-only decay rate without controlling M_r.

A further optional module `QuantitativeEffective.lean` obtains an **explicit**
albeit loose bound on the sieve modulus from Bertrand's postulate:
`M_r ≤ 37^r·2^(r²)`. Consequently, with `e(N) = #E∩[0,N)`,
`H_E(N)` value-index hits satisfy the unconditional finite estimate:

```text
7^r * H_E(N) <= 6^r * N + 7^r * (37^r * 2^(r*r)) * (e(N)+1).
```

Under the stated sparsity budget
`7^r * (37^r * 2^(r*r)) * (e(N)+1) ≤ 6^r*N`, a separate theorem gives
`7^r*H_E(N) ≤ 2*6^r*N`. An explicit variant for hits indexed by the
retained sequence is also provided, assuming the N-th retained value is
less than `2*N+2`. These statements remove the hidden modulus,
but the bounds are loose and not a finiteness result. The new module is
included in the optional Lean verification target. The elementary real-logarithm
optimization and its limitations are explained in
[QUANTITATIVE_RATE.md](QUANTITATIVE_RATE.md). A further optional module
`QuantitativeSharper.lean` retains each individual Bertrand factor,
proving the smaller modulus bound
`M_r ≤ 37^r * 2^(r*(r-1)/2)` and the corresponding sharper value-index
and retained-index estimates. Both use the existing finite-field sieve.
This improved result was Lean-certified by GitHub Actions run
`41236256862` (commit `4b65c88`, `BUILD_EXIT=0`, no `sorryAx`).
The logarithmic corollary is not yet a Lean theorem. The *finite-N*
statements were verified with pinned Lean 4.35.0 and Mathlib v4.35.0,
including the polynomial extension in [GitHub Actions run 41237410122](https://github.com/pczerkas/sparse-deletion-lean/actions/runs/41237410122).
All printed axioms are the three standard Lean axioms.
This computational verification is distinct from an independent mathematical
review or a literature novelty assessment. They do not invoke any theorem about
representation as five distinct squares. Both optional modules are kept
out of the main theorem's import graph.

## Polynomial growth of the sieve primes (optional experimental module)

The optional `PrimePolynomialBound.lean` uses Mathlib's
`Chebyshev.pi_ge` and elementary logarithm inequalities to prove
a coarse polynomial upper bound `largePrime r ≤ 64*(r+50)^2`.
This prime bound passed GitHub Actions run `41236892361` (commit
`67fa5d4`, no `sorryAx`, only standard axioms). The companion module
`QuantitativePolynomial.lean` uses it to prove the explicit CRT modulus bound
`M_r ≤ (64*(r+50)^2)^r`, and both value-index and retained-index finite-N
inequalities. That companion module passed GitHub Actions run `41237410122` (commit
`a0862e0`, `BUILD_EXIT=0`, no `sorryAx`, only standard axioms).
The further real-logarithm optimization is documented in
[QUANTITATIVE_RATE.md](QUANTITATIVE_RATE.md), not yet formalized in Lean.

## Certified explicit sieve-depth threshold

The optional module `QuantitativeRate.lean` translates the polynomial
CRT estimate into a finite, fully integer-valued rate statement. For
any depth `r`, if the deletion budget obeys

```text
(448*(r+50)^2)^r * (e(N)+1) ≤ N,
```

then `7^r*H_E(N) ≤ 2*6^r*N`. The same threshold is proved
for retained-sequence indexing under the standard Nth-survivor
hypothesis. This avoids logarithms and is intended as an independently
checkable stepping stone to the optimized real-logarithm corollary.
Both new budget lemmas passed [GitHub Actions run 41238649297](https://github.com/pczerkas/sparse-deletion-lean/actions/runs/41238649297)
(commit `ab671d6`, `BUILD_EXIT=0`, only standard axioms).

## Real-frequency statement (optional bridge to logarithmic optimization)

`QuantitativeReal.lean` converts the integer-budget bounds to the
real relative-frequency inequality
`(H_E(N):ℝ)/N ≤ 2*(6/7)^r`, for each positive N and
each sieve depth satisfying the explicit budget. An analogous
retained-index statement is also provided with its Nth-survivor
hypothesis. This is deliberately separate from the final analytic
choice of r; both statements passed GitHub Actions run `41238649297`
(commit `ab671d6`, no `sorryAx`).

## Logarithmic depth selection (separate optional module)

`QuantitativeLogChoice.lean` formalizes the real-analytic budget check
for `r = floor(log Q/(8*log(log Q)))`, where `Q=N/(e(N)+1)`,
assuming `N>0` and `log Q ≥ 2048`. Its conclusion is precisely
the integer budget required by `QuantitativeRate.lean`. This step passed GitHub Actions run `41239749155` (commit
`d83bdb5`). Its certificate prints only standard axioms, and
the original main proof is unaffected.

## Explicit log/loglog rate (optional final corollary)

`QuantitativeLogRate.lean` derives the **real log/loglog bound** from
the previously certified threshold. Write
`Q=N/(e(N)+1)`, `L=log Q`. For `N>0` and `L≥2048` it proves

```text
H_E(N)/N ≤ (7/3) * exp(-log(7/6) * L/(8*log L)).
```

There is also a retained-index version normalized by `2N+2`,
under the existing Nth-survivor assumption. The full module passed GitHub Actions run `41240273708`
(commit `a7fd3b7`; `BUILD_EXIT=0`, no `sorryAx`,
only `propext`, `Classical.choice`, `Quot.sound`).

## Improved explicit constants and further research

The verified optional module `QuantitativeConstants.lean`
reduces the elementary prime upper bound from
`64*(r+50)^2` to `16*(r+50)^2`, lowering the explicit CRT
modulus to `(16*(r+50)^2)^r`. Its finite-N statements passed GitHub Actions run `41241354688`
(commit `e9c4b3f`, only standard axioms and no `sorryAx`).

The separate `QuantitativeExponent.lean` **proves** a stronger
logarithmic sieve depth `floor(L/(3*log L))` instead of
`floor(L/(8*log L))`, improving the exponential coefficient
from `log(7/6)/8` to `log(7/6)/3` for `log Q ≥ 2048`.
The value- and retained-index versions passed GitHub Actions
run `41241698431` (commit `07e6d2a`, `BUILD_EXIT=0`,
no `sorryAx` and only standard axioms).

[OPTIMALITY_CONSTRUCTION.md](OPTIMALITY_CONSTRUCTION.md) develops
a mathematical construction (using classical results of Wright
and Siegel) of arbitrarily sparse deletion sets with infinitely
many triangular hits. It is not a Lean proof and **does not
establish optimality of the quantitative upper bound**.

[LITERATURE_REVIEW.md](LITERATURE_REVIEW.md) records a targeted
literature comparison and separates classical ingredients from
our precise sparse-deletion statement. No claim of research
novelty is made.

## Stronger log/loglog rate (fully verified)

The optional modules `QuantitativeHalfBudget.lean`,
`QuantitativeHalfChoice.lean`, and `QuantitativeHalfRate.lean`
improve the logarithmic sieve depth to
`r=floor(L/(2*log L))` with `L=log(N/(e(N)+1))≥2048`.
They prove the finite-budget threshold using the *verified*
prime bound `largePrime r≤16*(r+50)^2`, and obtain

```text
H_E(N)/N ≤ (7/3) * exp(-(log(7/6)/2)*L/log L).
```

The matching retained-index theorem has the same
Nth-survivor hypothesis as earlier variants. The full
certificate passed [GitHub Actions run 41279672392](https://github.com/pczerkas/sparse-deletion-lean/actions/runs/41279672392),
commit `080b44b`, with `BUILD_EXIT=0`, no `sorryAx`,
and only the three standard Lean axioms.

### Separate research on sharper local sieve constants

[WEIL_REFINEMENT.md](WEIL_REFINEMENT.md) describes the
stronger local contraction `3/4` and its exact formalization
boundary. The finite-field character identity,
the conditional `3/4` lemma, the CRT reduction and
the cubic root-count lemma are **Lean-certified**
(GitHub Actions runs `41290984477`, `41291253800`,
`41292056130`). The follow-up `WeilSingleHypothesis.lean` and
`WeilConditionalLogRate.lean` modules passed GitHub
Actions run `41292331952` (commit `42256a8`).
They show that the **single explicit** input
`CubicWeilCharacterUpper` suffices to prove

```text
H_E(N)/N ≤ (8/3)*exp(-(log(4/3)/2)*L/log L),
L = log(N/(e(N)+1)), L≥2048.
```

The matching retained-index inequality is also certified
under its survivor-growth hypothesis. **The deep Weil
character-sum inequality itself remains unformalized.**
This is a rigorously certified *conditional* theorem,
not a stronger unconditional result.

[SIEVE_EXPERIMENT.md](SIEVE_EXPERIMENT.md) reports
exact modular tests for every prime `37≤p≤500`
with reproducible `explore_sieve_residues.py`.
These finite tests are *not* a uniform proof.

[OPTIMALITY_CONSTRUCTION.md](OPTIMALITY_CONSTRUCTION.md)
now also gives a mathematical lower bound
`H_E(N)≥max(0,floor(e_E(N)/5)-1)` for the
arbitrarily sparse five-square construction.
It is not a matching lower bound for the
current upper rate and is not Lean-certified.

## Independent exact cubic value-set result

We also prove an **optional**, stronger, classical formula, independently
certified by `VerifiedExactValueSet.lean`:

For every finite field `F` with characteristic different from 3,

```text
|{(x,y) ∈ F² : x² + xy + y² = 1}| =
    |F| - 1   if |F| ≡ 1 (mod 3)
    |F| + 1   if |F| ≡ 2 (mod 3).
```

Consequently, the number of values of `x³-x` equals

```text
(2|F|+1)/3   if |F| ≡ 1 (mod 3)
(2|F|-1)/3   if |F| ≡ 2 (mod 3).
```

`CubicConicExact.lean` establishes an exact correspondence between
cubic fibers and conic points; `ConicExactCount.lean` counts those
points. The prime-field corollary is
`cubic_value_set_card_prime` (for every prime `p ≥ 5`).

The **main density proof requires only the elementary lower bound**, not
this stronger exact formula. The exact result is classical and is not
claimed to be a new mathematical discovery.

## Composite-square corollary

The set `E = {1} ∪ {primes}` has density zero. Hence the indices of
triangular partial sums of the squares of successive **composite**
positive integers have density zero. The formal theorem is
`SparseDeletion.composite_square_prefix_triangular_density_zero`
in `CompositeCorollary.lean`.

## Scope, provenance and publication

This repository contains the **active, verified proof only**. Earlier
alternative approaches and experimental files were removed from the
current tree; their history remains available through Git. No missing
historical file is required to rebuild the results.

The mathematical statements should be evaluated separately from the
novelty of their formalizations. In particular, the cubic value-set
formula is known classically; the status in the research literature of
the full sparse-deletion density statement should be independently
verified before claims of novelty.

The author used OpenAI ChatGPT for mathematical exploration, proof
development, refactoring, and Lean assistance. The author is responsible
for reviewing the mathematical statements and results.

**License:** MIT. See [LICENSE](LICENSE).
