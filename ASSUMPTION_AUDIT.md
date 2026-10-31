# Assumption and statement audit — 2026-10-30

**Scope:** `refactor/minimal-proof-dependencies`, starting from commit
`c1c19ef`. This is a review of the actual source declarations and of
the mathematical implications connecting them, not a substitute for
an independent external refereeing or for a completed clean rebuild.

## 1. Exact mathematical target

For a fixed `E : Set ℕ`, define

- `E` has natural density zero if
  `#(E ∩ [0,N)) / N → 0`;
- `a_n := Nat.nth (fun x => 0 < x ∧ x ∉ E) n`;
- `S_n := ∑_{j < n} a_j²` (in `ℕ`);
- `Triangular(s) := ∃ m : ℕ, 2*s = m*(m+1)`.

The formal conclusion
`HasDensityZero {n : ℕ | Triangular (keptIndexPrefix E n)}`
is exactly

```text
lim_(N→∞) #{0 ≤ n < N : ∃ m ∈ ℕ, 2∑_{j<n}a_j² = m(m+1)} / N = 0.
```

It does **not** prove finiteness of the hits, an eventual cutoff,
or a statement about the first `n` primes.

**Actual assumptions of the final theorem:**
`E : Set ℕ` and `HasDensityZero E` only. Neither enumerability,
computability, regular spacing of deletions nor a size bound on the
deleted elements is assumed. The proof constructs the infinite
complement of `E` from `HasDensityZero E` in `IndexGrowth.lean`.

The natural-number convention includes `0` as triangular, so
`n=0` is a hit. This finite exception cannot affect natural density.
If `0 ∈ E`, that membership is immaterial because only positive
integers are enumerated.

## 2. Arithmetic sieve audit

`naturalSquareSum n` includes `0²+1²+⋯+n²`. It satisfies

```text
6 S(n) = n(n+1)(2n+1).
```

For each shift `b ∈ ℤ`, if `S(n)+b = m(m+1)/2`,
then `8(S(n)+b)+1 = (2m+1)²`. Hence every genuine hit
passes the quadratic-residue test modulo any chosen prime.
The test may accept spurious hits: **necessity, not equivalence**
is all the sieve uses.

For prime `p ≥ 37`, the cubic polynomial
`8(S(x)+b)+1` modulo `p` is affinely equivalent to
`x³−x`, because `2`, `3`, and `6` are invertible.
The equivalence is uniform over the shift `b`.

The conic injection establishes
`2p ≤ 3|{x³−x : x∈F_p}| + 1`. The number of square
values in `F_p` including zero is `(p+1)/2`.
A general finite-map lemma gives

```text
G_p + |image(f)| ≤ p + |squares(F_p)|,
G_p ≤ 5(p+1)/6,
7 G_p ≤ 6p  (for p ≥ 35).
```

The prime family is restricted to `p≥37`, so the final bound is valid.
The basic square count uses Mathlib's
`quadraticChar_sum_zero`, **not** a Hasse or Weil bound.

Independent small finite-field spot checks matched the cubic
value-set formula and the sieve bound for primes
`37, 41, 43, 47, 53, 59, 61, 67, 71`, over all shifts modulo
each tested prime. These checks are supplementary, not formal proof.

## 3. CRT and sparse variation audit

`largePrime` enumerates distinct primes ≥37. Thus each new
prime is coprime to the preceding product. The individual modular
predicates are periodic in `n` and include every genuine
triangular hit. The formal CRT induction proves a uniform bound

```text
7^r * candidates(u, M_r, b).card ≤ 6^r * M_r
```

for **every** integer shift `b` and **every** interval start `u`.
Uniformity in both parameters is essential; the proof establishes it.

Let
`D_E(n) = −∑_{0≤k≤n, k∈E} k²`.
Then `D_E(n+1)=D_E(n)` whenever `n+1∉E`.
The exact integer equality

```text
∑_{1≤k≤n, k∉E} k² = naturalSquareSum(n) + D_E(n)
```

is proved in `KeptSquaresBridge.lean`.
No regularity of the values or jumps of `D_E` is assumed.

For each fixed block length `M`, the generic proof bounds
the number of hits among the first `N` value indices by

```text
H(N) ≤ C * ⌊N/M⌋ + M * #(E ∩ [0,N)) + (N mod M).
```

Hence `limsup H(N)/N ≤ C/M` because `E` has density zero.
Taking `C/M ≤ (6/7)^r` and then `r→∞` establishes
density zero. The quantifier order is correct: **first fix**
`r,M_r`, **then let** `N→∞`.

## 4. From values to enumerated indices

`IndexBridge.lean` formally identifies the sum of the first
`n+1` retained squares with the sum up to the value `a_n`.
`IndexGrowth.lean` proves the retained positive integers form
an infinite sequence and that eventually `a_n < 2n+2`.
`IndexTransfer.lean` constructs an injection from the first
`N` triangular *enumeration-index* hits to triangular
*value-index* hits below roughly `2N`.

This is enough to transfer zero density. No claim is made that
the two index sets coincide, and they do not generally coincide.

## 5. Final assumptions and proof-theoretic status

`MainUnconditionalValueSet.lean` proves the modular value-set
lower bound internally, then discharges the only special
arithmetic hypothesis of `main_of_cubic_value_bound`.

Consequently, **the final theorem is not conditional on**
Weil, Hasse, the Riemann hypothesis, numerical searches,
or any unproven cubic character-sum estimate.

On 2026-10-30, clean rebuild attempts on Kompik were interrupted by
build/cache/resource limits. Subsequently, GitHub Actions verified the
feature branch on 2026-10-31 at commit `4629474` (workflow run
`41234713571`): fresh runner, `lake build` completed with `BUILD_EXIT=0`.
This does not replace independent mathematical peer review.

The CI log for the current feature-branch commit reports only
`propext`, `Classical.choice`, and `Quot.sound` for the original
certificates, with no `sorryAx`.

## Optional quantitative extension (feature/quantitative-hit-bound)

The additional module `QuantitativeBound.lean` specializes the existing
uniform block counting lemma to exact finite-N estimates for triangular
hits, both by original integer values and by retained-sequence indices.
It does not strengthen the mathematical conclusion to finiteness and does
not introduce a five-square representation assumption. The first feature-branch CI run (2026-10-31, commit `0556cff`)
passed and reported only `propext`, `Classical.choice`, and `Quot.sound`
for its three quantitative results. The later module `QuantitativeSieve.lean` derives a full finite-N CRT
estimate at arbitrary sieve depth `r`. Commit `4629474` passed GitHub
Actions run `41234713571`; all seven named quantitative axioms reports
showed only `propext`, `Classical.choice`, `Quot.sound`. The new formal
finite-N bound is kernel-certified. The optional module `QuantitativeEffective.lean` uses Bertrand to
prove an explicit modulus upper bound and a finite-N inequality.
The source version at commit `a05632a` passed GitHub Actions run
`41235478894` with `BUILD_EXIT=0` and only the standard three axioms.
The optional *retained-index* corollary passed GitHub Actions run
`41235710674` at commit `5eb2d35`: `BUILD_EXIT=0`, no `sorryAx`, and
only `propext`, `Classical.choice`, `Quot.sound`. The separate
real-logarithm optimization is documented in `QUANTITATIVE_RATE.md`
but is not yet formalized in Lean; a stronger prime-counting-based
rate is also not formalized. The further optional module
`QuantitativeSharper.lean` reduces the Bertrand exponent to
`r*(r-1)/2`. Its separate certificate passed GitHub Actions run
`41236256862` (commit `4b65c88`) with `BUILD_EXIT=0`; all four
new declarations use only `propext`, `Classical.choice`,
`Quot.sound`, with no `sorryAx`.

## Polynomial prime-family bound (verified in CI)

`PrimePolynomialBound.lean` is an optional verified module using
`Chebyshev.pi_ge` from Mathlib, an elementary lower bound for the
prime-counting function, proving
`largePrime r ≤ 64*(r+50)^2`.
It is not part of the original theorem. The bound passed GitHub
Actions run `41236892361` at commit `67fa5d4`, with no `sorryAx`
and only the standard Lean axioms. `QuantitativePolynomial.lean` is
a further optional finite-N corollary that passed GitHub Actions
run `41237410122` (commit `a0862e0`, `BUILD_EXIT=0`, no `sorryAx`,
only the standard axioms).

## Explicit finite-budget rates (new optional module; CI pending)

`QuantitativeRate.lean` proves an integer-only conditional rate from
the independently certified polynomial CRT estimate. The hypothesis
is a concrete growth threshold on `N/(e(N)+1)`, not an additional
assumption needed by the main theorem. The certificate passed GitHub Actions run `41238649297`
(commit `ab671d6`, `BUILD_EXIT=0`, no `sorryAx`,
only `propext`, `Classical.choice`, and `Quot.sound`).

## Real-frequency bridge (optional, CI pending)

`QuantitativeReal.lean` adds a direct relative-frequency consequence
`(H_E(N):ℝ)/N ≤ 2*(6/7)^r` subject to the explicit budget and
N>0. It does not assert a log-log corollary. Both real-frequency results passed GitHub Actions run `41238649297`,
commit `ab671d6`, using only standard Lean axioms.

## 6. Conclusions and risks

- **Statement correspondence:** PASS — formal statement matches
  the density-zero sparse-deletion problem, including indexing.
- **Missing mathematical premises:** none identified in this review;
  the key uniform modular bound is proved, not merely assumed.
- **Main proof structure:** PASS by source audit and the recorded
  pre-clean successful build.
- **Fresh CI build of all current Lean code:** PASS (2026-10-31, commit `a0862e0`, run `41237410122`).
- **Independently established novelty:** NOT ASSESSED. The
  `x³−x` exact value-set formula is classical.
- **Potential overclaims to avoid:** finite number of triangular
  hits; result on initial-prime squares; union of arbitrarily
  many zero-density deletion sets remaining density zero.

Any publication should identify the density-zero conclusion
precisely and include the pinned toolchain, independent build
log, exact statement, and `#print axioms` certificate.
