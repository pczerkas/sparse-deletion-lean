# Quantitative rate for triangular square-prefix hits

**Status (2026-10-31):** the finite bounds **and the explicit log/loglog
estimate** are certified by Lean 4.35.0 / Mathlib v4.35.0.
GitHub Actions run [41240273708](https://github.com/pczerkas/sparse-deletion-lean/actions/runs/41240273708)
successfully compiled the complete `VerifiedQuantitativeBound.lean`
certificate, with `BUILD_EXIT=0`, no `sorryAx`, and only the standard
`propext`, `Classical.choice`, `Quot.sound` axioms.

The following statements are additional **consequences** of the original
main density-zero theorem. They are logically kept in optional modules
and do not modify the statement or imports of the main theorem.

## Definitions and conventions

For any deletion set `E ⊆ ℕ` and `N>0`, write

- `e(N) = #(E ∩ [0,N))`;
- `H_E(N) = # {n < N : the sum of squares of positive k ≤ n
  with k ∉ E is triangular}`;
- `Q(N) = N/(e(N)+1)`, a positive real number.

These `H_E` values count hits **by the original integer value**, not
by position in the surviving enumeration. A separate, formally
verified result below addresses the enumeration index.

## The finite-N results

`QuantitativeBound.lean` and `QuantitativeSieve.lean` specialize the
original shifted modular sieve and the perturbation-count lemma. They
give, for each depth `r`, a positive CRT modulus `M_r` and the bound

```text
7^r * H_E(N) ≤ 6^r * N + 7^r * M_r * (e(N)+1).
```

These inequalities do **not** assume that `E` has zero density.

Two separate elementary bounds on `M_r` were formalized:

- **Bertrand-only:** `M_r ≤ 37^r * 2^(r*(r-1)/2)`, in
  `QuantitativeSharper.lean`.
- **Chebyshev prime-counting bound:**
  `largePrime r ≤ 64*(r+50)^2` and
  `M_r ≤ (64*(r+50)^2)^r`, in
  `PrimePolynomialBound.lean` and `QuantitativePolynomial.lean`.

The second gives the stronger general estimate

```text
H_E(N)/N ≤ (6/7)^r + (64*(r+50)^2)^r / Q(N).
```

Here `r` is any natural number. The proof uses Mathlib's explicit
elementary Chebyshev inequality, not the prime number theorem, and
does not involve any assertion about five distinct squares.

## Certified effective integer budget

`QuantitativeRate.lean` proves the exact implication

```text
if (448*(r+50)^2)^r * (e(N)+1) ≤ N, then
7^r * H_E(N) ≤ 2 * 6^r * N.
```

For `N>0`, `QuantitativeReal.lean` equivalently derives

```text
H_E(N)/N ≤ 2*(6/7)^r.
```

This is effective for any explicit finite `N, r` and `e(N)`, without
calculating logarithms.

## Fully certified log/loglog decay

Assume `N>0` and set

```text
Q = N/(e(N)+1)
L = log Q.
```

For the conservative numerical threshold `L ≥ 2048`, select

```text
r = floor(L/(8*log L)).
```

`QuantitativeLogChoice.lean` proves that this `r` **satisfies**
the integer budget above. The underlying elementary calculations
are `r ≤ L`, `448*(r+50)^2 ≤ L^3`, and
`r*3*log L ≤ L`, whence
`(448*(r+50)^2)^r ≤ exp L = Q`.

`QuantitativeLogRate.lean` adds the exact floor-rounding estimate
and **kernel-certifies** the final inequality

```text
H_E(N)/N ≤ (7/3) *
  exp( -(log(7/6)/8) * log(Q)/log(log(Q)) )
```

for all `N>0` with `log Q≥2048`.

Equivalently, with the explicit positive constant
`c = log(7/6)/8`, one obtains

```text
H_E(N) ≤ (7/3) * N *
  exp(-c * log Q/log(log Q)).
```

No assumption of `d(E)=0` is needed in these finite-parameter
statements. When `d(E)=0`, then `Q(N)→∞`, so the bound eventually
applies and improves the qualitative density-zero conclusion.

## Indices in the retained sequence

Let `a_0<a_1<⋯` enumerate the surviving positive integers and
let `H_E^ind(N+1)` count triangular square-prefix hits among the
first `N+1` enumeration positions.

`QuantitativeLogRate.lean` proves the analogous inequality

```text
H_E^ind(N+1)/(2*N+2) ≤ (7/3) *
  exp( -(log(7/6)/8) * log(Q₂)/log(log(Q₂)) ),
Q₂ = (2*N+2)/(e(2*N+2)+1).
```

The formal hypotheses include:
- the surviving positive integers are infinite;
- `a_N < 2*N+2` (as an explicit survivor-growth bound);
- `log Q₂ ≥ 2048`.

When `E` has zero density, these additional growth and threshold
conditions hold eventually. To normalize by the number of enumeration
positions, observe that
`H_E^ind(N+1)/(N+1)=2*H_E^ind(N+1)/(2*N+2)`;
therefore a corresponding bound with coefficient `14/3` follows
mathematically. The factor-of-two normalization is not presented
as a separate named Lean theorem.

## Interpretation and limitations

- **Upper-density result, not finiteness.** The bounds allow
  infinitely many rare triangular hits.
- The numerical threshold `log Q ≥ 2048` is **enormous**.
  Constants are chosen for proof simplicity, not practical sharpness.
- None of the results settles the initial-prime square-prefix
  problem. The primes themselves have density zero, whereas the
  hypotheses concern deleting a zero-density subset from all integers.
- A successful Lean build verifies formal implication between
  definitions and hypotheses. It does **not** establish research
  novelty or replace independent peer review.

**Sources in this repository:** `QuantitativeBound.lean`,
`QuantitativeSieve.lean`, `QuantitativeEffective.lean`,
`QuantitativeSharper.lean`, `PrimePolynomialBound.lean`,
`QuantitativePolynomial.lean`, `QuantitativeRate.lean`,
`QuantitativeReal.lean`, `QuantitativeLogChoice.lean`,
`QuantitativeLogRate.lean` and `VerifiedQuantitativeBound.lean`.

## Refined Chebyshev base: experimental improvement

A new optional module `QuantitativeConstants.lean` aims to
prove `largePrime r ≤ 16*(r+50)^2` rather than
`64*(r+50)^2`. If the new CI check passes, the corresponding
general finite inequality will improve to

```text
H_E(N)/N ≤ (6/7)^r + (16*(r+50)^2)^r/Q(N).
```

The previously certified logarithmic conclusion remains
unchanged. The improved prime constant and both corresponding finite
inequalities were Lean-verified in GitHub Actions run
`41241354688` (commit `e9c4b3f`).

## Faster exponent (experimental)

The optional module `QuantitativeExponent.lean` aims to
replace `floor(L/(8*log L))` by `floor(L/(3*log L))`
for `L=log Q≥2048`. It would strengthen the exponential
rate constant from `log(7/6)/8` to `log(7/6)/3`.
The original loglog theorem remains unchanged and
certified independently. The proposed faster rate is
**not** certified until its own CI run succeeds.
