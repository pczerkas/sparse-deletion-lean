# Quantitative decay from the elementary Bertrand modulus bound

**Status:** mathematical consequence of the Lean-certified finite-`N`
inequality in `QuantitativeEffective.lean`. The real-analysis optimization
below has **not** been formalized in Lean. It is not a claim of publication
novelty.

Write

- `e(N) = # (E ∩ [0,N))`;
- `H_E(N) = # {n < N : sum of squares of positive integers ≤ n outside E is triangular}`;
- `Q(N) = N/(e(N)+1)`, for `N > 0`.

The original verified finite estimate is, for every `E`, `N` and `r ≥ 0`,

```text
7^r * H_E(N) ≤ 6^r * N + 7^r * 37^r * 2^(r*r) * (e(N)+1).
```

Dividing by `7^r N` gives

```text
H_E(N)/N ≤ (6/7)^r + (37^r * 2^(r*r))/Q(N).
```

## An explicit asymptotic rate

For `Q(N)>1` put `L = log Q(N)` (natural logarithm), and select

```text
r = floor(sqrt L).
```

Let `alpha = log(7/6) > 0`. Since `sqrt L - 1 < r ≤ sqrt L`,

```text
(6/7)^r ≤ (7/6) * exp(-alpha * sqrt L).
```

Moreover

```text
(37^r * 2^(r*r))/Q(N)
  ≤ exp(log(37) * sqrt L - (1-log(2)) * L).
```

Because `1-log(2)>0`, the second term is bounded by
`exp(-alpha*sqrt L)` for all sufficiently large `L`. Hence the
concrete asymptotic consequence is

```text
H_E(N)/N ≤ (13/6) * exp(-log(7/6) * sqrt(log Q(N)))
```

whenever `Q(N)` is sufficiently large.

The implicit threshold is absolute (independent of `E`). Therefore,
for any density-zero deletion set `E` (so `Q(N)→∞`),

```text
H_E(N) = O( N * exp(-log(7/6) * sqrt(log (N/(e(N)+1)))) ).
```

This is stronger than merely `H_E(N)=o(N)`, but weaker than the
previously proposed `exp(-c log(Q)/loglog(Q))` rate obtainable only with
a better bound on prime growth. The larger `37^r * 2^(r*r)` here is
a consequence of using Bertrand alone.

## Retained-sequence indexing

The separate Lean theorem `quantitative_index_bound_explicit` gives
for `N` with `keptNth E N < 2*N+2`:

```text
7^r * #index-hits below (N+1)
  ≤ 6^r*(2*N+2)
    + 7^r*37^r*2^(r*r)*(e(2*N+2)+1).
```

The survivor hypothesis holds eventually when `E` has density zero
(by `IndexGrowth.lean`). Consequently the same type of asymptotic
rate follows for hits counted by the position in the retained sequence,
with `Q(2N+2)` in place of `Q(N)` and harmless constant factors.

## Scope / limitations

- The upper bounds concern *triangular hits*, not their eventual
  disappearance; infinitely many rare hits are not excluded.
- No theorem about representations as five distinct squares is used.
- The finite inequalities are Lean-certified only after a successful
  CI run for the commit containing the corresponding declarations.
- The logarithmic optimization in this note is a mathematical
  derivation, **not** yet a Lean theorem. A future formalization would
  require elementary real exponential/logarithm estimates.

## Sharper finite modulus estimate

The separately compiled `QuantitativeSharper.lean` (verified in GitHub Actions run
`41236256862`, commit `4b65c88`) improves the purely elementary Bertrand bound to
`M_r ≤ 37^r 2^(r*(r-1)/2)`, by multiplying
`largePrime i ≤ 37·2^i` for `0≤i<r` instead of bounding all
factors by `37·2^r`. Thus the finite inequality can be sharpened to

```text
H_E(N)/N ≤ (6/7)^r + 37^r * 2^(r*(r-1)/2) / Q(N).
```

This keeps the same `exp(-c sqrt(log Q))` *type* of asymptotic decay,
but improves the finite-N constants; it does not prove the
`exp(-c log Q/loglog Q)` rate.

## Chebyshev prime-counting route: polynomial-size CRT modulus

The Lean-certified module `PrimePolynomialBound.lean` uses the explicit
Chebyshev lower bound already present in Mathlib and proves

```text
largePrime r ≤ 64*(r+50)^2.
```

The companion Lean-certified module `QuantitativePolynomial.lean` proves

```text
M_r ≤ (64*(r+50)^2)^r
H_E(N)/N ≤ (6/7)^r + (64*(r+50)^2)^r / Q(N).
```

**CI status:** both modules passed verification: `PrimePolynomialBound.lean`
on run `41236892361` (commit `67fa5d4`) and
`QuantitativePolynomial.lean` on run `41237410122` (commit `a0862e0`).
The final logarithmic optimization in this document remains a
mathematical derivation outside Lean; the finite-N polynomial-modulus
inequalities are kernel-certified. Unlike the Bertrand-only estimates above, their proof
uses Chebyshev's elementary prime-counting inequality (not the prime
number theorem).

### Mathematical derivation of the stronger asymptotic rate from the verified finite bound

Put `L = log Q(N)` and assume `L ≥ 256`. Choose
`r = floor(L/(8 log L))`. Then `r ≤ L`, `r+50 ≤ 2L`, and
`64*(r+50)^2 ≤ 256 L^2 ≤ L^3`. Therefore

```text
r * log(64*(r+50)^2) ≤ 3*r*log L ≤ 3*L/8.
```

Thus the perturbation term is at most `exp(-5L/8)`. Also, since
`r ≥ L/(8 log L)-1`, the sieve contraction obeys

```text
(6/7)^r ≤ (7/6)*exp(-(log(7/6)/8)*L/log L).
```

For `L ≥ 256`, `exp(-5L/8)` is bounded by the last exponential
without the `7/6` factor. Consequently the *mathematical*
corollary would be

```text
H_E(N)/N ≤ (13/6)*exp(-(log(7/6)/8)*log Q(N)/log(log Q(N))).
```

The optimization from the Lean-verified finite bound to the logarithmic
expression is not yet formalized in Lean. The numerical threshold and
constants above follow by elementary real inequalities, independent of
any unproved prime-counting conjecture.
