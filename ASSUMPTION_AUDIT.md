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

The last successful full multi-target build was obtained **before**
`lake clean` during repository pruning. On 2026-10-30,
a clean rebuild and cache restoration on Kompik were interrupted
by practical build/cache/resource limits; the post-clean rebuild
has **not yet been certified**. Do not conflate that engineering
task with the mathematical assumption check.

Earlier compiled `#print axioms` results for all four certificate
targets reported only `propext`, `Classical.choice`,
and `Quot.sound`, never `sorryAx`. A fresh successful CI
build of the current commit is still recommended before
publication.

## 6. Conclusions and risks

- **Statement correspondence:** PASS — formal statement matches
  the density-zero sparse-deletion problem, including indexing.
- **Missing mathematical premises:** none identified in this review;
  the key uniform modular bound is proved, not merely assumed.
- **Main proof structure:** PASS by source audit and the recorded
  pre-clean successful build.
- **Fresh post-clean build:** NOT YET CONFIRMED.
- **Independently established novelty:** NOT ASSESSED. The
  `x³−x` exact value-set formula is classical.
- **Potential overclaims to avoid:** finite number of triangular
  hits; result on initial-prime squares; union of arbitrarily
  many zero-density deletion sets remaining density zero.

Any publication should identify the density-zero conclusion
precisely and include the pinned toolchain, independent build
log, exact statement, and `#print axioms` certificate.
