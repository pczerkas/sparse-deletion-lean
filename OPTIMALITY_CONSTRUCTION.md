# Sparse deletions with infinitely many triangular square-prefix hits

**Status:** mathematical construction based on two published theorems;
**not yet formalized in Lean**. This note demonstrates that the
zero-density conclusion generally cannot be improved to finitely many
triangular hits, even when the deletion counting function grows
arbitrarily slowly. It does **not** show that the current quantitative
upper bound is sharp.

## Precise construction statement

For every nondecreasing function `g : ℕ → ℝ₊` tending to infinity,
one can choose a set `E ⊆ ℕ_{>0}` such that:

1. `#(E ∩ [1,N]) ≤ g(N)` for every sufficiently large `N`;
2. infinitely many indices `n` satisfy
   `∑_{1≤k≤n, k∉E} k² = m(m+1)/2` for some integer `m≥0`.

In particular, `E` has density zero and its count can grow as
slowly as an arbitrarily specified unbounded function.

The argument assumes the following **established** theorems:

- E. M. Wright (1933): for every sufficiently large integer `D`,
  there are representations `D=a₁²+⋯+a₅²` with five distinct
  positive roots and with all ratios `a_i²/D` constrained to
  prescribed positive values (within fixed tolerances). A
  consequence is that for **every fixed B**, all sufficiently
  large `D` have five distinct roots `a_i>B`.
  This strengthened form is reported explicitly in the introduction
  to Bateman--Hildebrand--Purdy (1994).
- Siegel's theorem: for every nonsingular elliptic curve over the
  rationals, there are only finitely many integral points in any
  fixed integral affine model. It applies to the shifted cubic
  curves below.

## Step 1: unbounded triangular residual

Define the square-pyramidal sum and triangular numbers by

```text
P(n) = n(n+1)(2n+1)/6, T(m)=m(m+1)/2.
```

Fix an integer `C≥0` and take `n` large enough that
`P(n)-C≥0`. Let `m(n)` be the largest nonnegative integer
with `T(m(n))≤P(n)-C`. Put

```text
D_C(n) = P(n)-C-T(m(n)).
```

Then `0 ≤ D_C(n) < m(n)+1 = O(n^(3/2))`. Moreover:

**Lemma:** `D_C(n)→∞` as `n→∞`.

Proof: Otherwise, a bounded nonnegative integer `d` occurs as
`D_C(n)` for infinitely many distinct `n`. Consequently
`P(n)-C-d=T(m)` has infinitely many integer solutions. With
`x=2n+1, y=2m+1`, this becomes

```text
3*y² = x³-x+3-24*(C+d).
```

The cubic `x³-x+a`, where `a=3-24*(C+d)` is an integer, has
discriminant `4-27*a² ≠0`, hence the curve is nonsingular of
genus one. By Siegel, it has only finitely many integral points.
Contradiction.

## Step 2: five-square surgery and preservation

Suppose finite deletions `E_j` have already been selected, and
all lie below the most recent preserved hit `n_{j-1}`.
Put `C_j=∑_{k∈E_j}k²`.

Given any large cutoff `B_j≥n_{j-1}`, the previous lemma lets
us choose an arbitrarily large `n_j` with

```text
D = D_{C_j}(n_j) sufficiently large.
```

Use Wright's theorem to write

```text
D = a₁² + a₂² + a₃² + a₄² + a₅²,
```

with distinct roots **all greater than `B_j`**.

Because `D=O(n_j^(3/2))`, every root satisfies
`a_i≤√D=O(n_j^(3/4))<n_j` when `n_j` is large.
Define `E_{j+1}=E_j∪{a₁,...,a₅}`. Then

```text
P(n_j)-∑_{k∈E_{j+1}}k²
= P(n_j)-C_j-D = T(m(n_j)).
```

Since all new deletions exceed `n_{j-1}`, the earlier hits are
unchanged.

To enforce a prescribed sparse counting bound, let `L_j` be
large enough that `g(N)≥5j` for all `N≥L_j`.
Choose `B_j≥max(n_{j-1},L_j)`; hence all newly added
deletions occur past the point at which `g(N)` allows the
enlarged cardinality `5j`. The construction can be
continued indefinitely.

The hits transfer to positions in the *retained enumeration*,
because `n_j` is not removed and the number of retained terms
up to `n_j` grows to infinity.

## An exact, two-stage numerical example

Initial deletion set:

```text
E₁ = {1,2,6,9,20}
sum_{k∈E₁}k² = 522
P(87)=223300
P(87)-522 = 222778 = T(667).
```

Second set of new deletions (all strictly larger than 87):

```text
A₂={88,89,94,180,276}
sum_{k∈A₂}k² = 133077
E₂=E₁ ∪ A₂,  #E₂=10
P(3500)=14297792250
P(3500)-522-133077=14297658651=T(169101).
```

The original hit at 87 is preserved, since all new deleted
integers exceed 87. These identities have been verified with
exact integer arithmetic, not as an asymptotic argument.

## What this proves / does NOT prove

- Given Wright and Siegel, the construction proves the
  *qualitative non-improvability to finiteness*: a deletion set
  can be arbitrarily sparse and still have infinitely many hits.
- It does **not** show that the specific upper rate
  `N exp(-c log Q/loglog Q)` is best possible. Matching lower
  bounds on `H_E(N)` in terms of `e(N)` remain an open
  problem for this project.
- The construction is not Lean-certified: formalizing the
  full analytic number-theory inputs (Wright + Siegel) would
  be an independent major project.

## Sources

- Bateman, Hildebrand, Purdy, *Sums of distinct squares*,
  Acta Arithmetica 67 (1994), 349--380:
  https://matwbn.icm.edu.pl/ksiazki/aa/aa67/aa6745.pdf
- E. M. Wright, *The representation of a number as a sum of five
  or more squares*, Quarterly Journal of Mathematics (1933),
  37--51, DOI: 10.1093/qmath/os-4.1.37.
- A. Baker, *The Diophantine Equation y²=ax³+bx²+cx+d*,
  J. London Math. Soc. (1968), DOI: 10.1112/jlms/s1-43.1.1
  (related background on integral points).
