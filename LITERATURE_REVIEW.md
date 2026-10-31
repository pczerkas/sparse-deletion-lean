# Preliminary literature and novelty review — 2026-10-31

**Scope:** the precise theorem in this repository concerns
square-prefix sums over the positive integers **after deleting an
arbitrary set of natural density zero**. The quantitative extension
bounds the number of triangular hits in terms of the number of
deleted elements.

**This is a preliminary targeted search, NOT an exhaustive
state-of-the-art assessment or a claim of mathematical novelty.**

## Results checked in original scholarly or curated sources

### 1. Triangular square-pyramidal numbers, with NO deletions

R. Finkelstein and H. London, *On triangular numbers which are sums
of consecutive squares*, Journal of Number Theory **4** (1972),
455--462. DOI 10.1016/0022-314X(72)90036-4.

The classical equation
`P(n)=T(m)` has positive solutions only at
`n=1,5,6,85` (OEIS A053611). This establishes the finite case
`E=∅`, not the arbitrary sparse-deletion theorem. It does
not supply a uniform bound when the deleted set varies with n.

References:
- https://oeis.org/A053611
- https://doi.org/10.1016/0022-314X(72)90036-4
- https://mathworld.wolfram.com/SquarePyramidalNumber.html

### 2. Five *distinct* positive squares and thin deletions

P. T. Bateman, A. J. Hildebrand, G. B. Purdy,
*Sums of distinct squares*, Acta Arithmetica **67** (1994),
349--380. DOI not established by this review. Theorem 0
quotes a sharp threshold `N(5)=245`, and the introduction
explicitly credits Wright (1933) with the much stronger
ability to prescribe ratios of the five squared terms
for large integers.

E. M. Wright, *The representation of a number as a sum of five
or more squares*, Q. J. Math. (1933), 37--51.
DOI 10.1093/qmath/os-4.1.37.

This supplies the necessary external tool for our
**non-finiteness construction**, not a new upper bound on hits.

References:
- https://matwbn.icm.edu.pl/ksiazki/aa/aa67/aa6745.pdf
- https://academic.oup.com/qjmath/article-abstract/os-4/1/37/1524348

### 3. Prime partial sums: analogous *density zero*, different sequence

J. Cilleruelo and F. Luca, *On the sum of the first n primes*,
Quarterly Journal of Mathematics **59** (2008), 475--486,
DOI 10.1093/qmath/ham055.

Their Theorem 2 bounds the number of n for which the
sum of the first n primes is a **square**. In particular,
the paper proves a density-zero result, with explicit
quantitative savings. This is related as a methodological
analogy, but the underlying summands, target, and perturbation
conditions differ: they do **not** prove the theorem about
triangular sums of squares after deleting arbitrary
density-zero subsets of natural numbers.

References:
- https://academic.oup.com/qjmath/article-abstract/59/4/475/1623067
- https://mathoverflow.net/questions/448733/when-does-the-sum-of-squares-of-initial-primes-equal-a-triangular-number/516348

### 4. Original initial-prime-square problem remains distinct

MathOverflow question 448733 concerns triangular
`∑_{j≤n} p_j²` for consecutive primes. It is not a
corollary of our theorem because the set of integers that
must be deleted to leave only primes has density **one**,
not zero. The conjecture of finitely many such solutions
must not be presented as proved here.

Reference:
- https://mathoverflow.net/questions/448733/when-does-the-sum-of-squares-of-initial-primes-equal-a-triangular-number

### 5. Modular sieve arguments for density-zero exceptional sets

Modular restrictions and the Chinese remainder theorem are
classical tools for proving zero density of exceptional
arithmetic sets. For example Martin Sleziak's 2018
MathOverflow answer gives an elementary density-zero argument
with independent moduli for a different consecutive-sum
problem. This supports treating our *methodology* as
part of an existing classical toolkit, rather than claiming
the existence of a modular sieve or its CRT multiplication
as a novel idea.

Reference:
- https://mathoverflow.net/questions/312830/lower-density-of-numbers-not-summable-by-consecutive-integers

### 6. Elliptic curves and fixed shifts

For each fixed integer C, the equation
`P(n)-C=T(m)` gives a nonsingular elliptic curve
`3(2m+1)²=(2n+1)³-(2n+1)+3-24C`.
Siegel's theorem implies finitely many integral solutions
for each **fixed** C. This is a well-known kind of argument;
it is not by itself a uniform statement over infinitely
many shifts C. Our construction of infinitely many hits
uses infinitely many different shifts created by sparse
deletions.

Background:
- A. Baker, *The Diophantine Equation y²=ax³+bx²+cx+d*,
  J. London Math. Soc. (1968),
  https://doi.org/10.1112/jlms/s1-43.1.1
- https://mathworld.wolfram.com/SquarePyramidalNumber.html

## Preliminary conclusions

1. **Classical ingredients confirmed:** unperturbed
   square-pyramidal/triangular intersections, five distinct squares,
   and elliptic-curve finiteness.
2. **Analogous results confirmed:** density-zero exceptional
   sets for certain different partial-sum sequences.
3. **Exact sparse-deletion result:** this targeted review did
   not identify a published theorem with the same universal
   quantification over every deletion set of density zero.
   This is an **absence of a match in the sources checked**,
   not a proof of novelty.
4. **Quantitative rate:** no source checked here precisely
   states the same `H_E(N)` inequality or the
   `N exp(-c log Q/loglog Q)` corollary in our setting.
   The CRT, finite-field and prime-counting components
   are classical. A prior-art review by an analytic
   number theorist is necessary before claiming a new
   result or submitting a publication.

## High-priority follow-up search paths

- MathSciNet/Zentralblatt and arXiv: exact polynomial
  square-prefix and figurate-value intersections
  under sparse changes;
- quantitative bounds uniform in additive shifts for
  `y²=f(x)+c` with f cubic;
- sparse perturbation of generalized polygonal and
  triangular value sets, with an explicit exceptional
  index counting function.

The next paper should state the precise quantifiers
and indexing conventions; no claimed proof for the
initial-prime-square question should be inferred.
