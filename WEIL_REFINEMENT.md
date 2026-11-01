# Optional Weil character-sum refinement — research note

**Status:** rigorous mathematical deduction from the classical Weil
bound, **not yet kernel-certified in Lean** and **NOT** imported
into the original elementary main proof.

The current Lean proof uses an elementary conic/image bound to
establish that at most `(6/7)p` residues pass a local test.
Exact computational experiments in `SIEVE_EXPERIMENT.md`
suggest that this bound can be substantially improved.

## 1. Uniform local fraction 3/4 from the Weil bound

For an odd prime `p≥37` and any `b∈F_p`, let

```text
f_b(x) = 8*(x*(x+1)*(2*x+1)/6 + b) + 1   in F_p[x].
```

The leading coefficient is `8/3`, nonzero because `p≥37`.
Thus `f_b` has degree exactly 3 and cannot be a scalar
multiple of a perfect square.

Let `χ` denote the quadratic character of `F_p`, with
`χ(0)=0`. The classical multiplicative Weil bound gives

```text
S_b = ∑_{x mod p} χ(f_b(x)),   |S_b| ≤ 2*sqrt(p).
```

This bound includes the singular case: the polynomial has odd
degree, hence it cannot be a constant times a square, and the
general character-sum theorem applies. An explicit singular
factorization would also give a stronger estimate.

Let `Z_b` be the number of distinct zeros of `f_b`; then
`0≤Z_b≤3`. The number `C_p(b)` of residue classes `x`
for which `f_b(x)` **is a square (including zero)** is

```text
C_p(b) = (p + S_b + Z_b)/2
       ≤ (p + 2*sqrt(p) + 3)/2.
```

For `p≥37`, `sqrt(p)≤p/6` and `6≤p/3`, so
`4*sqrt(p)+6≤p`. Consequently

```text
C_p(b) ≤ 3*p/4     for EVERY p≥37, EVERY b.
```

Unlike the finite experiment, this is a mathematical theorem
**using Weil's published character-sum bound**. This particular
application has not been formalized in the Lean repository.

## 2. CRT implication

Replace the local numerical bound
`7*C_p(b)≤6*p` by `4*C_p(b)≤3*p`
in the otherwise unchanged modular CRT sieve.

For arbitrary deletion sets `E` and finite N, the same
generic perturbation/counting argument yields

```text
4^r * H_E(N) ≤ 3^r * N + 4^r * M_r * (e(N)+1).
```

The existing, Lean-certified Chebyshev estimate

```text
M_r ≤ (16*(r+50)^2)^r
```

then gives

```text
H_E(N)/N ≤ (3/4)^r + (16*(r+50)^2)^r / Q(N),
Q(N) = N/(e(N)+1).
```

If `(64*(r+50)^2)^r ≤ Q(N)`, the sum is bounded by
`2*(3/4)^r`.

## 3. Explicit logarithmic consequence

With `L=log Q(N)≥2048`, choose `r=floor(L/(2 log L))`.
The elementary inequalities established in our sharper
log-choice analysis imply

```text
(112*(r+50)^2)^r ≤ exp(L)=Q(N),
```

which is stronger than the budget with coefficient 64.
The floor inequality yields

```text
H_E(N)/N ≤ (8/3)*exp(-(log(4/3)/2)*L/log L).
```

The exponential coefficient is

```text
c_Weil = log(4/3)/2 ≈ 0.14384.
```

Compare with the purely elementary 6/7 local sieve:
`c_elementary = log(7/6)/2 ≈ 0.07708`,
once that latest improvement passes CI.

An analogous bound transfers to retained-sequence indices
with the same survivor-growth condition as the existing theorem.

## Interpretation and formalization gap

- **Mathematical statement:** follows from a standard, unconditional
  theorem (Weil), not from a conjectural square-root estimate.
- **Formal verification:** the existing Lean repository does NOT
  contain a proof of the uniform character-sum estimate.
  Do not cite the 3/4 or improved log/loglog constant as
  *Lean-certified*.
- **Architecture:** leave this refinement as a separate research
  note rather than reintroducing older unverified conditional
  Hasse modules into the cleaned elementary proof tree.
- **Optimality:** even the stronger upper bound is not known
  to be sharp for arbitrary sparse deletion sets.

## Literature

- L. Babai, *Weil’s character sum estimate*, lecture notes,
  Theorem 4.3, University of Chicago,
  https://people.cs.uchicago.edu/~laci/HANDOUTS/weil.pdf
- T. Tao, *The Hardy–Littlewood–Chowla conjecture in the presence
  of a Siegel zero*, Journal of the London Mathematical Society
  (2022), section on Weil bounds for quadratic characters,
  https://doi.org/10.1112/jlms.12663
