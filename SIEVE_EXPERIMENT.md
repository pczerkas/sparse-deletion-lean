# Finite-field sieve experiments (p ≤ 500)

**Status:** exact finite computations in Python; **not a
formal uniform theorem**. Reproduce with
`python3 explore_sieve_residues.py --max-prime 500`.

For every prime `p≥37`, for each shift `b∈F_p` we count

```text
C_p(b) = #{x mod p : 8*(P(x)+b)+1 is a quadratic residue mod p},
P(x)=x*(x+1)*(2*x+1)/6.
```

This agrees with the local predicate used in
`PrimeSquarePass.lean` because `6` is invertible modulo p.
We tested every shift for every prime from 37 through 500,
using only exact modular arithmetic.

| p | max over b of C_p(b) | max ratio |
|---:|---:|---:|
| 37 | 24 | 0.648649 |
| 41 | 27 | 0.658537 |
| 43 | 29 | 0.674419 |
| 47 | 30 | 0.638298 |
| 53 | 35 | 0.660377 |
| 59 | 37 | 0.627119 |
| 61 | 38 | 0.622951 |
| 67 | 42 | 0.626866 |
| 71 | 44 | 0.619718 |
| 73 | 45 | 0.616438 |
| 79 | 49 | 0.620253 |
| 83 | 51 | 0.614458 |
| 89 | 53 | 0.595506 |
| 97 | 59 | 0.608247 |
| 101 | 60 | 0.594059 |
| 103 | 62 | 0.601942 |
| 107 | 65 | 0.607477 |

**Worst case over all 84 primes** `p∈[37,500]`:
`29/43≈0.674419` at `p=43`, `b=5`.

In particular, the numerical data satisfy the much stronger
candidate bound `C_p(b)≤(3/4)p` for all tested primes,
compared to the **proved uniform estimate**
`C_p(b)≤(6/7)p` used in our Lean CRT argument.

**Important:** this does NOT prove the ratio `3/4` for all
primes. The existing Lean proof uses only an elementary
lower bound on the cardinality of the image of a cubic
polynomial plus a count of quadratic residues, yielding
an asymptotic elementary upper bound near `5/6`.
An actual uniform improvement toward `3/4` would
require a new argument, possibly from elliptic character
sums/Weil-type bounds, or a stronger elementary
structural counting lemma.

With a universally proven contraction `3/4`, the
exponential coefficient in the log/loglog bound could be
larger, but that improvement is **not yet proved** and
must not be described as a Lean result.
