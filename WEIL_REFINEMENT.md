# Optional Weil character-sum refinement — research note

**Status (2026-11-01):** the abstract character-count identity,
the conditional local `3/4` lemma, the conditional CRT
reduction, and the concrete cubic-root bound are
**kernel-certified in Lean**. Full unconditional formalization
still needs the nontrivial Weil character-sum estimate.
The original elementary main proof remains unmodified.

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

## Verified Lean bridge and remaining input

The pinned project now includes the following verified files:

- `WeilCharacterBridge.lean`: the integer quadratic-character
  identity and a general finite-field proof of the `3/4`
  local contraction, given `Σχ≤2√p` and at most three roots.
- `WeilConditionalSieve.lean`: conditional CRT multiplication
  and both explicit finite-N counting bounds.
- `WeilCubicRoots.lean`: an unconditional Lean proof
  that the exact cubic family has no more than three roots.

GitHub Actions runs `41290984477`, `41291253800`,
and `41292056130` certify those files, with
`BUILD_EXIT=0` and only standard Lean axioms.
Two additional files have now **also passed** full CI
(run `41292331952`, commit `42256a8`, `BUILD_EXIT=0`,
no `sorryAx`, standard Lean axioms only):

- `WeilSingleHypothesis.lean`: the entire conditional
  theorem assumes only `CubicWeilCharacterUpper`.
- `WeilConditionalLogRate.lean`: the corresponding
  conditional `log(4/3)/2` log/loglog estimate, for both
  the value and retained-sequence indices.

**One missing deep theorem** remains: for every prime
`p≥37` in the sieve and every shift `b`, show in Lean
`Σ_x quadraticCharFun (ZMod p) (f_b(x)) ≤ 2√p`.
This is a special case of Weil's polynomial character-sum
theorem (Babai, Theorem 4.3, https://people.cs.uchicago.edu/~laci/HANDOUTS/weil.pdf).
Importing a hypothetical lemma as an axiom would not
constitute an unconditional Lean proof and is not our approach.

## Exact final conditional estimate certified by Lean

For `N>0` and `L=log(N/(e(N)+1))≥2048`, the
new theorem `quantitative_weil_value_loglog_bound` proves

```text
CubicWeilCharacterUpper →
  H_E(N)/N ≤ (8/3) * exp(-(log(4/3)/2) * L/log L).
```

The companion `quantitative_weil_index_loglog_bound`
handles retained-sequence indices with its original explicit
survivor-growth hypothesis. These implications are complete
Lean proofs (run `41292331952`). They DO NOT establish
`CubicWeilCharacterUpper` without an additional proof of
Weil's deep character-sum theorem. The existing unconditional
elementary `log(7/6)/2` bound is unaffected.
