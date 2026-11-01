# GitHub-only AINTLIB integration spike

This integration is isolated from the Lean 4.35 / Mathlib v4.35
proofs in the repository root. **Kompik is used only for lightweight
text edits, Git branching and pushing.** All Lean, Lake, Mathlib
downloads and builds run on GitHub-hosted Actions runners.

## Why an isolated pipeline?

- Original proof toolchain: Lean 4.35.0, pinned Mathlib.
- AINTLIB upstream commit:
  `8dafefa0f1f45af275e66007cfc6c28cbcd97089`.
- Upstream toolchain: `leanprover/lean4:v4.36.0-rc2`.
- Upstream Mathlib:
  `a2f96aabcf72be9e18bece4b5c7c54fcc0c029f4`.
- The upstream capstone is
  `HasseWeil.WeilPairing.hasse_bound`, from
  `HasseWeil.HasseBound`. Upstream's
  `tests/ModuleSystemTests.lean` checks it with
  `#print axioms` and reports only the standard Lean axioms.

We do not attempt to import mixed-version `.olean` files.
Instead, the new GitHub workflow checks out and builds the
exact upstream revision in its own workspace with its own
toolchain, then type-checks our
`integration/AINTLIBSmoke.lean` as a **downstream client**
inside the AINTLIB environment.

## What the smoke test establishes

`hasse_import_available` shows that our independent client
can call the genuine Hasse theorem. The lemma
`abs_character_sum_le_of_point_count` formally derives the
character-sum bound from a supplied curve point-count identity.
This is a genuine mathematical implication, but the equality
for our **specific cubic** is deliberately still a hypothesis.

The test includes exact `#guard_msgs` axiom checks for the
upstream theorem and our bridge; success must be confirmed
by its **own GitHub Actions run**, not inferred from the
upstream repository alone.

## What the smoke test does NOT establish

1. It does not prove that `PrimeCubicPoly` is represented by
   an elliptic Weierstrass curve.
2. It does not prove
   `#E(F_p) = p+1+∑_x χ(f_b(x))` for the corresponding curve.
3. It does not handle singular cubic fibers, which need an
   independent elementary double-root argument.
4. It does not discharge `CubicWeilCharacterUpper` or
   claim that the stronger 3/4 sieve is unconditional in Lean.
5. It does not upgrade the existing root project to Lean 4.36.

## Next planned milestone

First obtain a green GitHub Action for the pinned upstream
Hasse import. Then develop a curve/character-sum bridge in
the same upstream-compatible environment, while retaining
the original elementary proof as a separately certified
lean-4.35 result.

External source:
https://github.com/CBirkbeck/AINTLIB/tree/8dafefa0f1f45af275e66007cfc6c28cbcd97089

## First GitHub Actions result

GitHub Actions run `41295856674` **successfully built the pinned
AINTLIB Hasse capstone** but failed a *message-format assertion* in
our downstream smoke test. The Lean theorem statements and the
point-count-to-character-sum implication compiled; the asserted
message for our wrapper used a public name but the declaration was
elaborated as private. Commit `65b2b1a` added `@[expose] public section`, but run
`41297232029` revealed that the exported section requires
an explicit public Mathlib import: otherwise `Field` is not visible.
Both builds of the upstream Hasse capstone succeeded, but
neither downstream run passed. The subsequent test now uses
`public import Mathlib` and `public import HasseWeil.HasseBound`
before exporting the wrapper.

The next integration round includes `AINTLIBCubicModel.lean`:
a concrete `WeierstrassCurve` model and an algebraic identity
for the triangular-prefix cubic. It is tested in
AINTLIB's own GitHub-hosted workspace; no local `lake`
or Mathlib processing is performed on Kompik.

## Status after the first green isolated AINTLIB run

GitHub Actions run `41300991573` (commit `1ea21f9`) succeeded.
It certified the upstream Hasse import, downstream Hasse implication,
the exact change of variables, discriminant identity, and the
concrete Hasse corollary for nonsingular fibers, without `sorryAx`.
This does **not** yet prove the cubic character-sum bound.

The next module, `integration/AINTLIBPointCount.lean`, uses Mathlib's
`WeierstrassCurve.Affine.pointEquiv` to identify the elliptic point
count with one point at infinity plus the number of affine solutions.
Its own GitHub Actions verification must pass before this statement
is described as kernel-certified.

The remaining work is counting the quadratic roots in each fiber,
transporting them through the rescaling, and handling singular fibers.

## Singular-fiber factorization

The earlier `AINTLIBSingularSum.lean` certifies the quadratic-character
sum for a cubic whose factorization `a*(x-u)^2*(x-v)` is already given.
The new `AINTLIBSingularFactor.lean` attempts to prove the **missing
factorization for our actual cubic**, whenever the discriminant
factor `15552*b²+3888*b+239` vanishes.

A concrete polynomial identity is used (valid for fields where 2 and 3
are invertible), rather than choosing a root in an algebraic closure:

```text
t = 3*(24*b+3)/2
u = (t-1)/2
v = (-2*t-1)/2
f_b(x) - (8/3)*(x-u)^2*(x-v)
  = (x-12*b-1)*(15552*b²+3888*b+239)/6.
```

This identity was independently checked with exact symbolic algebra.
The Lean implementation **passed** GitHub Actions run
`41316791670` (commit `98f5a6f`) with the complete workflow green.
The exact factorization and character-sum identity use only standard
Lean axioms, with no `sorryAx`. No external character-sum conjecture
is involved in the singular case.

The stronger uniform cubic character bound will still require
a separate theorem that splits on whether the discriminant vanishes,
and a final bridge back to the original Lean 4.35 project.

## Full cubic-character estimate (new downstream module)

The optional `AINTLIBAllFibers.lean` combines the two cases via the
explicit discriminant expression. The singular case is reduced to a
sum of absolute value ≤1; the nonsingular case invokes our already
certified AINTLIB Hasse specialization. The outcome is the uniform
bound `|sum_x quadraticCharFun(f_b(x))| ≤ 2*sqrt(card F)`, including
both singular and nonsingular fibers.

**Status:** the combined theorem passed GitHub Actions run
`41317306525` (commit `a6c2e44`, SUCCESS). The singular and
nonsingular cases are therefore verified together in the isolated
AINTLIB Lean 4.36 workspace. They have not yet been integrated back
into the original Lean 4.35 `CubicWeilCharacterUpper` statement.

## Uniform prime-modulus specialization (new, CI pending)

`AINTLIBZModWeil.lean` specializes the combined theorem to
`ZMod p`, under exactly the natural assumptions `p.Prime` and
`37≤p`, and eliminates the curve-point `Fintype` hypothesis by
constructing it from the canonical nonsingular-point equivalence.
It aims to prove for every shift `b:ZMod p`:

```text
((∑ x : ZMod p, quadraticCharFun (ZMod p) (f_b(x)) : ℤ) : ℝ)
  ≤ 2 * sqrt(p).
```

The theorem matches the mathematical content of the remaining
`CubicWeilCharacterUpper` premise, modulo the exact polynomial
normalization and the separate Lean compiler version. This new
specialization needs its own successful CI run and is **not yet**
verified.

## Matching the old project's polynomial coefficients (new, CI pending)

The original Lean 4.35 theorem uses the polynomial
`primeCubicPoly p b`, whose coefficients are
`16/6, 24/6, 8/6, 8b+1` in `ZMod p`.
The new `AINTLIBPrimePolyBridge.lean` **reproduces that definition**
inside the Lean 4.36 AINTLIB workspace, proves the polynomial-evaluation
identity, and applies the prime-modulus Hasse/Weil estimate.

This will establish the exact *mathematical statement* of the
character-sum input required by `CubicWeilCharacterUpper`.
It still does not permit importing a Lean 4.36 certificate directly
into the pinned Lean 4.35 proof; solving that compatibility problem
remains a separate task. The new file and its declared axioms have
not yet passed GitHub Actions.
