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
