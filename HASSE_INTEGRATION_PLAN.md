# Route to an unconditional Lean certificate for the Weil refinement
**Investigation date: 2026-11-01. Status: research and integration plan,
not yet an unconditional Lean proof.**

## Existing progress in this repository
- `WeilCharacterBridge.lean`: exact finite-field character-count
  identity and local 3/4 contraction given the character-sum upper bound.
- `WeilCubicRoots.lean`: cubic-root count bounded by three, unconditional.
- `WeilSingleHypothesis.lean`: isolates the sole missing assumption
  `CubicWeilCharacterUpper`, which is **not** declared as an axiom.
- `WeilConditionalLogRate.lean`: explicit value-index and retained-index
  log/loglog conclusions conditional on that assumption.
- Complete CI for the conditional chain: run 41292331952. The latest
  documentation-only CI (54e6713) also passed on 2026-11-01.

## External Lean project discovered
`CBirkbeck/AINTLIB` has a separate formalization of the Hasse
bound for elliptic curves over finite fields, with the exported
theorem reported in its public blueprint:

```lean
HasseWeil.WeilPairing.hasse_bound
  (W : WeierstrassCurve K)
  [WeierstrassCurve.IsElliptic W.toAffine]
  [Fintype W.toAffine.Point] :
  |(HasseWeil.pointCount W.toAffine : ℝ)
       - (Fintype.card K : ℝ) - 1|
    ≤ 2 * Real.sqrt (Fintype.card K : ℝ)
```

Links:
- https://github.com/CBirkbeck/AINTLIB
- https://cbirkbeck.github.io/AINTLIB-blueprints/hasseweil/The-Hasse-bound/
- https://reservoir.lean-lang.org/@CBirkbeck/AINTLIB

**Compatibility warning:** our pinned project is Lean 4.35.0 /
Mathlib v4.35.0, while AINTLIB's mid-2026 Hasse blueprint
used an earlier Lean/Mathlib revision, and its project
may use a newer release candidate. We have NOT added it to
`lakefile.toml`. We must first verify that the selected
AINTLIB revision builds with our toolchain (or work in an
isolated branch and port just the relevant library).

The blueprint's claim of a sorry-free theorem is a useful lead,
but any imported theorem needs a fresh local `#print axioms`
and CI build in *our* pinned environment. A separate repository's
CI does not certify our imports.

## Mathematical bridge for the nonsingular cubic

For each prime p≥37 and shift b, let f_b(x) be the degree-3
cubic in our `primeCubicPoly`, with nonzero leading
coefficient a∈F_p.

On the nonsingular locus, the affine curve

```text
y² = f_b(x)
```

is a smooth genus-one curve, and its projective closure has
one point at infinity. For the integer quadratic-character sum
S_b = Σ_x χ(f_b(x)) the exact point-counting identity is

```text
#E(F_p) = p + 1 + S_b.
```

The Hasse bound gives `|S_b|≤2√p` and hence the *upper*
inequality needed by `CubicWeilCharacterUpper`.

The Lean bridge therefore needs:
1. Construct a `WeierstrassCurve (ZMod p)` from the coefficients of
   `primeCubicPoly`, possibly after a suitable change of variables.
2. Show its `IsElliptic` instance from the discriminant hypothesis.
3. Prove its point count equals `p+1+S_b` using the already
   proven `WeilCharacterBridge.square_pass_character_identity`,
   adapted from the affine relation to projective points.
4. Invoke the AINTLIB `hasse_bound` theorem and extract the
   one-sided character estimate.

## Singular cubic: an elementary argument avoiding Hasse

Over a finite field of odd characteristic, if a cubic has a
double root u and a distinct simple root v, it factors as

```text
f(x) = a*(x-u)^2*(x-v), a ≠ 0, u ≠ v.
```

For the standard quadratic character χ (χ(0)=0),

```text
χ(f(x)) = χ(a)*χ(x-v),  x ≠ u;
χ(f(u)) = 0.
```

As `Σ_x χ(x-v)=0` by translation invariance and
nontriviality of χ,

```text
Σ_x χ(f(x)) = -χ(a)*χ(u-v), hence |S|=1.
```

If a cubic has a triple root, the same argument gives S=0.
For the specific family `x³-x+c` in characteristic >3,
**triple roots do not occur**, since the x² coefficient
is zero but the coefficient of x is -1. Therefore the
singular case is always double+simple, and satisfies
`S≤1≤2√p` without any deep theorem.

This split avoids trying to instantiate `IsElliptic` for
singular cubics, which would be invalid.

## Verification milestones
- [x] All conditional arithmetic, CRT, and log/loglog reduction
      certified in the original project.
- [x] Concrete root count ≤3 certified.
- [ ] Port/check the external Hasse theorem with our pinned Mathlib,
      including explicit axiom audit.
- [ ] Build the nonsingular point-counting bridge in Lean.
- [ ] Prove the singular factorization and character-sum identity in Lean.
- [ ] Combine both cases to discharge `CubicWeilCharacterUpper`.
- [ ] Re-run complete independent GitHub Actions; only then call the
      `log(4/3)/2` quantitative refinement *unconditionally
      Lean-certified*.

All these modules remain optional and isolated from the existing
unconditional elementary main theorem.
