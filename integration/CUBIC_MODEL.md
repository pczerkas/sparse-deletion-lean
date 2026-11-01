# Explicit Weierstrass model for our cubic — bridge design

**Status:** algebraically checked on paper, not yet an AINTLIB Lean theorem.
No additional axioms or changes to the original Lean 4.35 proof.

Let `p ≥ 37` be prime, `F = ZMod p`, and `b ∈ F`.
Our local triangular-square condition is that the cubic

```text
f_b(x) = 8 * (x*(x+1)*(2*x+1)/6 + b) + 1
       = (8/3)*x^3 + 4*x^2 + (4/3)*x + (8*b+1)
```

is a quadratic residue, including zero, in `F`.

Set `a = 8/3`, a nonzero element of `F`, and
change variables `X=a*x`, `Y=a*y`. Then

```text
y^2 = f_b(x)   ↔   Y^2 = g_b(X)

g_b(X) = X^3 + 4*X^2 + (32/9)*X + (64/9)*(8*b+1).
```

The identity `g_b(a*x)=a^2*f_b(x)` holds exactly.
Hence the change of coordinates is a bijection between the
solutions of the two affine equations.

Represent `g_b` as a Weierstrass equation with coefficients:

```text
a1=0, a2=4, a3=0, a4=32/9, a6=(64/9)*(8*b+1).
```

If the cubic is square-free, this is a nonsingular elliptic
curve. It has one projective point at infinity. Therefore

```text
#E_b(F) = 1 + ∑_X #{Y : Y² = g_b(X)}
        = p+1+∑_X χ(g_b(X))
        = p+1+∑_x χ(f_b(x)).
```

The last equality uses that multiplication by `a` permutes
`F` and `χ(a²)=1` since `a≠0`.

The AINTLIB `hasse_bound` gives

```text
|∑_x χ(f_b(x))| ≤ 2*sqrt(p)
```

for non-singular fibers once the field-theoretic equation
and point count are formally identified.

For singular fibers the derivative of the cubic is a
separable quadratic (characteristic p≥37), so triple roots
cannot occur. A singular cubic factors as
`a*(x-u)^2*(x-v)` with `u≠v`. The already certified
`WeilSingularPointwise.lean` yields

```text
∑_x χ(f_b(x)) = -χ(a)*χ(u-v)
```

using the standard Mathlib `quadraticChar_sum_zero`.
In particular its absolute value is at most 1.

## Lean implementation milestones

1. Instantiate the concrete `WeierstrassCurve (ZMod p)`
   with the coefficients above and prove the coordinate
   identity `g_b(a*x)=a²*f_b(x)`.
2. Supply its `IsElliptic` instance for square-free fibers.
3. Bridge `HasseWeil.pointCount` to the finite-field character
   sum, including the point at infinity.
4. Formalize the singular double-root decomposition and
   sum of characters.
5. Combine cases to discharge `CubicWeilCharacterUpper`
   in the existing conditional quantitative chain.

The independent GitHub Action first checks that AINTLIB can
be imported without `sorryAx` in its native Lean 4.36 workspace.
That smoke test alone **does not** fulfill milestones 1–5.
