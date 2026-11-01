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

## Explicit discriminant of the proposed model

A direct symbolic expansion of the standard Weierstrass
discriminant for the five displayed coefficients gives

```text
Δ(W_b) = -(65536/729)*(15552*b² + 3888*b + 239).
```

This identity is valid over fields of characteristic
different from 2 and 3. In particular for `F=ZMod p`,
`p≥37`, the model is nonsingular **if and only if**
`15552*b²+3888*b+239 ≠ 0` in `F`.

This provides an explicit and decidable case split:
use Hasse when the quadratic expression is nonzero;
apply the double-root character-sum lemma if it is zero.

The algebraic expansion was checked symbolically, but is
**not yet a Lean theorem**. Do not infer that all fibers
are elliptic: those with vanishing discriminant must be
handled by the singular branch.

## Explicit factorization of every singular fiber

A further exact polynomial identity removes the need for an abstract
cubic-factorization theorem. Set

```text
q(b) = 15552*b² + 3888*b + 239,
u(b) = 18*b + 7/4,
v(b) = -36*b - 5.
```

Then **over any field of characteristic different from 2 and 3**,

```text
f_b(x) - (8/3)*(x-u(b))²*(x-v(b))
  = ((x-12*b-1)/6)*q(b).
```

This identity has been checked by symbolic polynomial expansion.
It is not yet a formal Lean theorem.

Since `Δ(W_b)=-(65536/729)*q(b)`, when the discriminant
vanishes in characteristic `p≥37`, the displayed identity
gives the explicit factorization

```text
f_b(x) = (8/3)*(x-u(b))²*(x-v(b)).
```

The **already Lean-certified** generic theorem
`quadraticCharFun_double_root_sum` therefore applies,
without using splitting fields, root multiplicities or
Hasse's theorem:

```text
Σ_x χ(f_b(x)) = -χ(8/3) * χ(u(b)-v(b)).
```

It follows mathematically that the absolute value of this
sum is ≤1. To make the entire singular branch
kernel-certified, the explicit algebraic factorization
and its connection to `primeCubicPoly` still need
a Lean proof. This is now a straightforward polynomial
identity, rather than a general algebraic-geometry task.

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
