# Joint AINTLIB + original Lean proof compatibility test

**Status:** experimental GitHub Actions test. The currently certified
AINTLIB-side theorem is independent of this joint build.

The workflow `.github/workflows/aintlib-root-compat.yml` exercises
source-level portability without changing the committed original
toolchain or root `lakefile.toml`.

In a disposable GitHub-hosted runner only:

1. Checkout this integration branch and the pinned AINTLIB
   commit `8dafefa0f1f45af275e66007cfc6c28cbcd97089`.
2. Install the **AINTLIB** Lean `4.36.0-rc2` toolchain and
   the matching Mathlib cache.
3. Copy all **unchanged** root `*.lean` source files into
   `aintlib/compat-src`; append temporary Lean library entries
   to AINTLIB's runner-local `lakefile.toml`. No source files
   are modified in either repository.
4. Compile the original `PrimeCubicPoly` module and then
   `WeilConditionalLogRate` under Lean 4.36.
5. Import the AINTLIB-side verified cubic bridge, prove the
   original `primeCubicPoly` definition equals the recreated
   `matchingPrimeCubicPoly` by definitional equality, and
   discharge **the actual original proposition**
   `SparseDeletion.CubicWeilCharacterUpper`.
6. Apply the already verified conditional log/loglog corollary
   to produce the unconditional strengthened result with
   exponential constant `log(4/3)/2`.
7. Print axioms and reject the run if `sorryAx` occurs.

The new downstream file is
`integration/RootWeilDischarge.lean`.

**Important:** this is a migration/compatibility **test**.
Until the GitHub Actions run succeeds, claims in steps 4–7 above
are targets, **not verified results**. The original Lean 4.35
`main` proof remains intact regardless of the outcome.
