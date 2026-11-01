# Joint AINTLIB + original Lean proof compatibility test

**Status:** **SUCCESS — kernel-certified** in GitHub Actions run
[41320828513](https://github.com/pczerkas/sparse-deletion-lean/actions/runs/41320828513)
at commit `733a9f6`. The full original conditional proof and the
AINTLIB Hasse theorem were built together under Lean 4.36.0-rc2.

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

**Verified result:** every stage of this joint-build test passed,
including both unconditional final log/loglog theorems and the exact
original `CubicWeilCharacterUpper` proposition. Each of the four
printed declarations depends only on `propext`, `Classical.choice`,
and `Quot.sound`; no `sorryAx` appears. The original Lean 4.35
`main` proof remains intact. The stronger theorem is certified
in the **joint Lean 4.36 workspace**, not in the unmodified
Lean 4.35 default package.
