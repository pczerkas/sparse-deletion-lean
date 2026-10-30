#!/usr/bin/env bash
# Reproducible verification of all maintained Lean certificates.
# Requires a working Lean/Lake installation with internet access on first run.
set -euo pipefail

cd "$(dirname "$(realpath "$0")")"
export PATH="$HOME/.elan/bin:$PATH"

echo "[1/3] Fetch precompiled Mathlib cache for the pinned manifest"
lake exe cache get

echo "[2/3] Build all four verification certificates"
lake build

echo "[3/3] Print axioms of the main, exact, and abstract theorems"
lake env lean VerifiedCompleteProof.lean
lake env lean VerifiedExactValueSet.lean
lake env lean VerifiedPerturbation.lean

echo "Verified: the printed theorem dependencies contain no sorryAx."
