module -- shake: keep-all

public import Mathlib.Tactic
public import Mathlib.Tactic.ComputeDegree

@[expose] public section

namespace SparseDeletion

open Polynomial

section CubicShape
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

noncomputable def cubicShape (a b c d : F) : Polynomial F :=
  C a * X ^ 3 + C b * X ^ 2 + C c * X + C d

end CubicShape
end SparseDeletion
