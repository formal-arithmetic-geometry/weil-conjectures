/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# The top exterior power of a free module

Let `M` be a free `R`-module with basis `b` indexed by `Fin r`. The top exterior power
`⋀[R]^r M` is free of rank one on `b₁ ∧ ⋯ ∧ b_r`, and `v₁ ∧ ⋯ ∧ v_r = det_b(v) • b₁ ∧ ⋯ ∧ b_r`.

## Main statements

- `AlternatingMap.apply_eq_det_smul`: an alternating map `f` in as many variables as the rank
  satisfies `f v = det_b(v) • f b`.
- `exteriorPower.ιMulti_eq_det_smul`: `v₁ ∧ ⋯ ∧ v_r = det_b(v) • b₁ ∧ ⋯ ∧ b_r`.
- `exteriorPower.bijective_smul_ιMulti_basis`: `a ↦ a • b₁ ∧ ⋯ ∧ b_r` is a bijection
  `R ≃ ⋀[R]^r M`.
-/

@[expose] public section

open Module

variable {R M N ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

namespace exteriorPower

variable {r : ℕ}

end exteriorPower
