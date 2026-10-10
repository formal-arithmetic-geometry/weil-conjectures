/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic

/-!
# Perfect pairings between zero modules

A pairing between two subsingleton modules is perfect.
-/

@[expose] public section

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- A pairing between two subsingleton modules is perfect: both duals are zero. -/
lemma isPerfPair_of_subsingleton [Subsingleton M] [Subsingleton N]
    (p : M →ₗ[R] N →ₗ[R] R) : p.IsPerfPair :=
  ⟨⟨Function.injective_of_subsingleton _, fun f ↦ ⟨0, LinearMap.ext fun y ↦ by
      rw [Subsingleton.elim y 0, map_zero, map_zero]⟩⟩,
    ⟨Function.injective_of_subsingleton _, fun f ↦ ⟨0, LinearMap.ext fun x ↦ by
      rw [Subsingleton.elim x 0, map_zero, map_zero]⟩⟩⟩

end LinearMap
