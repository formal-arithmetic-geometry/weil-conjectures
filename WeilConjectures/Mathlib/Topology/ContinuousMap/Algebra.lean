/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra

/-!
# Precomposition as a ring homomorphism

Precomposition with a continuous map `f : C(α, β)` is a ring homomorphism
`C(β, R) →+* C(α, R)` for a topological ring `R`. This is the ring-valued analogue of
`ContinuousMap.compAddMonoidHom'`, which is used to build the presheaf of rings
`U ↦ C(U, R)` on the pro-étale site.
-/

@[expose] public section

namespace ContinuousMap

variable {α β R : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace R]
  [Ring R] [IsTopologicalRing R]

/-- Precomposition with `f : C(α, β)`, as a ring homomorphism `C(β, R) →+* C(α, R)`. -/
@[simps]
def compRightRingHom (f : C(α, β)) : C(β, R) →+* C(α, R) where
  toFun g := g.comp f
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
lemma compRightRingHom_id : compRightRingHom (R := R) (ContinuousMap.id α) = RingHom.id _ := rfl

lemma compRightRingHom_comp {γ : Type*} [TopologicalSpace γ] (f : C(α, β)) (g : C(β, γ)) :
    compRightRingHom (R := R) (g.comp f) =
      (compRightRingHom f).comp (compRightRingHom g) := rfl

end ContinuousMap
