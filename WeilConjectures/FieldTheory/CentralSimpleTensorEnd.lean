/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.BrauerGroup.Defs
public import Mathlib.Algebra.Azumaya.Defs
import WeilConjectures.FieldTheory.CentralSimpleTensorInjective
import Mathlib.LinearAlgebra.Basis.MulOpposite
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The enveloping algebra of a central simple algebra

For a finite-dimensional central simple algebra `A` over `K`, left and right multiplication
`a ⊗ op(b) ↦ (v ↦ a * v * b)` is an isomorphism `A ⊗ Aᵐᵒᵖ ≅ End_K(A)`.

## Implementation details

The map is injective since `A ⊗ Aᵐᵒᵖ` is simple, and both sides have dimension
`(dim_K A)^2`.

## References

* Stacks Project, Tag 074I, Lemma 11.4.10.
-/

@[expose] public section

universe u

namespace Field

/-- Left and right multiplication identify the enveloping algebra of a finite-dimensional
central simple algebra with its linear endomorphisms. -/
theorem centralSimple_mulLeftRight_bijective (K : Type u) [Field K] (A : CSA.{u, u} K) :
    Function.Bijective (AlgHom.mulLeftRight K A) := by
  have hi := centralSimple_mulLeftRight_injective K A
  refine ⟨hi, ?_⟩
  apply (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (f := (AlgHom.mulLeftRight K A).toLinearMap) ?_).mp hi
  rw [Module.finrank_tensorProduct, Module.finrank_linearMap, MulOpposite.finrank]

end Field
