/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Trace

/-!
# The trace of a composition operator on a space of linear maps

For endomorphisms `h` of `M` and `g` of `N`, the operator `φ ↦ g ∘ φ ∘ h` on `M →ₗ N` has
trace `tr g * tr h`: under `M →ₗ N ≅ M^* ⊗ N` it is `h^* ⊗ g`.
-/

@[expose] public section

namespace LinearMap

open TensorProduct

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] [Module.Free R M] [Module.Finite R M] [Module.Free R N] [Module.Finite R N]

/-- The trace of the operator `φ ↦ g ∘ φ ∘ h` on `M →ₗ[R] N` is `tr g * tr h`. -/
theorem trace_llcomp_comp_lcomp (g : N →ₗ[R] N) (h : M →ₗ[R] M) :
    trace R (M →ₗ[R] N) (llcomp R M N N g ∘ₗ lcomp R N h) = trace R N g * trace R M h := by
  set e := dualTensorHomEquiv R M N
  have key : llcomp R M N N g ∘ₗ lcomp R N h =
      e.conj (TensorProduct.map (Module.Dual.transpose (R := R) h) g) := by
    rw [LinearEquiv.conj_apply]
    refine (LinearEquiv.eq_comp_toLinearMap_symm _ _).2 ?_
    refine TensorProduct.ext' fun f n ↦ LinearMap.ext fun x ↦ ?_
    simp [e, dualTensorHomEquiv, dualTensorHom_apply, Module.Dual.transpose_apply]
  rw [key, trace_conj', trace_tensorProduct', trace_transpose', mul_comm]

end LinearMap
