/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.BilinearMap

/-!
# Bijectivity of bilinear maps under change of variables

A bilinear map `B : M →ₗ N →ₗ P` whose adjoint `M → (N →ₗ P)` is bijective keeps this property
after precomposing both variables with linear equivalences (`LinearMap.compl₁₂`). This is the
analogue, for an arbitrary codomain `P`, of `LinearMap.IsPerfPair.compl₁₂`.
-/

@[expose] public section

namespace LinearMap

variable {R M M' N N' P : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid M']
  [AddCommMonoid N] [AddCommMonoid N'] [AddCommMonoid P] [Module R M] [Module R M'] [Module R N]
  [Module R N'] [Module R P] (B : M →ₗ[R] N →ₗ[R] P) (e₁ : M' ≃ₗ[R] M) (e₂ : N' ≃ₗ[R] N)

/-- If the adjoint `M → (N →ₗ P)` of a bilinear map `B` is bijective, so is the adjoint of
`B.compl₁₂ e₁ e₂` for linear equivalences `e₁`, `e₂`. -/
theorem bijective_compl₁₂_of_equiv (h : Function.Bijective B) :
    Function.Bijective (B.compl₁₂ (e₁ : M' →ₗ[R] M) (e₂ : N' →ₗ[R] N)) :=
  ((LinearEquiv.congrLeft P R e₂).symm.bijective.comp h).comp e₁.bijective

/-- If the adjoint `N → (M →ₗ P)` of a bilinear map `B` is bijective, so is the adjoint of
`B.compl₁₂ e₁ e₂` for linear equivalences `e₁`, `e₂`. -/
theorem bijective_flip_compl₁₂_of_equiv (h : Function.Bijective B.flip) :
    Function.Bijective (B.compl₁₂ (e₁ : M' →ₗ[R] M) (e₂ : N' →ₗ[R] N)).flip :=
  ((LinearEquiv.congrLeft P R e₁).symm.bijective.comp h).comp e₂.bijective

end LinearMap
