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

variable {R M M' N N' P : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup M'] [AddCommGroup N]
  [AddCommGroup N'] [AddCommGroup P] [Module R M] [Module R M'] [Module R N] [Module R N']
  [Module R P] (B : M →ₗ[R] N →ₗ[R] P) (e₁ : M' ≃ₗ[R] M) (e₂ : N' ≃ₗ[R] N)

lemma bijective_compl₁₂ (h : Function.Bijective B) :
    Function.Bijective (B.compl₁₂ e₁.toLinearMap e₂.toLinearMap) :=
  ((LinearEquiv.congrLeft P R e₂).symm.bijective.comp h).comp e₁.bijective

lemma bijective_flip_compl₁₂ (h : Function.Bijective B.flip) :
    Function.Bijective (B.compl₁₂ e₁.toLinearMap e₂.toLinearMap).flip :=
  ((LinearEquiv.congrLeft P R e₁).symm.bijective.comp h).comp e₂.bijective

end LinearMap
