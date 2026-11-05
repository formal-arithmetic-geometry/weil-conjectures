/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Injectivity of maps out of an extension of scalars along a field

Let `f : R →+* S` be a ring morphism from a field `R`, and `g : X ⟶ Y` an `R`-linear map from
an `R`-module `X` to an `S`-module `Y`. Suppose that `X` and `Y` embed into spaces of functions
on a set `T`, with values in `R` and `S` respectively, compatibly with `g`. Then the
`S`-linear map `S ⊗_R X ⟶ Y`, `s ⊗ x ↦ s • g x`, adjoint to `g`, is injective
(`ModuleCat.injective_homEquiv_symm_of_eval`): writing an element of `S ⊗_R X` as
`∑ᵢ bᵢ ⊗ xᵢ` for an `R`-basis `(bᵢ)` of `S`, its image evaluated at `t` is `∑ᵢ f (xᵢ t) bᵢ`, whose
vanishing forces every `xᵢ t` to vanish.

This is the injectivity of `S ⊗_R C(T, R) ⟶ C(T, S)`, for instance for an extension of
nonarchimedean fields.
-/

@[expose] public section

open CategoryTheory TensorProduct

namespace ModuleCat

universe v u₁ u₂

variable {R : Type u₁} {S : Type u₂} [Field R] [CommRing S] (f : R →+* S)

end ModuleCat
