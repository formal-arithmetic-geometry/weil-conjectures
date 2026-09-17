/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic

/-!
# The morphism of `R`-modules given by an element

An element `m` of an `R`-module `M` is the same thing as an `R`-linear map `R ⟶ M`, namely
`r ↦ r • m`. This file records that map as a morphism of `ModuleCat R` out of
`ModuleCat.of R R`, together with the fact that composing it with a morphism `M ⟶ N` gives the
morphism attached to the image of `m`.

Stating this generically matters: instantiating it at a concrete module — one obtained by a
restriction of scalars, say — is cheap, whereas redoing the element-level argument there makes
the kernel unfold the module structure.
-/

@[expose] public section

open CategoryTheory

universe u

namespace ModuleCat

variable {R : Type u} [Ring R] {M N : ModuleCat.{u} R}

/-- The morphism of `R`-modules `R ⟶ M` attached to an element `m` of `M`, namely `r ↦ r • m`.

The source and target are spelled out because `ModuleCat.ofHom` would elaborate its target as
`ModuleCat.of R ↥M`, which need not be syntactically `M`. -/
def toSpanSingletonHom (M : ModuleCat.{u} R) (m : M) : ModuleCat.of R R ⟶ M :=
  ConcreteCategory.ofHom (C := ModuleCat R) (X := ModuleCat.of R R) (Y := M)
    { toFun := fun r ↦ r • m
      map_add' := fun a b ↦ add_smul a b m
      map_smul' := fun a b ↦ mul_smul a b m }

@[simp]
lemma toSpanSingletonHom_apply (M : ModuleCat.{u} R) (m : M) (r : R) :
    toSpanSingletonHom M m r = r • m := rfl

/-- Composing the morphism attached to `m` with `φ : M ⟶ N` gives the morphism attached to
`φ m`. -/
@[reassoc]
lemma toSpanSingletonHom_comp (φ : M ⟶ N) (m : M) :
    toSpanSingletonHom M m ≫ φ = toSpanSingletonHom N (φ m) :=
  ModuleCat.hom_ext (LinearMap.ext fun r ↦ φ.hom.map_smul r m)

end ModuleCat
