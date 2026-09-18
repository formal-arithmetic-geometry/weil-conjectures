/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# The morphism of `R`-modules given by an element

An element `m` of an `R`-module `M` is the same thing as an `R`-linear map `R ⟶ M`, namely
`r ↦ r • m`. This file records `LinearMap.toSpanSingleton` as a morphism of `ModuleCat R` out of
`ModuleCat.of R R`, together with the fact that composing it with a morphism `M ⟶ N` gives the
morphism attached to the image of `m`.

This is the mirror of `Mathlib/Algebra/Category/ModuleCat/EpiMono.lean` because that is the first
file in the `ModuleCat` hierarchy that has `LinearMap.toSpanSingleton` in scope.

## Main definitions

- `ModuleCat.toSpanSingletonHom`
-/

@[expose] public section

open CategoryTheory

universe u

namespace ModuleCat

variable {R : Type u} [Ring R]

/-- The morphism of `R`-modules `R ⟶ M` attached to an element `m` of `M`, namely `r ↦ r • m`.

Note that the source and the target have to be spelled out: `ModuleCat.ofHom` would elaborate its
target as `ModuleCat.of R ↥M`, which need not be syntactically `M`. -/
def toSpanSingletonHom (M : ModuleCat.{u} R) (m : M) : ModuleCat.of R R ⟶ M :=
  ConcreteCategory.ofHom (C := ModuleCat R) (X := ModuleCat.of R R) (Y := M)
    (LinearMap.toSpanSingleton R M m)

@[simp]
lemma toSpanSingletonHom_apply (M : ModuleCat.{u} R) (m : M) (r : R) :
    toSpanSingletonHom M m r = r • m :=
  LinearMap.toSpanSingleton_apply R M m r

variable {M N : ModuleCat.{u} R}

/-- Composing the morphism attached to `m` with `φ : M ⟶ N` gives the morphism attached to
`φ m`:

```
                        toSpanSingletonHom M m
  ModuleCat.of R R ---------------------------------> M
                   ╲                                  |
                    ╲  toSpanSingletonHom N (φ m)     | φ
                     ╲                                v
                      ──────────────────────────────> N
```
-/
@[reassoc]
lemma toSpanSingletonHom_comp (φ : M ⟶ N) (m : M) :
    toSpanSingletonHom M m ≫ φ = toSpanSingletonHom N (φ m) :=
  ModuleCat.hom_ext (LinearMap.comp_toSpanSingleton φ.hom m)

end ModuleCat
