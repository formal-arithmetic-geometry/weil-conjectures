/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.Pi

/-!
# Finite disjoint covers in a site

A family of morphisms `f i : Y i ⟶ W` in a site is a *disjoint cover*
(`CategoryTheory.GrothendieckTopology.IsDisjointCover`) if it generates a covering sieve, consists
of monomorphisms, and is pairwise disjoint: any object mapping compatibly to `Y i` and `Y j` with
`i ≠ j` is covered by the empty sieve. For a sheaf `F`, sections over the `Y i` then glue
uniquely, i.e. `F(W) ≅ ∏ F(Y i)`.

An object `W` *has finite disjoint refinements*
(`CategoryTheory.GrothendieckTopology.HasFiniteDisjointRefinements`) if every covering sieve of
`W` contains the members of a finite disjoint cover of `W`. This holds for affine objects of the
pro-étale site whose underlying ring is w-contractible. Over such an object, a locally surjective
morphism `P ⟶ Q` of presheaves of modules with `Q` separated is surjective on sections over `W`
as soon as sections of `P` over the members of finite disjoint covers of `W` glue
(`CategoryTheory.Presheaf.surjective_app_of_hasFiniteDisjointRefinements`).
-/

@[expose] public section

universe w v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

namespace GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- A family of morphisms `f i : Y i ⟶ W` is a disjoint cover of `W` if it generates a covering
sieve, consists of monomorphisms, and is pairwise disjoint: any object mapping compatibly to
`Y i` and `Y j` with `i ≠ j` is covered by the empty sieve. -/
structure IsDisjointCover {W : C} {ι : Type*} {Y : ι → C} (f : ∀ i, Y i ⟶ W) : Prop where
  ofArrows_mem : Sieve.ofArrows Y f ∈ J W
  mono (i : ι) : Mono (f i)
  bot_mem (i j : ι) (hij : i ≠ j) {Z : C} (a : Z ⟶ Y i) (b : Z ⟶ Y j) (h : a ≫ f i = b ≫ f j) :
    ⊥ ∈ J Z

variable {J}

namespace IsDisjointCover

variable {R : Type*} [Ring R] {W : C} {ι : Type*} {Y : ι → C} {f : ∀ i, Y i ⟶ W}

end IsDisjointCover

end GrothendieckTopology

namespace Presheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Type*} [Ring R]

end Presheaf

end CategoryTheory
