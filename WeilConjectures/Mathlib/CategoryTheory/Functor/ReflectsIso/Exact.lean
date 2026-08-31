/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import WeilConjectures.Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly

/-!
# Exactness hypotheses for a pair of functors which jointly reflects isomorphisms

`CategoryTheory.JointlyReflectIsomorphisms.isZero_iff`, `.exact_iff` and `.shortExact_iff`
ask for the target categories `D i` to be abelian and for the functors `F i` to be exact.
This file discharges those hypotheses for the two-element family
`CategoryTheory.pairFunctor` of a pair of exact functors between abelian categories, so that
the three criteria apply to a pair of functors out of the box.

-/

@[expose] public section

universe v₁ v u₁ u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] {D₁ D₂ : Type u₁} [Category.{v₁} D₁] [Category.{v₁} D₂]

/-- The two-element family of categories `fun b ↦ cond b D₁ D₂` is abelian.

Like `CategoryTheory.instCategoryCond` this is `scoped`, so that it is not tried on
unrelated goals whose head happens to be `cond`. -/
scoped instance instAbelianCond [Abelian D₁] [Abelian D₂] (b : Bool) :
    Abelian (cond b D₁ D₂) :=
  Bool.rec (motive := fun b ↦ Abelian (cond b D₁ D₂)) ‹Abelian D₂› ‹Abelian D₁› b

variable (F₁ : C ⥤ D₁) (F₂ : C ⥤ D₂)

/-- A pair of left exact functors is objectwise left exact. -/
instance preservesFiniteLimits_pairFunctor [PreservesFiniteLimits F₁] [PreservesFiniteLimits F₂]
    (b : Bool) : PreservesFiniteLimits (pairFunctor F₁ F₂ b) :=
  Bool.rec (motive := fun b ↦ PreservesFiniteLimits (pairFunctor F₁ F₂ b))
    ‹PreservesFiniteLimits F₂› ‹PreservesFiniteLimits F₁› b

/-- A pair of right exact functors is objectwise right exact. -/
instance preservesFiniteColimits_pairFunctor [PreservesFiniteColimits F₁]
    [PreservesFiniteColimits F₂] (b : Bool) : PreservesFiniteColimits (pairFunctor F₁ F₂ b) :=
  Bool.rec (motive := fun b ↦ PreservesFiniteColimits (pairFunctor F₁ F₂ b))
    ‹PreservesFiniteColimits F₂› ‹PreservesFiniteColimits F₁› b

end CategoryTheory
