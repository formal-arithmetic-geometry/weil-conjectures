/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Ext identity comparison

Source: Stacks Project, derived.tex, Tag 015F; Mathlib Ext.Map.
(blueprint: lem-weil-pbc-ext-exact-functor-identity-comparison)
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

/-- An exact functor isomorphic to the identity acts on Ext by that comparison.
Source: Stacks Project, derived.tex, Tag 015F, and Mathlib Ext.Map.

Proof: represent x by a shifted morphism between single complexes in the derived
category. The identity functor on complexes induces the identity after localization.
The components of e induce the corresponding isomorphism from the functor induced by F
to the identity. Naturality for the shifted morphism is exactly the displayed square.
After cancelling the canonical comparisons with single complexes and shifts, its
components are Ext.mk₀ (e.hom.app X) and Ext.mk₀ (e.hom.app Y).
(blueprint: lem-weil-pbc-ext-exact-functor-identity-comparison)
-/
theorem exactFunctorIdentityComparison
    {C : Type*} [Category C] [Abelian C] [HasExt.{w} C]
    (F : C ⥤ C) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (e : F ≅ 𝟭 C) {X Y : C} {n : ℕ} (x : Ext.{w} X Y n) :
    (x.mapExactFunctor F).comp (Ext.mk₀ (e.hom.app Y)) (add_zero n) =
      (Ext.mk₀ (e.hom.app X)).comp x (zero_add n) := by sorry

end CategoryTheory.Abelian.Ext
