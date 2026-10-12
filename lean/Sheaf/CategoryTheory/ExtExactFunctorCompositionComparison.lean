/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Ext composition comparison

Source: Stacks Project, derived.tex, Tag 015F; Mathlib Ext.Map.
(blueprint: lem-weil-pbc-ext-exact-functor-composition-comparison)
-/

@[expose] public section

universe w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

/-- Exact functors respect composition after transport by a natural isomorphism.
Source: Stacks Project, derived.tex, Tag 015F (lemma-right-derived-exact-functor:
every complex computes an exact functor), and Mathlib Ext.Map's definition through
localized shifted morphisms.

Proof: identify Ext with shifted morphisms between complexes concentrated in degree zero.
The induced functor for F followed by G agrees with that for their composite, through
its canonical comparison. The natural isomorphism e induces an isomorphism on complexes
and their localization. Its naturality for the shifted morphism representing x says
that mapping x by H and then e at Y equals e at X followed by mapping x by F then G.
The degree-zero components are precisely Ext.mk₀ of e.hom.app. The comparison with
single complexes and the shift isomorphisms cancel on both sides, giving the equality.
(blueprint: lem-weil-pbc-ext-exact-functor-composition-comparison)
-/
theorem exactFunctorCompositionComparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasExt.{w} C] [HasExt.{w} D] [HasExt.{w} E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : H ≅ F ⋙ G) {X Y : C} {n : ℕ} (x : Ext.{w} X Y n) :
    (x.mapExactFunctor H).comp (Ext.mk₀ (e.hom.app Y)) (add_zero n) =
      (Ext.mk₀ (e.hom.app X)).comp
        ((x.mapExactFunctor F).mapExactFunctor G) (zero_add n) := by sorry

end CategoryTheory.Abelian.Ext
