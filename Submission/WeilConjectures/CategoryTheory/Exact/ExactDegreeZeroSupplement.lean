/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import Submission.WeilConjectures.CategoryTheory.ExactDegreeZero

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# A named interface for exact functors on degree-zero objects

The object and morphism functions have their own names. In particular, comparing their
images under a localized functor does not require unfolding the single-degree functor.
The constructions are the canonical Mathlib single functor and its exact-functor comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace SheafExactDegreeZero

variable {V W X : Type*} [Category V] [Category W] [Category X]
  [Abelian V] [Abelian W] [Abelian X]
  [HasDerivedCategory V] [HasDerivedCategory W] [HasDerivedCategory X]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Compatibility with the canonical composition and isomorphism comparisons.
Source: Mathlib exact-functor single comparison and the source library's single coherence.
(blueprint: def-geo-exact-degree-zero-interface) -/
theorem comparison_comp (F : V ⥤ W) (G : W ⥤ X) (H : V ⥤ X)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H) (M : V) :
    (comparison G).inv.app (F.obj M) ≫
      G.mapDerivedCategory.map ((comparison F).inv.app M) ≫
      (Functor.mapDerivedCategoryCompIso F G).hom.app (obj V M) ≫
      (Functor.mapDerivedCategoryNatIso e).hom.app (obj V M) =
    map (e.hom.app M) ≫ (comparison H).inv.app M := by
  unfold comparison functor map obj
  change (G.mapDerivedCategorySingleFunctor 0).inv.app (F.obj M) ≫
    G.mapDerivedCategory.map ((F.mapDerivedCategorySingleFunctor 0).inv.app M) ≫
    (Functor.mapDerivedCategoryCompIso F G).hom.app _ ≫
    (Functor.mapDerivedCategoryNatIso e).hom.app _ =
    (DerivedCategory.singleFunctor X 0).map (e.hom.app M) ≫
      (H.mapDerivedCategorySingleFunctor 0).inv.app M
  rw [← cancel_mono ((H.mapDerivedCategorySingleFunctor 0).hom.app M)]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_hom_app_singleFunctor,
    ← Functor.mapDerivedCategoryCompIso_hom_app_singleFunctor F G M]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc,
    ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc, Category.comp_id]

/-- Units of exact functors respect a specified composition isomorphism.
(blueprint: def-geo-exact-degree-zero-interface) -/
theorem unit_comp (F : V ⥤ W) (G : W ⥤ X) (H : V ⥤ X)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : F ⋙ G ≅ H)
    (eD : F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ H.mapDerivedCategory)
    (heD : eD = Functor.mapDerivedCategoryCompIso F G ≪≫
      Functor.mapDerivedCategoryNatIso e)
    {K : X} {L : W} {M : V}
    (f : K ⟶ G.obj L) (g : L ⟶ F.obj M) (h : K ⟶ H.obj M)
    (hh : h = f ≫ G.map g ≫ e.hom.app M) :
    unit H h = unit G f ≫ G.mapDerivedCategory.map (unit F g) ≫
      eD.hom.app (obj V M) := by
  subst eD
  unfold unit
  subst h
  simp only [map_comp, Functor.map_comp, Category.assoc,
    Iso.trans_hom, NatTrans.comp_app]
  have hn := (comparison G).inv.naturality g
  change map (G.map g) ≫ (comparison G).inv.app (F.obj M) =
    (comparison G).inv.app L ≫ G.mapDerivedCategory.map (map g) at hn
  rw [← reassoc_of% hn, comparison_comp F G H e M]

universe u

end SheafExactDegreeZero
