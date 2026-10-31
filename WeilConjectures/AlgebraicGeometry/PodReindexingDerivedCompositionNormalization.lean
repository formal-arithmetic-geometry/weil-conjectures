/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Derived composition normalization

Source: blueprint dual-Tate compatibility, Step 6; localization universal property
(blueprint: lem-pod-reindexing-derived-composition-normalization).
-/

@[expose] public section
set_option autoImplicit false
set_option Elab.async false

open CategoryTheory CategoryTheory.Limits

namespace WeilConjectures

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem derived_eqToIso {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (h : F = G) :
    Functor.mapDerivedCategoryNatIso (eqToIso h) =
      eqToIso (by cases h; rfl) := by
  subst h
  apply Iso.ext
  exact Functor.mapDerivedCategoryNatIso_refl

private theorem mapDerived_compositor {C B D : Type*}
    [Category C] [Category B] [Category D] [Abelian C] [Abelian B] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory B] [HasDerivedCategory D]
    (F F' : C ⥤ B) (G G' : B ⥤ D) (V V' : C ⥤ D)
    [F.Additive] [F'.Additive] [G.Additive] [G'.Additive] [V.Additive] [V'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits V'] [PreservesFiniteColimits V']
    (eF : F ≅ F') (eG : G ≅ G') (eV : V ≅ V')
    (a : V' ≅ F' ⋙ G') (k : V ≅ F ⋙ G)
    (h : eV ≪≫ a = k ≪≫ Functor.isoWhiskerRight eF G ≪≫
      Functor.isoWhiskerLeft F' eG) :
    Functor.mapDerivedCategoryNatIso a ≪≫ Functor.mapDerivedCategoryCompIso F' G' =
      (Functor.mapDerivedCategoryNatIso eV).symm ≪≫
        (Functor.mapDerivedCategoryNatIso k ≪≫ Functor.mapDerivedCategoryCompIso F G) ≪≫
        Functor.isoWhiskerRight (Functor.mapDerivedCategoryNatIso eF) G.mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft F'.mapDerivedCategory
          (Functor.mapDerivedCategoryNatIso eG) := by
  apply Iso.ext
  apply (cancel_epi (Functor.mapDerivedCategoryNatIso eV).hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, ← Functor.mapDerivedCategoryNatIso_trans, h]
  simp only [Functor.mapDerivedCategoryNatIso_trans, Category.assoc]
  rw [Functor.mapDerivedCategoryNatIso_isoWhiskerLeft]
  rw [← Category.assoc (Functor.mapDerivedCategoryNatIso
    (Functor.isoWhiskerRight eF G)).hom]
  rw [Functor.mapDerivedCategoryNatIso_isoWhiskerRight]
  simp only [Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Category.assoc]

private theorem derived_compositor_unique {C B D : Type*}
    [Category C] [Category B] [Category D] [Abelian C] [Abelian B] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory B] [HasDerivedCategory D]
    (F : C ⥤ B) (G : B ⥤ D) (V : C ⥤ D)
    [F.Additive] [G.Additive] [V.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (a : V.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory)
    (b : V ≅ F ⋙ G)
    (ha : ∀ P : CochainComplex C ℤ, a.hom.app (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      V.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex b.hom (.up ℤ)).app P)) :
    a = Functor.mapDerivedCategoryNatIso b ≪≫ Functor.mapDerivedCategoryCompIso F G := by
  apply Iso.ext
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) (fun P ↦ ?_)
  apply (cancel_mono (G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
    G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P))).mp
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [ha, Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]

/-- The sectionwise composition equality and a normalized model determine its derived image.
Source: blueprint dual-Tate compatibility, Step 6; Stacks 015F
(blueprint: lem-pod-reindexing-derived-composition-normalization).

Proof: localization extensionality and the model equation determine the normalized derived
isomorphism. The derived natural-isomorphism functor preserves the equality isomorphisms and
composition; in the compositor case use compatibility with both whiskerings. Substitution
of the normalized isomorphism gives the displayed equality. -/
theorem podReindexingDerivedCompositionNormalization {C B D : Type*}
    [Category C] [Category B] [Category D] [Abelian C] [Abelian B] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory B] [HasDerivedCategory D]
    (F F' : C ⥤ B) (G G' : B ⥤ D) (V V' : C ⥤ D)
    [F.Additive] [F'.Additive] [G.Additive] [G'.Additive] [V.Additive] [V'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits V'] [PreservesFiniteColimits V']
    (hF : F = F') (hG : G = G') (hV : V = V')
    (hdF : F.mapDerivedCategory = F'.mapDerivedCategory)
    (hdG : G.mapDerivedCategory = G'.mapDerivedCategory)
    (hdV : V.mapDerivedCategory = V'.mapDerivedCategory)
    (a : V' ≅ F' ⋙ G') (k : V ≅ F ⋙ G)
    (kd : V.mapDerivedCategory ≅ F.mapDerivedCategory ⋙ G.mapDerivedCategory)
    (hraw : eqToIso hV ≪≫ a = k ≪≫ Functor.isoWhiskerRight (eqToIso hF) G ≪≫
      Functor.isoWhiskerLeft F' (eqToIso hG))
    (hmodel : ∀ P : CochainComplex C ℤ, kd.hom.app (DerivedCategory.Q.obj P) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
      V.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex k.hom (.up ℤ)).app P)) :
    Functor.mapDerivedCategoryNatIso a ≪≫ Functor.mapDerivedCategoryCompIso F' G' =
      (eqToIso hdV).symm ≪≫ kd ≪≫
        Functor.isoWhiskerRight (eqToIso hdF) G.mapDerivedCategory ≪≫
        Functor.isoWhiskerLeft F'.mapDerivedCategory (eqToIso hdG) := by
  have heF : Functor.mapDerivedCategoryNatIso (eqToIso hF) = eqToIso hdF :=
    derived_eqToIso F F' hF
  have heG : Functor.mapDerivedCategoryNatIso (eqToIso hG) = eqToIso hdG :=
    derived_eqToIso G G' hG
  have heV : Functor.mapDerivedCategoryNatIso (eqToIso hV) = eqToIso hdV :=
    derived_eqToIso V V' hV
  rw [derived_compositor_unique F G V kd k hmodel, ← heF, ← heG, ← heV]
  exact mapDerived_compositor F F' G G' V V' (eqToIso hF) (eqToIso hG) (eqToIso hV)
    a k hraw

end WeilConjectures
