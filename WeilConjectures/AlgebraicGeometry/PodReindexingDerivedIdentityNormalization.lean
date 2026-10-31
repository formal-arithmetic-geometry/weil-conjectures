/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Derived identity normalization

Source: blueprint dual-Tate compatibility, Step 6; localization universal property
(blueprint: lem-pod-reindexing-derived-identity-normalization).
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

private theorem identity_model_derived {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (P : CochainComplex C ℤ) :
    (Functor.mapDerivedCategoryIdIso C).hom.app (DerivedCategory.Q.obj P) =
      (𝟭 C).mapDerivedCategoryFactors.hom.app P := by
  have hf := Functor.mapDerivedCategoryIdIso_hom_app_Qh_obj C
    ((HomotopyCategory.quotient C (.up ℤ)).obj P)
  refine hf.trans ?_
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change (𝟭 C).mapDerivedCategory.map (𝟙 _) ≫
    (𝟭 C).mapDerivedCategoryFactors.hom.app P ≫ 𝟙 _ ≫
      DerivedCategory.Qh.map (𝟙 _) = _
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id]
  exact Category.comp_id ((𝟭 C).mapDerivedCategoryFactors.hom.app P)

private theorem derived_identity_unique {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (F : C ⥤ C) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (a : F.mapDerivedCategory ≅ 𝟭 _) (b : F ≅ 𝟭 C)
    (ha : ∀ P : CochainComplex C ℤ, a.hom.app (DerivedCategory.Q.obj P) =
      F.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex b.hom (.up ℤ)).app P)) :
    a = Functor.mapDerivedCategoryNatIso b ≪≫ Functor.mapDerivedCategoryIdIso C := by
  apply Iso.ext
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) (fun P ↦ ?_)
  exact (ha P).trans ((Functor.mapDerivedCategoryNatIso_fac b P).symm.trans
    (congrArg ((Functor.mapDerivedCategoryNatIso b).hom.app (DerivedCategory.Q.obj P) ≫ ·)
      (identity_model_derived P).symm))

private theorem mapDerived_identity {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] (F G : C ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (e : F ≅ G) (a : G ≅ 𝟭 C) (k : F ≅ 𝟭 C) (h : e ≪≫ a = k) :
    Functor.mapDerivedCategoryNatIso a ≪≫ Functor.mapDerivedCategoryIdIso C =
      (Functor.mapDerivedCategoryNatIso e).symm ≪≫
        (Functor.mapDerivedCategoryNatIso k ≪≫ Functor.mapDerivedCategoryIdIso C) := by
  have hh := congrArg (fun a ↦ (Functor.mapDerivedCategoryNatIso a).hom) h
  rw [Functor.mapDerivedCategoryNatIso_trans] at hh
  apply Iso.ext
  apply (cancel_epi (Functor.mapDerivedCategoryNatIso e).hom).mp
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, hh]

/-- The sectionwise identity equality and a normalized model determine its derived image.
Source: blueprint dual-Tate compatibility, Step 6; Stacks 015F
(blueprint: lem-pod-reindexing-derived-identity-normalization).

Proof: localization extensionality and the model equation determine the normalized derived
isomorphism. The derived natural-isomorphism functor preserves the equality isomorphisms and
composition. Substitute the normalized isomorphism and cancel the derived equality
isomorphism to obtain the displayed equality. -/
theorem podReindexingDerivedIdentityNormalization {C : Type*}
    [Category C] [Abelian C] [HasDerivedCategory C]
    (F G : C ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (h : F = G) (hd : F.mapDerivedCategory = G.mapDerivedCategory)
    (a : G ≅ 𝟭 C) (k : F ≅ 𝟭 C) (kd : F.mapDerivedCategory ≅ 𝟭 _)
    (hraw : eqToIso h ≪≫ a = k)
    (hmodel : ∀ P : CochainComplex C ℤ, kd.hom.app (DerivedCategory.Q.obj P) =
      F.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex k.hom (.up ℤ)).app P)) :
    Functor.mapDerivedCategoryNatIso a ≪≫ Functor.mapDerivedCategoryIdIso C =
      (eqToIso hd).symm ≪≫ kd := by
  have he : Functor.mapDerivedCategoryNatIso (eqToIso h) = eqToIso hd :=
    derived_eqToIso F G h
  rw [derived_identity_unique F kd k hmodel, ← he]
  exact mapDerived_identity F G (eqToIso h) a k hraw

end WeilConjectures
