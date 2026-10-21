/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.ComparisonDerivedPullbackFixed
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
public import Sheaf.SixFunctors.OpenTensorNormalizationData

import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.Finite.Exact
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FullyFaithful
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.ClosedImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import Sheaf.CategoryTheory.DerivedCategory.DerivedMateComparison

/-!
# Restriction normalization of derived immersion comparisons

Source: blueprint main-20261015, proof of `lem-weil-finite-duality-site-comparison`,
second paragraph; Stacks Tags 09AF, 09BM, 09AA, 015F and 0FND
(blueprint: lem-sf-derived-immersion-comparison-normalization).
-/

@[expose] public noncomputable section

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe v h w u

open CategoryTheory Limits

namespace CategoryTheory

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

open SheafOfModules.OpenTensorNormalization in
private theorem exact_hom_fac
    {C D : Type v} [Category.{h} C] [Category.{h} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) (K : CochainComplex C ℤ) (L : CochainComplex D ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ L) :
    (exactDerivedAdjunction a).homEquiv (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj L)
        (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
        G.mapDerivedCategoryFactors.inv.app L := by
  have hu : (exactDerivedAdjunction a).unit.app (DerivedCategory.Q.obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        G.mapDerivedCategoryFactors.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.inv.app K) := by
    simp only [exactDerivedAdjunction, Adjunction.localization_unit_app]
    rfl
  rw [Adjunction.homEquiv_unit, hu, G.mapDerivedCategory.map_comp]
  simp only [Category.assoc, ← G.mapDerivedCategory.map_comp_assoc,
    Iso.inv_hom_id_app]
  erw [G.mapDerivedCategory.map_id, Category.id_comp]
  have hn := G.mapDerivedCategoryFactors.inv.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← Functor.map_comp]
  rfl

namespace Functor

private theorem exactSquare_fac
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    {R : C ⥤ D} {G : D ⥤ F} {L : C ⥤ E} {S : E ⥤ F}
    [R.Additive] [G.Additive] [L.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : R ⋙ G ≅ L ⋙ S) (K : CochainComplex C ℤ) :
    (mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj K) ≫
      S.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app K) ≫
      S.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj K) =
    G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app K) := by
  have hc := mapDerivedCategoryCompIso_hom_app_factors R G K
  have hi : (mapDerivedCategoryCompIso R G).inv.app (DerivedCategory.Q.obj K) ≫
      (R ⋙ G).mapDerivedCategoryFactors.hom.app K =
    G.mapDerivedCategory.map (R.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) := by
    apply (cancel_epi ((mapDerivedCategoryCompIso R G).hom.app (DerivedCategory.Q.obj K))).mp
    rw [Iso.hom_inv_id_app_assoc]
    exact hc.symm
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [mapDerivedCategoryCompIso_hom_app_factors, mapDerivedCategoryNatIso_fac]
  rw [← Category.assoc, hi, Category.assoc]

private theorem exactSquarePlus_fac
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    {R : C ⥤ D} {G : D ⥤ F} {L : C ⥤ E} {S : E ⥤ F}
    [R.Additive] [G.Additive] [L.Additive] [S.Additive]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : R ⋙ G ≅ L ⋙ S) (K : HomotopyCategory.Plus C) :
    ((mapDerivedCategoryPlusCompIso R G).symm ≪≫
      mapDerivedCategoryPlusNatIso e ≪≫ mapDerivedCategoryPlusCompIso L S).hom.app
        (DerivedCategory.Plus.Qh.obj K) ≫
      S.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      S.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj K) =
    G.mapDerivedCategoryPlus.map (R.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      G.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj K) ≫
      DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.hom).app K) := by
  have hc := mapDerivedCategoryPlusCompIso_hom_app_factorsh R G K
  have hi : (mapDerivedCategoryPlusCompIso R G).inv.app (DerivedCategory.Plus.Qh.obj K) ≫
      (R ⋙ G).mapDerivedCategoryPlusFactorsh.hom.app K =
    G.mapDerivedCategoryPlus.map (R.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      G.mapDerivedCategoryPlusFactorsh.hom.app (R.mapHomotopyCategoryPlus.obj K) := by
    apply (cancel_epi ((mapDerivedCategoryPlusCompIso R G).hom.app
      (DerivedCategory.Plus.Qh.obj K))).mp
    rw [Iso.hom_inv_id_app_assoc]
    exact hc.symm
  simp only [Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Category.assoc]
  rw [mapDerivedCategoryPlusCompIso_hom_app_factorsh, mapDerivedCategoryPlusNatIso_hom_app_factorsh]
  rw [← Category.assoc, hi, Category.assoc]

end Functor

open SheafOfModules.OpenTensorNormalization in
private theorem exact_mate
    {A B C D : Type v} [Category.{h} A] [Category.{h} B]
    [Category.{h} C] [Category.{h} D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
    [G.Additive] [H.Additive]
    [PreservesFiniteLimits L₁] [PreservesFiniteColimits L₁]
    [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
    [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
    [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (d : R₁ ⋙ G ≅ H ⋙ R₂) (b : G ⋙ L₂ ≅ L₁ ⋙ H)
    (hb : ∀ P, a₂.unit.app (G.obj P) ≫ R₂.map (b.hom.app P) =
      G.map (a₁.unit.app P) ≫ d.hom.app (L₁.obj P)) :
    ((mateEquiv (exactDerivedAdjunction a₁) (exactDerivedAdjunction a₂)).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso d).hom)).natTrans =
        (Functor.mapDerivedCategorySquareIso b).hom := by
  have hι (K : CochainComplex A ℤ) :
      (a₂.mapHomologicalComplex (.up ℤ)).homEquiv
          ((G.mapHomologicalComplex (.up ℤ)).obj K)
          ((H.mapHomologicalComplex (.up ℤ)).obj ((L₁.mapHomologicalComplex (.up ℤ)).obj K))
          ((NatTrans.mapHomologicalComplex b.hom (.up ℤ)).app K) =
        (G.mapHomologicalComplex (.up ℤ)).map
            ((a₁.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
          (NatTrans.mapHomologicalComplex d.hom (.up ℤ)).app
            ((L₁.mapHomologicalComplex (.up ℤ)).obj K) := by
    apply HomologicalComplex.Hom.ext
    funext n
    exact hb (K.X n)
  apply Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ))
  intro K
  apply (cancel_mono (H.mapDerivedCategory.map (L₁.mapDerivedCategoryFactors.hom.app K) ≫
    H.mapDerivedCategoryFactors.hom.app ((L₁.mapHomologicalComplex (.up ℤ)).obj K))).mp
  have hc := derivedMate_comparison
    (a₁.mapHomologicalComplex (.up ℤ)) (a₂.mapHomologicalComplex (.up ℤ))
    (exactDerivedAdjunction a₁) (exactDerivedAdjunction a₂)
    L₁.mapDerivedCategoryFactors.hom L₂.mapDerivedCategoryFactors.hom
    R₁.mapDerivedCategoryFactors R₂.mapDerivedCategoryFactors
    G.mapDerivedCategoryFactors H.mapDerivedCategoryFactors
    (exact_hom_fac a₁) (exact_hom_fac a₂)
    (TwoSquare.mk _ _ _ _ (NatTrans.mapHomologicalComplex d.hom (.up ℤ)))
    (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso d).hom)
    (Functor.exactSquare_fac d) (NatTrans.mapHomologicalComplex b.hom (.up ℤ)) hι K
  exact hc.trans (Functor.exactSquare_fac b K).symm

open SheafOfModules.OpenTensorNormalization in
private theorem exact_unit_isIso
    {C D : Type v} [Category.{h} C] [Category.{h} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) [IsIso a.unit] : IsIso (exactDerivedAdjunction a).unit := by
  have hf := (exactDerivedAdjunction a).fullyFaithfulLOfCompIsoId
    ((Functor.mapDerivedCategoryCompIso F G).symm ≪≫
      Functor.mapDerivedCategoryNatIso (asIso a.unit).symm ≪≫
        Functor.mapDerivedCategoryIdIso C)
  have := hf.full
  have := hf.faithful
  exact (exactDerivedAdjunction a).unit_isIso_of_L_fully_faithful

private theorem exact_base_change
    {B B' C C' : Type*} [Category* B] [Category* B'] [Category* C] [Category* C']
    [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
    [HasDerivedCategory B] [HasDerivedCategory B']
    [HasDerivedCategory C] [HasDerivedCategory C']
    [EnoughInjectives B] [EnoughInjectives B']
    {G : B ⥤ C} {G' : B' ⥤ C'} {β : B ⥤ B'} {γ : C ⥤ C'}
    [G.Additive] [G'.Additive] [β.Additive] [γ.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    [PreservesFiniteLimits β] [PreservesFiniteColimits β]
    [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]
    (e : G ⋙ γ ≅ β ⋙ G') :
    Functor.rightDerivedFunctorPlusBaseChange e.hom ≫
        Functor.whiskerLeft β.mapDerivedCategoryPlus
          G'.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom =
      Functor.whiskerRight G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom
          γ.mapDerivedCategoryPlus ≫
        ((Functor.mapDerivedCategoryPlusCompIso G γ).symm ≪≫
          Functor.mapDerivedCategoryPlusNatIso e ≪≫
            Functor.mapDerivedCategoryPlusCompIso β G').hom := by
  apply Localization.natTrans_ext DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso B)
  intro K
  apply (cancel_epi (γ.mapDerivedCategoryPlus.map
    (G.rightDerivedFunctorPlusUnit.app K))).mp
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  have hf := congr_app (Functor.rightDerivedFunctorPlusBaseChange_fac e.hom) K
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.comp_id] at hf
  rw [reassoc_of% hf, ← Functor.map_comp_assoc]
  have hu := congr_app G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_fac K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hu
  rw [hu]
  apply (cancel_mono
    (G'.mapDerivedCategoryPlus.map (β.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
      G'.mapDerivedCategoryPlusFactorsh.hom.app (β.mapHomotopyCategoryPlus.obj K))).mp
  simp only [Category.assoc]
  rw [Functor.exactSquarePlus_fac e K]
  simp only [Functor.rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.comp_id, Category.id_comp,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app, Functor.map_id]
  erw [Category.id_comp, Category.id_comp]
  erw [Category.assoc, Category.assoc, Category.assoc]
  erw [G'.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.naturality_assoc]
  simp only [← G'.mapDerivedCategoryPlus.map_comp_assoc,
    Iso.inv_hom_id_app, Functor.map_id, Category.id_comp]
  have hu' := congr_app G'.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_fac
    (β.mapHomotopyCategoryPlus.obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hu'
  erw [reassoc_of% hu']
  simp only [Iso.inv_hom_id_app, ← Functor.map_comp_assoc,
    Functor.map_id, Category.id_comp]
  erw [Category.comp_id]

private theorem plus_counit_isIso
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (a : F ⊣ G) [IsIso a.counit] (L : DerivedCategory.Plus D) :
    IsIso (a.derivedPlus.counit.app L) := by
  have hH (K : HomotopyCategory D (.up ℤ)) :
      IsIso ((a.mapHomotopyCategory (.up ℤ)).counit.app K) := by
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    rw [Adjunction.mapHomotopyCategory_counit_app_quotient]
    have : ∀ n : ℤ,
        IsIso (((a.mapHomologicalComplex (.up ℤ)).counit.app P).f n) :=
      fun n ↦ inferInstanceAs (IsIso (a.counit.app (P.X n)))
    have : IsIso ((a.mapHomologicalComplex (.up ℤ)).counit.app P) :=
      HomologicalComplex.Hom.isIso_of_components _
    infer_instance
  have hP (K : HomotopyCategory.Plus D) :
      IsIso (a.mapHomotopyCategoryPlus.counit.app K) := by
    have : IsIso ((HomotopyCategory.Plus.ι D).map
        (a.mapHomotopyCategoryPlus.counit.app K)) := by
      rw [Adjunction.ι_map_mapHomotopyCategoryPlus_counit_app]
      exact hH K.obj
    exact isIso_of_reflects_iso _ (HomotopyCategory.Plus.ι D)
  have hQ (K : HomotopyCategory.Plus D) :
      IsIso (a.derivedPlus.counit.app (DerivedCategory.Plus.Qh.obj K)) := by
    have hc := a.derivedPlus_counit_app_fac K
    have := hP K
    have : IsIso (F.mapDerivedCategoryPlus.map (G.rightDerivedFunctorPlusUnit.app K) ≫
        a.derivedPlus.counit.app (DerivedCategory.Plus.Qh.obj K)) := by
      rw [hc]
      infer_instance
    have : IsIso G.rightDerivedFunctorPlusUnit :=
      Functor.isIso_rightDerivedFunctorPlusUnit G
    have : IsIso (G.rightDerivedFunctorPlusUnit.app K) :=
      NatIso.isIso_app_of_isIso G.rightDerivedFunctorPlusUnit K
    have : IsIso (F.mapDerivedCategoryPlus.map (G.rightDerivedFunctorPlusUnit.app K)) :=
      F.mapDerivedCategoryPlus.map_isIso _
    exact IsIso.of_isIso_comp_left
      (F.mapDerivedCategoryPlus.map (G.rightDerivedFunctorPlusUnit.app K)) _
  exact (NatTrans.isIso_app_iff_of_iso a.derivedPlus.counit
    (DerivedCategory.Plus.Qh.objObjPreimageIso L)).mp
      (hQ (DerivedCategory.Plus.Qh.objPreimage L))

end CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- Open etale restriction is also a left adjoint, hence preserves colimits.
Source: Stacks Tag 03DI; the existing restriction/direct-image adjunction
(blueprint: lem-sf-derived-immersion-comparison-normalization). -/
instance derivedImmersionEtaleRestriction_isLeftAdjoint (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).IsLeftAdjoint :=
  (Etale.openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j).isLeftAdjoint

/-- Open pro-etale restriction is also a left adjoint, hence preserves colimits.
Source: Stacks Tag 09AE; the existing restriction/direct-image adjunction
(blueprint: lem-sf-derived-immersion-comparison-normalization). -/
instance derivedImmersionProEtaleRestriction_isLeftAdjoint (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (openImmersionRestriction (ModuleCat.{u + 1} A) j).IsLeftAdjoint :=
  (openImmersionRestrictionLowerStarAdjunction (ModuleCat.{u + 1} A) j).isLeftAdjoint

/-- Termwise canonical pullback comparison in open-restriction form, using the exact
composition identifications. Source: Stacks Tags 09AF and 015F
(blueprint: lem-sf-derived-immersion-comparison-normalization). -/
def derivedImmersionOpenPullbackComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
        (openImmersionRestriction (ModuleCat.{u + 1} A) j).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso (openComparisonRestrictionIso A j) ≪≫
      Functor.mapDerivedCategoryCompIso _ _

/-- Termwise descent of the specified canonical open extension comparison.
Source: Stacks Tags 09AF and 015F
(blueprint: lem-sf-derived-immersion-comparison-normalization). -/
def derivedImmersionOpenExtensionComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (openImmersionLowerShriekComparisonUpperStarIso (ModuleCat.{u + 1} A) j) ≪≫
        Functor.mapDerivedCategoryCompIso _ _

/-- The exact derived etale open adjunction, with its localized ordinary unit and counit.
Source: Stacks Tag 015F
(blueprint: lem-sf-derived-immersion-comparison-normalization). -/
abbrev derivedImmersionOpenEtaleAdjunction (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
    (Etale.openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j)

/-- The exact derived pro-etale open adjunction, localized with the same normalization.
Source: Stacks Tag 015F
(blueprint: lem-sf-derived-immersion-comparison-normalization). -/
abbrev derivedImmersionOpenProEtaleAdjunction (A : Type (u + 1)) [CommRing A]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  SheafOfModules.OpenTensorNormalization.exactDerivedAdjunction
    (openImmersionLowerShriekAdjunction (ModuleCat.{u + 1} A) j)

/-- The canonical open comparisons respect units and counits on the unbounded derived
categories. The invertible units identify the restricted extension comparison with the
identity. Source: blueprint finite-duality site-comparison proof, paragraph 2;
Stacks Tags 09AF, 0F70 and 015F
(blueprint: lem-sf-derived-immersion-comparison-normalization).

Proof:
1. Comparison, both restrictions and both extensions by zero are exact. Apply the
exact-functor localization to their canonical sheaf comparisons.
2. The sheaf unit equation is `openComparison_unit_normalization` (Tag 09AF).
3. Transpose C_X(e_M) after the inverse open comparison. Naturality of the pullback
comparison and the etale triangle identity give a_M as its transpose. The inverse
transpose is e'_M after j_!(a_M), giving the sheaf counit equation.
4. Exact derived adjunctions localize these units and counits. Exact transformation
pasting localizes both sheaf equations, with the displayed canonical compositors.
5. The etale open unit is invertible, as is its termwise inverse after localization.
The unit equation then makes the pro-etale unit at C_U L invertible. Cancelling the
units says precisely that the restriction of o_j is the identity. The canonical
pullback comparisons carry their identity and composition identifications through
localization; the same argument covers identity and empty immersions. -/
theorem derivedImmersionOpen_normalization (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (j : U ⟶ X) [IsOpenImmersion j] :
    (∀ L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.map
          ((derivedImmersionOpenEtaleAdjunction A j).unit.app L) ≫
        (derivedImmersionOpenPullbackComparison A j).hom.app
          ((Etale.openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj L) ≫
        (openImmersionRestriction (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
          ((derivedImmersionOpenExtensionComparison A j).hom.app L) =
      (derivedImmersionOpenProEtaleAdjunction A j).unit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj L)) ∧
    (∀ M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)),
      (derivedImmersionOpenExtensionComparison A j).hom.app
          ((Etale.openImmersionRestriction (ModuleCat.{u + 1} A) j).mapDerivedCategory.obj M) ≫
        (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory.map
          ((derivedImmersionOpenPullbackComparison A j).hom.app M) ≫
        (derivedImmersionOpenProEtaleAdjunction A j).counit.app
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj M) =
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        ((derivedImmersionOpenEtaleAdjunction A j).counit.app M)) ∧
    (∀ L : DerivedCategory (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)),
      IsIso ((derivedImmersionOpenEtaleAdjunction A j).unit.app L) ∧
      IsIso ((derivedImmersionOpenProEtaleAdjunction A j).unit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) U).mapDerivedCategory.obj L))) := by
  let B := ModuleCat.{u + 1} A
  let e := Etale.openImmersionLowerShriekAdjunction B j
  let d := openImmersionLowerShriekAdjunction B j
  let a := openComparisonRestrictionIso A j
  let o := openImmersionLowerShriekComparisonUpperStarIso B j
  have hb F : d.unit.app ((comparisonUpperStar B U).obj F) ≫
      (openImmersionRestriction B j).map (o.inv.app F) =
        (comparisonUpperStar B U).map (e.unit.app F) ≫ a.hom.app _ := by
    apply (cancel_mono ((openImmersionRestriction B j).map (o.hom.app F))).mp
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    exact ((openComparison_unit_normalization A j).2 F).symm
  have hm := CategoryTheory.exact_mate e d a o.symm hb
  have ho : (Functor.mapDerivedCategorySquareIso o.symm).hom =
      (derivedImmersionOpenExtensionComparison A j).inv := by
    simp only [Functor.mapDerivedCategorySquareIso, derivedImmersionOpenExtensionComparison,
      Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapDerivedCategoryNatIso_symm, Category.assoc, o, B]
  rw [ho] at hm
  change ((mateEquiv (derivedImmersionOpenEtaleAdjunction A j)
    (derivedImmersionOpenProEtaleAdjunction A j)).symm
    (TwoSquare.mk _ _ _ _ (derivedImmersionOpenPullbackComparison A j).hom)).natTrans =
      (derivedImmersionOpenExtensionComparison A j).inv at hm
  refine ⟨?_, ?_, ?_⟩
  · intro L
    have hu := unit_mateEquiv_symm (derivedImmersionOpenEtaleAdjunction A j)
      (derivedImmersionOpenProEtaleAdjunction A j)
      (TwoSquare.mk _ _ _ _ (derivedImmersionOpenPullbackComparison A j).hom) L
    dsimp only [CategoryTheory.Functor.id_obj] at hu
    rw [congr_app hm L] at hu
    rw [reassoc_of% hu, ← Functor.map_comp]
    simp
  · intro M
    have hc := mateEquiv_counit_symm (derivedImmersionOpenEtaleAdjunction A j)
      (derivedImmersionOpenProEtaleAdjunction A j)
      (TwoSquare.mk _ _ _ _ (derivedImmersionOpenPullbackComparison A j).hom) M
    rw [congr_app hm _] at hc
    rw [hc, Iso.hom_inv_id_app_assoc]
  · intro L
    have := CategoryTheory.exact_unit_isIso e
    have := CategoryTheory.exact_unit_isIso d
    exact ⟨inferInstance, inferInstance⟩

/-- Etale closed direct image is exact; left exactness is already supplied by its
right-adjoint structure. Source: Stacks Tags 04CA and 08M3
(blueprint: lem-sf-derived-immersion-comparison-normalization).

Proof: identify the etale topos of the closed subscheme with the closed complement
topos. Its direct image on modules is exact and fully faithful, with invertible
restriction counit, as in lem-trf-oriented-closed-base-localization. -/
@[instance] theorem derivedImmersionClosedEtale_exact (A : Type (u + 1)) [CommRing A]
    [Finite A] {Z X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (h : Z ⟶ X) [IsClosedImmersion h] :
    PreservesFiniteColimits (Etale.lowerStar (ModuleCat.{u + 1} A) h) := by
  infer_instance

/-- Pro-etale closed direct image is exact over a Noetherian target; its left
exactness is the right-adjoint structure. Source: Stacks Tag 09BM
(blueprint: lem-sf-derived-immersion-comparison-normalization).

Proof: the complement open immersion is quasi-compact: every open in a Noetherian
scheme is quasi-compact. Apply lem-exc-proetale-closed-exact to this complement.
No constructibility hypothesis is used. -/
@[instance] theorem derivedImmersionClosedProEtale_exact (A : Type (u + 1)) [CommRing A]
    [Finite A] {Z X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (h : Z ⟶ X) [IsClosedImmersion h] :
    PreservesFiniteColimits (lowerStar (ModuleCat.{u + 1} A) h) := by
  let V : X.Opens :=
    ⟨(Set.range h.base)ᶜ, h.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hV : IsCompl (Set.range h.base) (Set.range V.ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact isCompl_compl
  exact preservesFiniteColimits_lowerStar_of_isCompl (R := A) h V.ι hV

/-- The ordinary closed comparison is the specified counit transpose, not an
independently chosen isomorphism. Source: Stacks Tag 0B65
(blueprint: lem-sf-derived-immersion-comparison-normalization).

Proof: the direct-image comparison is the double mate of the sectionwise comparison
of direct images. The iterated-mate identity identifies it with the mate of the
canonical pullback comparison. Applying the inverse-transpose counit formula gives
exactly the asserted component formula. -/
theorem derivedImmersionClosed_sheaf_transpose (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (h : Z ⟶ X) [IsClosedImmersion h]
    (F : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (lowerStarComparisonUpperStarBaseChange h (ModuleCat.{u + 1} A)).app F =
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).homEquiv _ _)
        ((comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) h).hom.app
            ((Etale.lowerStar (ModuleCat.{u + 1} A) h).obj F) ≫
          (comparisonUpperStar (ModuleCat.{u + 1} A) Z).map
            ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h).counit.app F)) := by
  let ad := upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h
  let e := ad.homEquiv
    ((comparisonUpperStar (ModuleCat.{u + 1} A) X).obj
      ((Etale.lowerStar (ModuleCat.{u + 1} A) h).obj F))
    ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).obj F)
  change _ = e _
  apply e.symm.injective
  rw [Equiv.symm_apply_apply]
  change (upperStar (ModuleCat.{u + 1} A) h).map
      ((lowerStarComparisonUpperStarBaseChange h (ModuleCat.{u + 1} A)).app F) ≫
      ad.counit.app _ = _
  have hm := mateEquiv_counit_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h)
    (lowerStarComparisonUpperStarBaseChange h (ModuleCat.{u + 1} A)) F
  have hi := iterated_mateEquiv_conjugateEquiv_symm
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h)
    (comparisonAdjunction (ModuleCat.{u + 1} A) X)
    (comparisonAdjunction (ModuleCat.{u + 1} A) Z)
    (lowerStarCompComparisonLowerStarIso h (ModuleCat.{u + 1} A)).inv
  unfold lowerStarComparisonUpperStarBaseChange at hm
  rw [hi] at hm
  exact hm

/-- Termwise descent on D+ of the ordinary closed counit mate. The sheaf mate is
invertible for this qcqs morphism, so its descent uses the standard natural-iso API.
Source: Stacks Tags 099R, 015F and 0B65
(blueprint: lem-sf-derived-immersion-comparison-normalization). -/
def derivedImmersionClosedTermwiseComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (h : Z ⟶ X) [IsClosedImmersion h] :
    (Etale.lowerStar (ModuleCat.{u + 1} A) h).mapDerivedCategoryPlus ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus ⋙
        (lowerStar (ModuleCat.{u + 1} A) h).mapDerivedCategoryPlus :=
  letI := isIso_lowerStarComparisonUpperStarBaseChange h (ModuleCat.{u + 1} A)
  (Functor.mapDerivedCategoryPlusCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso
      (asIso (lowerStarComparisonUpperStarBaseChange h (ModuleCat.{u + 1} A))) ≪≫
        Functor.mapDerivedCategoryPlusCompIso _ _

/-- The specified derived closed mate equals the termwise sheaf mate under the
canonical exact-functor identifications; its counit equation has invertible counits,
so restriction identifies it with the identity of C_Z L.
Source: blueprint finite-duality site-comparison proof, paragraph 2;
Stacks Tags 015F, 0FND, 09AA and 0B65
(blueprint: lem-sf-derived-immersion-comparison-normalization).

Proof:
1. The two closed direct images are exact by the preceding exactness statements.
Their universal right-derived comparisons with termwise localization are invertible.
2. The fraction formula of lem-pc-pre-derived-adjoint-functors-general, at identity
quasi-isomorphisms, identifies the derived transpose of Q(f) with Q(f-sharp).
The inverse images of other quasi-isomorphisms give the same formula on all fractions.
Thus the derived closed counits are the localized ordinary counits.
3. Localize the ordinary transpose equation by exact transformation pasting. It gives
the counit equation for the termwise mate. The specified derived mate has the same
transpose by lem-weil-pbc-comparison-direct-image-canonical-mate. Injectivity of the
adjunction Hom bijection identifies these actual maps, giving the first equality.
4. Both ordinary closed counits are invertible by the closed-complement description
and lem-exc-proetale-closed-fully-faithful. Their termwise inverses localize, giving
invertibility of the derived counits. Cancelling them in the second equality identifies
the restricted mate with the identity. All comparisons use the canonical compositors,
which localize their identity and composition equations, including empty immersions. -/
theorem derivedImmersionClosed_normalization (A : Type (u + 1)) [CommRing A] [Finite A]
    {Z X : Scheme.{u}} [IsLocallyNoetherian X] [CompactSpace X]
    (h : Z ⟶ X) [IsClosedImmersion h]
    (L : DerivedCategory.Plus (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    ((fixedComparisonDirectImageMatePlus A h).app L ≫
      (lowerStar (ModuleCat.{u + 1} A) h).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.obj L) =
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus.map
          ((Etale.lowerStar (ModuleCat.{u + 1} A) h
            ).rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app L) ≫
        (derivedImmersionClosedTermwiseComparison A h).hom.app L) ∧
    ((fixedComparisonPullbackPlus A h).hom.app
        ((Etale.rightDerivedLowerStarPlus (ModuleCat.{u + 1} A) h).obj L) ≫
      (upperStar (ModuleCat.{u + 1} A) h).mapDerivedCategoryPlus.map
        ((fixedComparisonDirectImageMatePlus A h).app L) ≫
      (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) h).counit.app
        ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.obj L) =
      (comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.map
        ((Etale.derivedUpperStarLowerStarAdjunctionPlus
          (ModuleCat.{u + 1} A) h).counit.app L)) ∧
    IsIso ((Etale.derivedUpperStarLowerStarAdjunctionPlus
      (ModuleCat.{u + 1} A) h).counit.app L) ∧
    IsIso ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} A) h).counit.app
      ((comparisonUpperStar (ModuleCat.{u + 1} A) Z).mapDerivedCategoryPlus.obj L)) := by
  refine ⟨?_, fixedComparisonDirectImageMatePlus_counit A h L, ?_, ?_⟩
  · have := isIso_lowerStarComparisonUpperStarBaseChange h (ModuleCat.{u + 1} A)
    exact congr_app (CategoryTheory.exact_base_change
      (asIso (lowerStarComparisonUpperStarBaseChange h (ModuleCat.{u + 1} A)))) L
  · dsimp only [Etale.derivedUpperStarLowerStarAdjunctionPlus]
    rw [Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
    exact CategoryTheory.plus_counit_isIso
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h) L
  · dsimp only [derivedUpperStarLowerStarAdjunctionPlus]
    rw [Adjunction.derivedAdjunctionPlus_eq_derivedPlus]
    exact CategoryTheory.plus_counit_isIso
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) h) _

end AlgebraicGeometry.ProEtale
