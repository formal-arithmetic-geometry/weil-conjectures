/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F7
-/
module

public import Sheaf.SecSmoothPurity.ProEtaleDerivedOpenRestriction
public import Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
public import Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import all Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
import all Sheaf.AlgebraicGeometry.UnboundedExchangeAgrees
import all Sheaf.AlgebraicGeometry.FixSiteOpenExchangeSheaf
import Sheaf.CategoryTheory.ExchangeMateCube
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarComp
import all Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import Sheaf.AlgebraicGeometry.OpenComparisonUnitNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Comparison transport of the normalized open restriction map

Source: retained blueprint Step 7, restriction and mate-pasting calculation;
Stacks Tags 099R, 09AF and 09BN
(blueprint: lem-exc-etale-origin-open-restriction-transport).

This calculation concerns open restriction of a direct image, without any proper/open
interchange map or properness hypothesis.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxErrors 1
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme

variable (A : Type u) [CommRing A] [Finite A]

/-- Exact comparison followed by canonical constant-ring realization.
Source: Stacks Tag 099R, retained blueprint Step 7
(blueprint: lem-exc-etale-origin-open-restriction-transport). -/
def etaleOriginOpenComparison (T : Scheme.{u}) :
    Etale.DerivedCategoryModule (ULift.{u + 1, u} A) T ⥤ proEtaleDerivedCategory T A :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory ⋙
    (sfIntrinsicDerivedEquivalence T A).functor

/-- Canonical realization coordinates for exact open extension, descended termwise.
Source: Stacks Tags 00YV and 09AE, retained blueprint Step 7
(blueprint: lem-exc-etale-origin-open-restriction-transport). -/
def etaleOriginOpenCoordinates {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ sfIntrinsicDerivedOpen A j ≅
      (ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
          (sfIntrinsicDerivedEquivalence Y A).functor :=
  (mapDerivedCategoryCompIso _ _).symm ≪≫
    mapDerivedCategoryNatIso
      ((sfIntrinsicModuleEquivalence X A).funInvIdAssoc
        (ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
            (sfIntrinsicModuleEquivalence Y A).functor)) ≪≫
    mapDerivedCategoryCompIso _ _

/-- The termwise canonical open comparison in intrinsic constant coefficients.
Source: Stacks Tag 09AF, retained blueprint Step 7
(blueprint: lem-exc-etale-origin-open-restriction-transport). -/
def etaleOriginOpenExtensionComparison {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
        etaleOriginOpenComparison A Y ≅
      etaleOriginOpenComparison A X ⋙ sfIntrinsicDerivedOpen A j :=
  isoWhiskerRight
      ((mapDerivedCategoryCompIso _ _).symm ≪≫
        mapDerivedCategoryNatIso
          (ProEtale.openImmersionLowerShriekComparisonUpperStarIso
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j) ≪≫
        mapDerivedCategoryCompIso _ _) (sfIntrinsicDerivedEquivalence Y A).functor ≪≫
    isoWhiskerLeft
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory
      (etaleOriginOpenCoordinates A j).symm

/-- The counit-normalized direct-image comparison, included from D+ into D and then
transported by the canonical realization. Every compatibility isomorphism is the
published universal derived-functor comparison.
Source: Stacks Tag 099R, retained blueprint Step 7
(blueprint: lem-exc-etale-origin-open-restriction-transport). -/
def etaleOriginOpenDirectImageComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (etaleOriginOpenComparison A Y).obj
        ((Etale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor.obj K.obj) ≅
      (proEtaleConstantDerivedDirectImage f A).obj
        ((etaleOriginOpenComparison A X).obj K.obj) :=
  let N := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
  let re := Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f
  let rp := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f
  letI := ProEtale.isIso_fixedComparisonDirectImageMatePlus (ULift.{u + 1, u} A) f
  (sfIntrinsicDerivedEquivalence Y A).functor.mapIso
    ((N Y).mapDerivedCategory.mapIso (re.rightDerivedFunctorPlusCompatibility.app K).symm ≪≫
      ((N Y).mapDerivedCategoryPlusCompatibility.app (re.rightDerivedFunctorPlus.obj K)).symm ≪≫
      DerivedCategory.Plus.ι.mapIso
        ((asIso (ProEtale.fixedComparisonDirectImageMatePlus
          (ULift.{u + 1, u} A) f)).app K) ≪≫
      (rp.rightDerivedFunctorPlusCompatibility.app ((N X).mapDerivedCategoryPlus.obj K)) ≪≫
      rp.rightDerivedFunctor.mapIso ((N X).mapDerivedCategoryPlusCompatibility.app K)) ≪≫
    (sfIntrinsicDerivedDirectImageComparison f A).symm.app ((N X).mapDerivedCategory.obj K.obj)


section DerivedCoordinates

private lemma homotopy_comp_inv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    (J : HomotopyCategory C (.up ℤ)) :
    (mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).inv.app J = 𝟙 _ := by
  have h := (mapHomotopyCategoryCompIso (Iso.refl (F ⋙ G)) (.up ℤ)).hom_inv_id_app J
  rw [mapHomotopyCategoryCompIso_refl_hom_app, Category.id_comp] at h
  exact h

private def derivedCoordinates
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    [Abelian.HasKInjectiveResolutions E]
    (L : C ⥤ D) (G : D ⥤ F) (H : C ⥤ E) (R : E ⥤ F)
    [L.Additive] [G.Additive] [H.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [L.PreservesKInjectiveComplexes] (e : L ⋙ G ≅ H ⋙ R) :
    L.mapDerivedCategory ⋙ G.rightDerivedFunctor ≅
      H.rightDerivedFunctor ⋙ R.mapDerivedCategory :=
  (mapDerivedCategoryCompRightDerivedFunctorIso L G).symm ≪≫
    rightDerivedFunctorNatIso e ≪≫ rightDerivedFunctorCompMapDerivedCategoryIso H R

attribute [local irreducible] derivedCoordinates

private lemma derivedCoordinates_fac
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    [Abelian.HasKInjectiveResolutions E]
    (L : C ⥤ D) (G : D ⥤ F) (H : C ⥤ E) (R : E ⥤ F)
    [L.Additive] [G.Additive] [H.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [L.PreservesKInjectiveComplexes] (e : L ⋙ G ≅ H ⋙ R)
    (J : HomotopyCategory C (.up ℤ)) :
    (mapDerivedCategoryCompRightDerivedFunctorUnit L G).app J ≫
        (derivedCoordinates L G H R e).hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app J) ≫
        (rightDerivedFunctorCompMapDerivedCategoryUnit H R).app J := by
  simp only [derivedCoordinates, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [← mapDerivedCategoryCompRightDerivedFunctorIso_hom_fac_app L G J]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  rw [← Category.assoc]
  rw [show (L ⋙ G).rightDerivedFunctorUnit.app J ≫
      (rightDerivedFunctorNatIso e).hom.app (DerivedCategory.Qh.obj J) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app J) ≫
        (H ⋙ R).rightDerivedFunctorUnit.app J by
    exact rightDerivedFunctorNatTrans_app e.hom J]
  simp only [Category.assoc]
  congr 1
  simp [rightDerivedFunctorCompMapDerivedCategoryIso]

private lemma derivedCoordinates_kinjective
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    [Abelian.HasKInjectiveResolutions E]
    (L : C ⥤ D) (G : D ⥤ F) (H : C ⥤ E) (R : E ⥤ F)
    [L.Additive] [G.Additive] [H.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [L.PreservesKInjectiveComplexes] (e : L ⋙ G ≅ H ⋙ R)
    (J : HomotopyCategory C (.up ℤ))
    [IsIso (G.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (.up ℤ)).obj J))]
    [IsIso (H.rightDerivedFunctorUnit.app J)] :
    (derivedCoordinates L G H R e).hom.app (DerivedCategory.Qh.obj J) ≫
        R.mapDerivedCategory.map (inv (H.rightDerivedFunctorUnit.app J)) ≫
        R.mapDerivedCategoryFactorsh.hom.app ((H.mapHomotopyCategory (.up ℤ)).obj J) =
      G.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app J) ≫
        inv (G.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (.up ℤ)).obj J)) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app J) := by
  have h := derivedCoordinates_fac L G H R e J
  simp only [mapDerivedCategoryCompRightDerivedFunctorUnit_app,
    rightDerivedFunctorCompMapDerivedCategoryUnit, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app, associator_hom_app, associator_inv_app,
    Category.id_comp, Category.comp_id] at h
  erw [homotopy_comp_inv, CategoryTheory.Functor.map_id, Category.id_comp,
    homotopy_comp_inv, CategoryTheory.Functor.map_id, Category.id_comp] at h
  apply (cancel_epi (G.rightDerivedFunctorUnit.app
    ((L.mapHomotopyCategory (.up ℤ)).obj J) ≫
      G.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.inv.app J))).1
  simp only [Category.assoc]
  rw [reassoc_of% h]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp,
    IsIso.hom_inv_id, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id, Category.assoc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, IsIso.hom_inv_id_assoc,
    Category.comp_id]

private lemma derivedCoordinates_Q
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    [Abelian.HasKInjectiveResolutions E]
    (L : C ⥤ D) (G : D ⥤ F) (H : C ⥤ E) (R : E ⥤ F)
    [L.Additive] [G.Additive] [H.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [L.PreservesKInjectiveComplexes] (e : L ⋙ G ≅ H ⋙ R)
    (J : CochainComplex C ℤ) [J.IsKInjective] :
    (derivedCoordinates L G H R e).hom.app (DerivedCategory.Q.obj J) ≫
        R.mapDerivedCategory.map (H.rightDerivedFunctorObjQIso J).hom ≫
        R.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj J) =
      G.rightDerivedFunctor.map (L.mapDerivedCategoryFactors.hom.app J) ≫
        (G.rightDerivedFunctorObjQIso ((L.mapHomologicalComplex (.up ℤ)).obj J)).hom ≫
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app J) := by
  letI : IsIso (G.rightDerivedFunctorUnit.app
      ((L.mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient C (.up ℤ)).obj J))) :=
    inferInstanceAs (IsIso (G.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((L.mapHomologicalComplex (.up ℤ)).obj J))))
  have h := derivedCoordinates_kinjective L G H R e
    ((HomotopyCategory.quotient C (.up ℤ)).obj J)
  change (derivedCoordinates L G H R e).hom.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj J)) ≫
      R.mapDerivedCategory.map (inv (H.rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient C (.up ℤ)).obj J))) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient E (.up ℤ)).obj
        ((H.mapHomologicalComplex (.up ℤ)).obj J)) =
    G.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient C (.up ℤ)).obj J)) ≫
      inv (G.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((L.mapHomologicalComplex (.up ℤ)).obj J))) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient F (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app J)) at h
  simp only [mapDerivedCategoryFactorsh_hom_app, rightDerivedFunctorObjQIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    asIso_inv, mapHomotopyCategoryFactors, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.id_comp, Functor.map_comp, Category.assoc] at h ⊢
  repeat first
    | erw [CategoryTheory.Functor.map_id] at h
    | erw [Category.id_comp] at h
    | erw [Category.comp_id] at h
  repeat first
    | erw [CategoryTheory.Functor.map_id]
    | erw [Category.id_comp]
    | erw [Category.comp_id]
  exact h

private lemma coordinates_inv_eq_square
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    [Abelian.HasKInjectiveResolutions E]
    (L : C ⥤ D) (G : D ⥤ F) (H : C ⥤ E) (R : E ⥤ F)
    [L.Additive] [G.Additive] [H.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [L.PreservesKInjectiveComplexes] (e : L ⋙ G ≅ H ⋙ R) :
    (derivedCoordinates L G H R e).inv = Etale.derivedSquare e.inv := by
  letI := Etale.derivedSquare_absolute H R.mapDerivedCategory
  apply rightDerived_ext (H.rightDerivedFunctor ⋙ R.mapDerivedCategory)
    (whiskerRight H.rightDerivedFunctorUnit R.mapDerivedCategory ≫
      (Functor.associator _ _ _).hom) (HomotopyCategory.quasiIso C (.up ℤ))
  ext J
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    associator_hom_app, Category.comp_id]
  have h := derivedCoordinates_fac L G H R e J
  simp only [mapDerivedCategoryCompRightDerivedFunctorUnit_app,
    rightDerivedFunctorCompMapDerivedCategoryUnit, NatTrans.comp_app,
    whiskerRight_app, whiskerLeft_app, associator_hom_app, associator_inv_app,
    Category.id_comp, Category.comp_id] at h
  erw [homotopy_comp_inv, CategoryTheory.Functor.map_id, Category.id_comp,
    homotopy_comp_inv, CategoryTheory.Functor.map_id, Category.id_comp] at h
  have hs := Etale.derivedSquare_app_fac e.inv J
  let eh : (L ⋙ G).mapHomotopyCategory (.up ℤ) ≅
      (H ⋙ R).mapHomotopyCategory (.up ℤ) :=
    { hom := NatTrans.mapHomotopyCategory e.hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory e.inv (.up ℤ)
      hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp, e.hom_inv_id,
        NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp, e.inv_hom_id,
        NatTrans.mapHomotopyCategory_id] }
  haveI : IsIso ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app J) :=
    (eh.app J).isIso_hom
  apply (cancel_epi (DerivedCategory.Qh.map
    ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app J) ≫
      R.mapDerivedCategoryFactorsh.inv.app ((H.mapHomotopyCategory (.up ℤ)).obj J))).1
  simp only [Category.assoc]
  rw [← reassoc_of% h]
  erw [Iso.hom_inv_id_app, Category.comp_id]
  erw [hs]
  rw [← DerivedCategory.Qh.map_comp_assoc]
  have hc : (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app J ≫
      (NatTrans.mapHomotopyCategory e.inv (.up ℤ)).app J = 𝟙 _ :=
    congr_app eh.hom_inv_id J
  rw [hc, CategoryTheory.Functor.map_id, Category.id_comp]

private lemma exact_left_composition
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (P : C ⥤ D) (G : D ⥤ E) [P.Additive] [G.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [P.PreservesKInjectiveComplexes] :
    mapDerivedCategoryCompRightDerivedFunctorIso P G =
      rightDerivedFunctorCompIso P G ≪≫
        isoWhiskerRight P.rightDerivedFunctorIsoMapDerivedCategory G.rightDerivedFunctor := by
  apply Iso.ext
  apply (P ⋙ G).rightDerivedFunctor.rightDerived_ext
    (P ⋙ G).rightDerivedFunctorUnit (HomotopyCategory.quasiIso C (.up ℤ))
  ext J
  simp only [NatTrans.comp_app, whiskerLeft_app, Iso.trans_hom, isoWhiskerRight_hom,
    whiskerRight_app, Category.assoc]
  rw [mapDerivedCategoryCompRightDerivedFunctorIso_hom_fac_app,
    rightDerivedFunctorCompIso_fac_app_assoc, rightDerivedFunctorCompUnit_app,
    mapDerivedCategoryCompRightDerivedFunctorUnit_app]
  erw [homotopy_comp_inv, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [Category.assoc, ← G.rightDerivedFunctor.map_comp]
  apply congrArg (fun f ↦ G.rightDerivedFunctorUnit.app
    ((P.mapHomotopyCategory (.up ℤ)).obj J) ≫ G.rightDerivedFunctor.map f)
  exact (congr_app P.rightDerivedFunctorIsoMapDerivedCategory_hom_fac J).symm

private lemma exact_right_composition
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (Q : D ⥤ E) [F.Additive] [Q.Additive]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    [F.PreservesKInjectiveComplexes] :
    rightDerivedFunctorCompMapDerivedCategoryIso F Q =
      rightDerivedFunctorCompIso F Q ≪≫
        isoWhiskerLeft F.rightDerivedFunctor Q.rightDerivedFunctorIsoMapDerivedCategory := by
  rw [rightDerivedFunctorCompMapDerivedCategoryIso_eq_viaRightDerived]
  rfl

private lemma intrinsic_directImage_coordinates {X Y : Scheme.{u}} (f : X ⟶ Y) :
    sfIntrinsicDerivedDirectImageComparison f A =
      derivedCoordinates (sfIntrinsicModuleEquivalence X A).functor
        (proEtaleConstantModuleDirectImage f A)
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
        (sfIntrinsicModuleEquivalence Y A).functor
        (sfIntrinsicDirectImageComparison f A) := by
  apply (sfIntrinsicDerivedDirectImageComparison_existsUnique f A).unique
  · exact (sfIntrinsicDerivedDirectImageComparison_existsUnique f A).exists.choose_spec
  · intro J hJ
    exact derivedCoordinates_Q (sfIntrinsicModuleEquivalence X A).functor
      (proEtaleConstantModuleDirectImage f A)
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f)
      (sfIntrinsicModuleEquivalence Y A).functor
      (sfIntrinsicDirectImageComparison f A) J

private lemma intrinsic_directImage_inv_eq_square {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sfIntrinsicDerivedDirectImageComparison f A).inv =
      Etale.derivedSquare (sfIntrinsicDirectImageComparison f A).inv := by
  rw [intrinsic_directImage_coordinates A f]
  exact coordinates_inv_eq_square _ _ _ _ _

private lemma inclusion_exact_square
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    [Abelian C] [Abelian D] [Abelian E] [Abelian F]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory F]
    (L : C ⥤ D) (G : D ⥤ F) (H : C ⥤ E) (R : E ⥤ F)
    [L.Additive] [G.Additive] [H.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (e : L ⋙ G ≅ H ⋙ R) (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map
        (((mapDerivedCategoryPlusCompIso L G).symm ≪≫
          mapDerivedCategoryPlusNatIso e ≪≫ mapDerivedCategoryPlusCompIso H R).hom.app K) =
      (mapDerivedCategorySquareIso e).hom.app K.obj := by
  have hi : DerivedCategory.Plus.ι.map
      ((mapDerivedCategoryPlusCompIso L G).inv.app K) =
      (mapDerivedCategoryCompIso L G).inv.app K.obj := by
    apply (cancel_mono ((mapDerivedCategoryCompIso L G).hom.app K.obj)).1
    erw [← ι_map_mapDerivedCategoryPlusCompIso_hom_app,
      ← DerivedCategory.Plus.ι.map_comp, Iso.inv_hom_id_app,
      CategoryTheory.Functor.map_id, ι_map_mapDerivedCategoryPlusCompIso_hom_app,
      Iso.inv_hom_id_app]
    rfl
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.map_comp,
    ι_map_mapDerivedCategoryPlusCompIso_hom_app,
    ι_map_mapDerivedCategoryPlusNatIso_hom_app, hi]
  rfl

private lemma fixed_directImage_component {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (Etale.derivedSquare (ProEtale.lowerStarComparisonUpperStarBaseChange f
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))).app K.obj =
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).mapDerivedCategory.map
        ((Etale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          f).rightDerivedFunctorPlusCompatibility.inv.app K) ≫
      DerivedCategory.Plus.ι.map
        ((ProEtale.fixedComparisonDirectImageMatePlus (ULift.{u + 1, u} A) f).app K) ≫
      (ProEtale.lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        f).rightDerivedFunctorPlusCompatibility.hom.app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategoryPlus.obj K) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let e := ProEtale.comparisonUpperStarCompUpperStarIso B f
  have h := derived_mate_plus_comparison
    (Etale.upperStarLowerStarAdjunction B f) (ProEtale.upperStarLowerStarAdjunction B f)
    (((mapDerivedCategoryPlusCompIso _ _).symm ≪≫
      mapDerivedCategoryPlusNatIso e ≪≫ mapDerivedCategoryPlusCompIso _ _).hom)
    (mapDerivedCategorySquareIso e).hom (inclusion_exact_square _ _ _ _ e) K
  rw [Etale.derived_mate_exact_eq_square] at h
  rw [← derived_mate_eq] at h
  rw [← ProEtale.underived_comparison_mate] at h
  exact h

private def intrinsic_pullback_coordinates {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (sfIntrinsicModuleEquivalence Y A).functor ⋙ sfIntrinsicPullback A f ≅
      ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f ⋙
        (sfIntrinsicModuleEquivalence X A).functor :=
  (sfIntrinsicModuleEquivalence Y A).funInvIdAssoc _

attribute [local irreducible] sfIntrinsicModuleEquivalence
  sfIntrinsicDirectImageComparison sfIntrinsicDerivedDirectImageComparison
  sfProperOpenFixedRestrictionIso

private lemma directImage_coordinate_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (F : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    (sfIntrinsicDirectImageComparison f A).inv.app F ≫
      (sfProperOpenDirectImageCoordinates A f).hom.app
        ((sfIntrinsicModuleEquivalence X A).functor.obj F) =
      (sfIntrinsicModuleEquivalence Y A).functor.map
        ((ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).map
          ((sfIntrinsicModuleEquivalence X A).unitIso.hom.app F)) := by
  simp only [sfProperOpenDirectImageCoordinates, Iso.symm_hom, Iso.trans_inv,
    NatTrans.comp_app, isoWhiskerLeft_inv, isoWhiskerRight_inv, whiskerLeft_app,
    whiskerRight_app, Iso.symm_inv, Functor.leftUnitor_inv_app,
    Functor.associator_hom_app, Category.id_comp, Category.comp_id, Category.assoc]
  rw [Equivalence.counitInv_app_functor]
  change (sfIntrinsicDirectImageComparison f A).inv.app F ≫
      (proEtaleConstantModuleDirectImage f A).map
        ((sfIntrinsicModuleEquivalence X A).functor.map
          ((sfIntrinsicModuleEquivalence X A).unitIso.hom.app F)) ≫
      (sfIntrinsicDirectImageComparison f A).hom.app
        ((sfIntrinsicModuleEquivalence X A).inverse.obj
          ((sfIntrinsicModuleEquivalence X A).functor.obj F)) = _
  have hn := (sfIntrinsicDirectImageComparison f A).hom.naturality
    ((sfIntrinsicModuleEquivalence X A).unitIso.hom.app F)
  dsimp only [Functor.comp_map] at hn
  erw [hn, Iso.inv_hom_id_app_assoc]

private def fixed_restriction {U V W T : Scheme.{u}}
    (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p) :=
  isoWhiskerLeft (ProEtale.lowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p)
      (ProEtale.upperStarIsoOpenImmersionRestriction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i) ≪≫
    sfProperOpenFixedRestrictionIso A r k i p sq ≪≫
    isoWhiskerRight (ProEtale.upperStarIsoOpenImmersionRestriction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) k).symm
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) r)

private lemma fixed_restriction_eq_baseChange
    {U V W T : Scheme.{u}} (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p) :
    (fixed_restriction A r k i p sq).hom =
      ProEtale.baseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq.toCommSq := by
  rw [ProEtale.baseChangeMap_eq]
  unfold fixed_restriction sfProperOpenFixedRestrictionIso
  rfl

private lemma intrinsic_underived_cube
    {U V W T : Scheme.{u}} (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p)
    (F : Sheaf (ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    (sfIntrinsicModuleEquivalence W A).functor.map ((ProEtale.baseChangeMap
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq.toCommSq).app F) ≫
        (sfIntrinsicDirectImageComparison r A).inv.app
          ((ProEtale.upperStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) k).obj F) ≫
        (proEtaleConstantModuleDirectImage r A).map
          ((intrinsic_pullback_coordinates A k).inv.app F) =
      (intrinsic_pullback_coordinates A i).inv.app
          ((ProEtale.lowerStar
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).obj F) ≫
        (sfIntrinsicPullback A i).map
          ((sfIntrinsicDirectImageComparison p A).inv.app F) ≫
        (sfProperOpenPullbackRestriction A r k i p sq).hom.app
          ((sfIntrinsicModuleEquivalence V A).functor.obj F) := by
  rw [← fixed_restriction_eq_baseChange A r k i p sq]
  dsimp only [fixed_restriction]
  simp only [sfProperOpenPullbackRestriction, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, isoWhiskerLeft_hom, isoWhiskerRight_hom,
    whiskerLeft_app, whiskerRight_app, Category.assoc]
  let z := ((sfProperOpenDirectImageCoordinates A r).app
    ((sfIntrinsicPullback A k).obj ((sfIntrinsicModuleEquivalence V A).functor.obj F)))
  haveI : IsIso z.hom := z.isIso_hom
  apply (cancel_mono z.hom).1
  dsimp only [z, Iso.app_hom]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app, Category.comp_id]
  have hp := congrArg (sfIntrinsicPullback A i).map
    (directImage_coordinate_unit A p F)
  simp only [Functor.map_comp] at hp
  erw [reassoc_of% hp]
  have hn := (sfProperOpenDirectImageCoordinates A r).hom.naturality
    ((intrinsic_pullback_coordinates A k).inv.app F)
  erw [hn]
  erw [reassoc_of% (directImage_coordinate_unit A r
    ((ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) k).obj F))]
  simp only [intrinsic_pullback_coordinates, sfIntrinsicTransportComp,
    sfIntrinsicTransportIso, Equivalence.funInvIdAssoc_hom_app,
    Equivalence.funInvIdAssoc_inv_app, Iso.symm_inv, Iso.symm_hom,
    isoWhiskerLeft_inv, isoWhiskerRight_inv, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, whiskerLeft_app, whiskerRight_app,
    Functor.comp_map, sfIntrinsicPullback, sfIntrinsicTransport, Category.assoc]
  simp only [← Functor.map_comp]
  change (sfIntrinsicModuleEquivalence W A).functor.map
      ((fixed_restriction A r k i p sq).hom.app F ≫
        (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) r).map
          ((sfIntrinsicModuleEquivalence U A).unitIso.hom.app
              ((ProEtale.upperStar
                (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) k).obj F) ≫
            (sfIntrinsicModuleEquivalence U A).inverse.map
              ((sfIntrinsicModuleEquivalence U A).functor.map
                ((ProEtale.upperStar
                  (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) k).map
                  ((sfIntrinsicModuleEquivalence V A).unitIso.hom.app F))))) = _
  have ht := (sfIntrinsicModuleEquivalence T A).unitIso.hom.naturality
    ((ProEtale.lowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).map
      ((sfIntrinsicModuleEquivalence V A).unitIso.hom.app F))
  have hu := (sfIntrinsicModuleEquivalence U A).unitIso.hom.naturality
    ((ProEtale.upperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) k).map
      ((sfIntrinsicModuleEquivalence V A).unitIso.hom.app F))
  have he := (fixed_restriction A r k i p sq).hom.naturality
    ((sfIntrinsicModuleEquivalence V A).unitIso.hom.app F)
  dsimp only [Functor.id_map, Functor.comp_map] at ht hu he
  erw [← hu]
  have ht' := congrArg
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).map ht
  simp only [Functor.map_comp] at ht'
  erw [← reassoc_of% ht']
  apply congrArg (sfIntrinsicModuleEquivalence W A).functor.map
  slice_rhs 2 3 => rw [← Functor.map_comp]
  erw [Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% he]
  rfl



private lemma intrinsic_restriction_eq_square
    {U V W T : Scheme.{u}} (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p) :
    (sfProperOpenDerivedRestriction A r k i p sq).hom =
      Etale.derivedSquare (sfProperOpenPullbackRestriction A r k i p sq).hom := by
  letI := (sfIntrinsicConstantModuleAdjunction p A).preservesKInjectiveComplexes
  letI := (sfIntrinsicOpenAdjunction A k).preservesKInjectiveComplexes
  have h := coordinates_inv_eq_square (sfIntrinsicPullback A k)
    (proEtaleConstantModuleDirectImage r A) (proEtaleConstantModuleDirectImage p A)
    (sfIntrinsicPullback A i) (sfProperOpenPullbackRestriction A r k i p sq).symm
  change _ = Etale.derivedSquare (sfProperOpenPullbackRestriction A r k i p sq).hom at h
  rw [← h]
  unfold derivedCoordinates
  dsimp only [sfProperOpenDerivedRestriction]
  rw [exact_left_composition, exact_right_composition]
  simp only [Iso.trans_inv, Iso.symm_inv, Iso.symm_hom, Iso.trans_hom,
    isoWhiskerRight_inv, isoWhiskerLeft_inv, isoWhiskerRight_hom,
    isoWhiskerLeft_hom, Category.assoc]
  rfl

attribute [local irreducible] sfProperOpenDerivedRestriction

private lemma inverse_cube_forward
    {C : Type*} [Category C] {X Y Z U V W : C}
    (a : X ⟶ Y) (b : Y ⟶ Z) (c : U ⟶ V) (d : V ⟶ W)
    (ai : Y ⟶ X) (bi : Z ⟶ Y) (ci : V ⟶ U) (di : W ⟶ V)
    (e : X ⟶ U) (f : Z ⟶ W)
    (ha : ai ≫ a = 𝟙 _) (hb : bi ≫ b = 𝟙 _)
    (hc : c ≫ ci = 𝟙 _) (hd : d ≫ di = 𝟙 _)
    (h : a ≫ b ≫ f = e ≫ c ≫ d) : bi ≫ ai ≫ e = f ≫ di ≫ ci := by
  have hh := congrArg (fun z ↦ bi ≫ ai ≫ z ≫ di ≫ ci) h
  simp only [← Category.assoc, ha, hb, Category.id_comp] at hh
  simpa only [Category.assoc, hd, hc, Category.comp_id] using hh.symm

private lemma exchangeMate_inverse_cube
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    (pF : F ⋙ b ≅ a ⋙ F') (pG : G ⋙ c ≅ a ⋙ G')
    (pH : H ⋙ d ≅ b ⋙ H') (pK : K ⋙ d ≅ c ⋙ K')
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' : G' ⋙ K' ⟶ F' ⋙ H')
    (hc : ∀ X : A,
      pK.hom.app (G.obj X) ≫ K'.map (pG.hom.app X) ≫ θ'.app (a.obj X) =
        d.map (θ.app X) ≫ pH.hom.app (F.obj X) ≫ H'.map (pF.hom.app X))
    (E : B) :
    c.map ((mateEquiv adj adjK (TwoSquare.mk _ _ _ _ θ)).app E) ≫
        (mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ pK.inv)).app (H.obj E) ≫
        S'.map (pH.hom.app E) =
      pG.hom.app (R.obj E) ≫
        G'.map ((mateEquiv adj adj' (TwoSquare.mk _ _ _ _ pF.inv)).app E) ≫
        (mateEquiv adj' adjK' (TwoSquare.mk _ _ _ _ θ')).app (b.obj E) := by
  apply exchangeMate_cube adj adjK adj' adjK' a b c d pF pG pH pK θ θ' _ E
  intro X
  apply inverse_cube_forward
    (pK.hom.app (G.obj X)) (K'.map (pG.hom.app X))
    (pH.hom.app (F.obj X)) (H'.map (pF.hom.app X))
    (pK.inv.app (G.obj X)) (K'.map (pG.inv.app X))
    (pH.inv.app (F.obj X)) (H'.map (pF.inv.app X))
    (d.map (θ.app X)) (θ'.app (a.obj X))
    (Iso.inv_hom_id_app _ _)
    (by rw [← Functor.map_comp, Iso.inv_hom_id_app]; exact CategoryTheory.Functor.map_id _ _)
    (Iso.hom_inv_id_app _ _)
    (by rw [← Functor.map_comp, Iso.hom_inv_id_app]; exact CategoryTheory.Functor.map_id _ _)
  exact hc X

private lemma exchangeMate_named_cube
    {A B C D A' B' C' D' : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Category A'] [Category B'] [Category C'] [Category D']
    {F : A ⥤ B} {R : B ⥤ A} {G : A ⥤ C} {H : B ⥤ D}
    {K : C ⥤ D} {S : D ⥤ C}
    {F' : A' ⥤ B'} {R' : B' ⥤ A'} {G' : A' ⥤ C'} {H' : B' ⥤ D'}
    {K' : C' ⥤ D'} {S' : D' ⥤ C'}
    (adj : F ⊣ R) (adjK : K ⊣ S) (adj' : F' ⊣ R') (adjK' : K' ⊣ S')
    (a : A ⥤ A') (b : B ⥤ B') (c : C ⥤ C') (d : D ⥤ D')
    (pF : a ⋙ F' ≅ F ⋙ b) (pG : a ⋙ G' ≅ G ⋙ c)
    (pH : b ⋙ H' ≅ H ⋙ d) (pK : c ⋙ K' ≅ K ⋙ d)
    (θ : G ⋙ K ⟶ F ⋙ H) (θ' : G' ⋙ K' ⟶ F' ⋙ H')
    (hc : ∀ X : A,
      pK.inv.app (G.obj X) ≫ K'.map (pG.inv.app X) ≫ θ'.app (a.obj X) =
        d.map (θ.app X) ≫ pH.inv.app (F.obj X) ≫ H'.map (pF.inv.app X))
    (e : R ⋙ G ⟶ H ⋙ S) (e' : R' ⋙ G' ⟶ H' ⋙ S')
    (mF : R ⋙ a ⟶ b ⋙ R') (mK : S ⋙ c ⟶ d ⋙ S')
    (he : e = (mateEquiv adj adjK (TwoSquare.mk _ _ _ _ θ)).natTrans)
    (he' : e' = (mateEquiv adj' adjK' (TwoSquare.mk _ _ _ _ θ')).natTrans)
    (hmF : mF = (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ pF.hom)).natTrans)
    (hmK : mK = (mateEquiv adjK adjK' (TwoSquare.mk _ _ _ _ pK.hom)).natTrans)
    (E : B) :
    c.map (e.app E) ≫ mK.app (H.obj E) ≫ S'.map (pH.inv.app E) =
      pG.inv.app (R.obj E) ≫ G'.map (mF.app E) ≫ e'.app (b.obj E) := by
  subst he he' hmF hmK
  simpa only [Iso.symm_hom, Iso.symm_inv] using
    exchangeMate_inverse_cube adj adjK adj' adjK' a b c d
      pF.symm pG.symm pH.symm pK.symm θ θ' hc E

attribute [local irreducible] Etale.upperStar Etale.lowerStar
  ProEtale.upperStar ProEtale.lowerStar ProEtale.comparisonUpperStar
  ProEtale.comparisonUpperStarCompUpperStarIso
  Etale.squareUpperStarIso ProEtale.upperStarCompIso
  presheafToSheaf Functor.sheafPullbackConstruction.sheafPullback
  Etale.upperStarLowerStarAdjunction ProEtale.upperStarLowerStarAdjunction

-- Keep the coefficient instances as structure parameters. Specializing the raw
-- equation directly makes the kernel repeatedly compare nested sheafification proofs.
private structure ComparisonCubeEquation
    (B : Type*) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] {U V W T : Scheme.{u}}
    (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k]
    (sq : CommSq r k i p)
    (F : Sheaf V.smallEtaleTopology B) : Prop where
  equation :
    (ProEtale.comparisonUpperStar B W).map
        ((Etale.baseChangeMap B sq.flip).app F) ≫
      (ProEtale.lowerStarComparisonUpperStarBaseChange r B).app
        ((Etale.upperStar B k).obj F) ≫
      (ProEtale.lowerStar B r).map
        ((ProEtale.comparisonUpperStarCompUpperStarIso B k).inv.app F) =
    (ProEtale.comparisonUpperStarCompUpperStarIso B i).inv.app
        ((Etale.lowerStar B p).obj F) ≫
      (ProEtale.upperStar B i).map
        ((ProEtale.lowerStarComparisonUpperStarBaseChange p B).app F) ≫
      (ProEtale.baseChangeMap B sq).app
        ((ProEtale.comparisonUpperStar B V).obj F)

private lemma comparison_underived_cube_ring
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {U V W T : Scheme.{u}}
    (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k]
    (sq : ChosenCartesianSquare r k i p)
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ComparisonCubeEquation (ModuleCat.{u + 1} Λ) r k i p sq.toCommSq F := by
  constructor
  exact exchangeMate_named_cube
    (F := Etale.upperStar (ModuleCat.{u + 1} Λ) p) (R := Etale.lowerStar (ModuleCat.{u + 1} Λ) p)
    (G := Etale.upperStar (ModuleCat.{u + 1} Λ) i) (H := Etale.upperStar (ModuleCat.{u + 1} Λ) k)
    (K := Etale.upperStar (ModuleCat.{u + 1} Λ) r) (S := Etale.lowerStar (ModuleCat.{u + 1} Λ) r)
    (F' := ProEtale.upperStar (ModuleCat.{u + 1} Λ) p)
    (R' := ProEtale.lowerStar (ModuleCat.{u + 1} Λ) p)
    (G' := ProEtale.upperStar (ModuleCat.{u + 1} Λ) i)
    (H' := ProEtale.upperStar (ModuleCat.{u + 1} Λ) k)
    (K' := ProEtale.upperStar (ModuleCat.{u + 1} Λ) r)
    (S' := ProEtale.lowerStar (ModuleCat.{u + 1} Λ) r)
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p)
    (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) T)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) V)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) W)
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} Λ) U)
    (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) p)
    (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) i)
    (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) k)
    (ProEtale.comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} Λ) r)
    (Etale.squareUpperStarIso (ModuleCat.{u + 1} Λ) sq.toCommSq.flip).hom
    (ProEtale.upperStarCompIso (ModuleCat.{u + 1} Λ) sq.w).hom
    (ProEtale.fixSiteOpenExchangeSquare Λ sq)
    (Etale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq.flip)
    (ProEtale.baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq)
    (ProEtale.lowerStarComparisonUpperStarBaseChange p (ModuleCat.{u + 1} Λ))
    (ProEtale.lowerStarComparisonUpperStarBaseChange r (ModuleCat.{u + 1} Λ))
    rfl (ProEtale.pro_baseChange_eq_mate Λ sq.toCommSq)
    (ProEtale.underived_comparison_mate Λ p)
    (ProEtale.underived_comparison_mate Λ r) F


private lemma comparison_underived_cube {V T W : Scheme.{u}}
    (p : V ⟶ T) (i : W ⟶ T) [IsOpenImmersion i]
    (F : Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) :
    ComparisonCubeEquation (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (pullback.snd p i) (pullback.fst p i) i p
      (IsPullback.of_hasPullback p i).flip.toCommSq F := by
  exact comparison_underived_cube_ring (ULift.{u + 1, u} A)
    (pullback.snd p i) (pullback.fst p i) i p
    { toCommSq := (IsPullback.of_hasPullback p i).flip.toCommSq
      isoPullback := pullbackSymmetry p i
      hom_fst := by simp
      hom_snd := by simp } F

private lemma intrinsic_derived_cube
    {U V W T : Scheme.{u}} (r : U ⟶ W) (k : U ⟶ V) (i : W ⟶ T) (p : V ⟶ T)
    [IsOpenImmersion i] [IsOpenImmersion k] (sq : IsPullback r k i p)
    (K : DerivedCategory
      (Sheaf (ProEt.topology V) (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (sfIntrinsicDerivedEquivalence W A).functor.map
        ((Etale.derivedSquare (ProEtale.baseChangeMap
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq.toCommSq)).app K) ≫
      (sfIntrinsicDerivedDirectImageComparison r A).inv.app
        ((ProEtale.upperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) k).mapDerivedCategory.obj K) ≫
      (proEtaleConstantDerivedDirectImage r A).map
        ((mapDerivedCategorySquareIso (intrinsic_pullback_coordinates A k)).inv.app K) =
    (mapDerivedCategorySquareIso (intrinsic_pullback_coordinates A i)).inv.app
        ((ProEtale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj K) ≫
      (sfIntrinsicDerivedPullback A i).map
        ((sfIntrinsicDerivedDirectImageComparison p A).inv.app K) ≫
      (sfProperOpenDerivedRestriction A r k i p sq).hom.app
        ((sfIntrinsicDerivedEquivalence V A).functor.obj K) := by
  have h := Etale.derivedSquare_cube
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p)
    (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) r)
    (proEtaleConstantModuleDirectImage p A) (proEtaleConstantModuleDirectImage r A)
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) k)
    (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i)
    (sfIntrinsicPullback A k) (sfIntrinsicPullback A i)
    (sfIntrinsicModuleEquivalence V A).functor
    (sfIntrinsicModuleEquivalence T A).functor
    (sfIntrinsicModuleEquivalence U A).functor
    (sfIntrinsicModuleEquivalence W A).functor
    (ProEtale.baseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) sq.toCommSq)
    (sfProperOpenPullbackRestriction A r k i p sq).hom
    (sfIntrinsicDirectImageComparison p A).inv
    (sfIntrinsicDirectImageComparison r A).inv
    (intrinsic_pullback_coordinates A i) (intrinsic_pullback_coordinates A k)
    (intrinsic_underived_cube A r k i p sq) K
  rw [intrinsic_directImage_inv_eq_square A r, intrinsic_directImage_inv_eq_square A p,
    intrinsic_restriction_eq_square A r k i p sq]
  exact h



/- This is the exact-localization unit calculation of
`Adjunction.mapDerivedCategoryAdjunction_mate_Qh_obj`, with the two localized
adjunctions specified by their unit equations. It therefore also applies to the
intrinsic category, where the adjunction was localized directly on complexes. -/
open CategoryTheory.Adjunction in
private lemma exact_unit_square_Qh
    {C₁ D₁ C₂ D₂ : Type*}
    [Category C₁] [Category D₁] [Category C₂] [Category D₂]
    [Abelian C₁] [Abelian D₁] [Abelian C₂] [Abelian D₂]
    [HasDerivedCategory C₁] [HasDerivedCategory D₁]
    [HasDerivedCategory C₂] [HasDerivedCategory D₂]
    {f₁ : C₁ ⥤ D₁} {g₁ : D₁ ⥤ C₁} {f₂ : C₂ ⥤ D₂} {g₂ : D₂ ⥤ C₂}
    [f₁.Additive] [g₁.Additive] [f₂.Additive] [g₂.Additive]
    [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
    [PreservesFiniteLimits g₁] [PreservesFiniteColimits g₁]
    [PreservesFiniteLimits f₂] [PreservesFiniteColimits f₂]
    [PreservesFiniteLimits g₂] [PreservesFiniteColimits g₂]
    (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂)
    (ad₁ : f₁.mapDerivedCategory ⊣ g₁.mapDerivedCategory)
    (ad₂ : f₂.mapDerivedCategory ⊣ g₂.mapDerivedCategory)
    (hunit₁ : ∀ X, ad₁.unit.app (DerivedCategory.Qh.obj X) ≫
      g₁.mapDerivedCategory.map (f₁.mapDerivedCategoryFactorsh.hom.app X) ≫
      g₁.mapDerivedCategoryFactorsh.hom.app ((f₁.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X))
    (hunit₂ : ∀ X, ad₂.unit.app (DerivedCategory.Qh.obj X) ≫
      g₂.mapDerivedCategory.map (f₂.mapDerivedCategoryFactorsh.hom.app X) ≫
      g₂.mapDerivedCategoryFactorsh.hom.app ((f₂.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).unit.app X))
    (u : C₁ ⥤ C₂) (v : D₁ ⥤ D₂)
    [u.Additive] [v.Additive]
    [PreservesFiniteLimits u] [PreservesFiniteColimits u]
    [PreservesFiniteLimits v] [PreservesFiniteColimits v]
    (τ : g₁ ⋙ u ≅ v ⋙ g₂) (β : u ⋙ f₂ ≅ f₁ ⋙ v)
    (hβ : ∀ K, adj₂.unit.app (u.obj K) ≫ g₂.map (β.hom.app K) =
      u.map (adj₁.unit.app K) ≫ τ.hom.app (f₁.obj K))
    (X : HomotopyCategory C₁ (.up ℤ)) :
    ad₂.unit.app (u.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) ≫
        g₂.mapDerivedCategory.map
          ((mapDerivedCategorySquareIso β).hom.app (DerivedCategory.Qh.obj X)) =
      u.mapDerivedCategory.map (ad₁.unit.app (DerivedCategory.Qh.obj X)) ≫
        (mapDerivedCategorySquareIso τ).hom.app
          (f₁.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) := by
  -- reduce to a computation in the homotopy category
  rw [← cancel_epi (u.mapDerivedCategoryFactorsh.inv.app X),
    ← cancel_mono (g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
      (f₁.mapDerivedCategoryFactorsh.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactorsh.hom.app
        ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactorsh.hom.app
        ((v.mapHomotopyCategory (.up ℤ)).obj ((f₁.mapHomotopyCategory (.up ℤ)).obj X)))]
  -- the left hand side
  have h₁ := ad₂.unit.naturality
    (u.mapDerivedCategoryFactorsh.inv.app X)
  have h₂ := hunit₂
    ((u.mapHomotopyCategory (.up ℤ)).obj X)
  have h₃ := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj β X
  have h₄ := g₂.mapDerivedCategoryFactorsh.hom.naturality
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (u ⋙ f₂)) (.up ℤ)).hom.app X ≫
      (NatTrans.mapHomotopyCategory β.hom (.up ℤ)).app X ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (f₁ ⋙ v)) (.up ℤ)).inv.app X)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at h₁ h₄
  have h₂' : ad₂.unit.app
      (DerivedCategory.Qh.obj ((u.mapHomotopyCategory (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).unit.app
        ((u.mapHomotopyCategory (.up ℤ)).obj X)) ≫
        g₂.mapDerivedCategoryFactorsh.inv.app _ ≫
        g₂.mapDerivedCategory.map (f₂.mapDerivedCategoryFactorsh.inv.app _) := by
    rw [← h₂]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have h₃' := congrArg g₂.mapDerivedCategory.map h₃
  simp only [Functor.map_comp] at h₃'
  have hL : u.mapDerivedCategoryFactorsh.inv.app X ≫
      ad₂.unit.app
        (u.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) ≫
      g₂.mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso β).hom.app (DerivedCategory.Qh.obj X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactorsh.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactorsh.hom.app
        ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactorsh.hom.app
        ((v.mapHomotopyCategory (.up ℤ)).obj ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).unit.app
        ((u.mapHomotopyCategory (.up ℤ)).obj X) ≫ (g₂.mapHomotopyCategory (.up ℤ)).map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (u ⋙ f₂)) (.up ℤ)).hom.app X ≫
            (NatTrans.mapHomotopyCategory β.hom (.up ℤ)).app X ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (f₁ ⋙ v)) (.up ℤ)).inv.app X)) := by
    rw [reassoc_of% h₁, h₂']
    simp only [Category.assoc]
    rw [reassoc_of% h₃']
    simp only [Functor.map_comp, Category.assoc] at h₄ ⊢
    rw [h₄, Iso.inv_hom_id_app_assoc]
  -- the right hand side
  have k₁ := hunit₁ X
  have k₁' : ad₁.unit.app (DerivedCategory.Qh.obj X) =
      DerivedCategory.Qh.map ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X) ≫
        g₁.mapDerivedCategoryFactorsh.inv.app _ ≫
        g₁.mapDerivedCategory.map (f₁.mapDerivedCategoryFactorsh.inv.app _) := by
    rw [← k₁]
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    rw [← Functor.map_comp, Iso.hom_inv_id_app]
    erw [CategoryTheory.Functor.map_id, Category.comp_id]
  have k₂ := u.mapDerivedCategoryFactorsh.inv.naturality
    ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X)
  have k₃ : u.mapDerivedCategory.map (g₁.mapDerivedCategory.map
      (f₁.mapDerivedCategoryFactorsh.inv.app X)) ≫
      (Functor.mapDerivedCategorySquareIso τ).hom.app
        (f₁.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) =
      (Functor.mapDerivedCategorySquareIso τ).hom.app _ ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
          (f₁.mapDerivedCategoryFactorsh.inv.app X)) :=
    (Functor.mapDerivedCategorySquareIso τ).hom.naturality _
  have k₄ := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj τ
    ((f₁.mapHomotopyCategory (.up ℤ)).obj X)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at k₂
  have hR : u.mapDerivedCategoryFactorsh.inv.app X ≫
      u.mapDerivedCategory.map
        (ad₁.unit.app (DerivedCategory.Qh.obj X)) ≫
      (Functor.mapDerivedCategorySquareIso τ).hom.app
        (f₁.mapDerivedCategory.obj (DerivedCategory.Qh.obj X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactorsh.hom.app X)) ≫
      g₂.mapDerivedCategory.map (v.mapDerivedCategoryFactorsh.hom.app
        ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      g₂.mapDerivedCategoryFactorsh.hom.app
        ((v.mapHomotopyCategory (.up ℤ)).obj ((f₁.mapHomotopyCategory (.up ℤ)).obj X)) =
      DerivedCategory.Qh.map ((u.mapHomotopyCategory (.up ℤ)).map
        ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X) ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (g₁ ⋙ u)) (.up ℤ)).hom.app _ ≫
          (NatTrans.mapHomotopyCategory τ.hom (.up ℤ)).app _ ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (v ⋙ g₂)) (.up ℤ)).inv.app _) := by
    rw [k₁']
    simp only [Functor.map_comp, Category.assoc]
    have hc : g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
        (f₁.mapDerivedCategoryFactorsh.inv.app X)) ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map
          (f₁.mapDerivedCategoryFactorsh.hom.app X)) = 𝟙 _ := by
      rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id_app]
      erw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rw [← reassoc_of% k₂, reassoc_of% k₃, reassoc_of% hc]
    simp only [Functor.map_comp] at k₄ ⊢
    rw [k₄]
  simp only [Category.assoc]
  rw [hL, hR]
  congr 1
  clear h₁ h₂ h₃ h₄ h₂' h₃' hL k₁ k₁' k₂ k₃ k₄ hR hunit₁ hunit₂ ad₁ ad₂
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  have hu₂ : (adj₂.mapHomotopyCategory (.up ℤ)).unit.app ((u.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient C₁ (.up ℤ)).obj K)) =
      (HomotopyCategory.quotient C₂ (.up ℤ)).map ((adj₂.mapHomologicalComplex (.up ℤ)).unit.app
        ((u.mapHomologicalComplex (.up ℤ)).obj K)) :=
    mapHomotopyCategory_unit_app_quotient _ adj₂ _
  rw [hu₂, mapHomotopyCategory_unit_app_quotient]
  have hc : (adj₂.mapHomologicalComplex (.up ℤ)).unit.app
      ((u.mapHomologicalComplex (.up ℤ)).obj K) ≫
      (g₂.mapHomologicalComplex (.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso (Iso.refl (u ⋙ f₂)) (.up ℤ)).hom.app K ≫
          (NatTrans.mapHomologicalComplex β.hom (.up ℤ)).app K ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (f₁ ⋙ v)) (.up ℤ)).inv.app K) =
      (u.mapHomologicalComplex (.up ℤ)).map ((adj₁.mapHomologicalComplex (.up ℤ)).unit.app K) ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (g₁ ⋙ u)) (.up ℤ)).hom.app _ ≫
        (NatTrans.mapHomologicalComplex τ.hom (.up ℤ)).app _ ≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (v ⋙ g₂)) (.up ℤ)).inv.app _ := by
    ext n
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      mapHomologicalComplex_unit_app_f, Functor.mapHomologicalComplexCompIso_hom_app_f,
      Functor.mapHomologicalComplexCompIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
      Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
    erw [Category.id_comp, Category.id_comp, Category.comp_id, Category.comp_id]
    exact hβ (K.X n)
  have := (HomotopyCategory.quotient C₂ (.up ℤ)).congr_map hc
  simp only [Functor.map_comp] at this ⊢
  exact this

private lemma exact_unit_square
    {C₁ D₁ C₂ D₂ : Type*}
    [Category C₁] [Category D₁] [Category C₂] [Category D₂]
    [Abelian C₁] [Abelian D₁] [Abelian C₂] [Abelian D₂]
    [HasDerivedCategory C₁] [HasDerivedCategory D₁]
    [HasDerivedCategory C₂] [HasDerivedCategory D₂]
    {f₁ : C₁ ⥤ D₁} {g₁ : D₁ ⥤ C₁} {f₂ : C₂ ⥤ D₂} {g₂ : D₂ ⥤ C₂}
    [f₁.Additive] [g₁.Additive] [f₂.Additive] [g₂.Additive]
    [PreservesFiniteLimits f₁] [PreservesFiniteColimits f₁]
    [PreservesFiniteLimits g₁] [PreservesFiniteColimits g₁]
    [PreservesFiniteLimits f₂] [PreservesFiniteColimits f₂]
    [PreservesFiniteLimits g₂] [PreservesFiniteColimits g₂]
    (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂)
    (ad₁ : f₁.mapDerivedCategory ⊣ g₁.mapDerivedCategory)
    (ad₂ : f₂.mapDerivedCategory ⊣ g₂.mapDerivedCategory)
    (hunit₁ : ∀ X, ad₁.unit.app (DerivedCategory.Qh.obj X) ≫
      g₁.mapDerivedCategory.map (f₁.mapDerivedCategoryFactorsh.hom.app X) ≫
      g₁.mapDerivedCategoryFactorsh.hom.app ((f₁.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((adj₁.mapHomotopyCategory (.up ℤ)).unit.app X))
    (hunit₂ : ∀ X, ad₂.unit.app (DerivedCategory.Qh.obj X) ≫
      g₂.mapDerivedCategory.map (f₂.mapDerivedCategoryFactorsh.hom.app X) ≫
      g₂.mapDerivedCategoryFactorsh.hom.app ((f₂.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).unit.app X))
    (u : C₁ ⥤ C₂) (v : D₁ ⥤ D₂)
    [u.Additive] [v.Additive]
    [PreservesFiniteLimits u] [PreservesFiniteColimits u]
    [PreservesFiniteLimits v] [PreservesFiniteColimits v]
    (τ : g₁ ⋙ u ≅ v ⋙ g₂) (β : u ⋙ f₂ ≅ f₁ ⋙ v)
    (hβ : ∀ K, adj₂.unit.app (u.obj K) ≫ g₂.map (β.hom.app K) =
      u.map (adj₁.unit.app K) ≫ τ.hom.app (f₁.obj K))
    (K : DerivedCategory C₁) :
    ad₂.unit.app (u.mapDerivedCategory.obj K) ≫
        g₂.mapDerivedCategory.map
          ((mapDerivedCategorySquareIso β).hom.app K) =
      u.mapDerivedCategory.map (ad₁.unit.app K) ≫
        (mapDerivedCategorySquareIso τ).hom.app
          (f₁.mapDerivedCategory.obj K) := by
  have := Localization.essSurj (DerivedCategory.Qh (C := C₁)) (HomotopyCategory.quasiIso C₁ (.up ℤ))
  let e := DerivedCategory.Qh.objObjPreimageIso K
  rw [← cancel_epi (u.mapDerivedCategory.map e.hom)]
  have h₁ : u.mapDerivedCategory.map e.hom ≫
      ad₂.unit.app (u.mapDerivedCategory.obj K) =
      ad₂.unit.app (u.mapDerivedCategory.obj _) ≫
        g₂.mapDerivedCategory.map (f₂.mapDerivedCategory.map (u.mapDerivedCategory.map e.hom)) :=
    ad₂.unit.naturality _
  have h₂ : f₂.mapDerivedCategory.map (u.mapDerivedCategory.map e.hom) ≫
      (Functor.mapDerivedCategorySquareIso β).hom.app K =
      (Functor.mapDerivedCategorySquareIso β).hom.app _ ≫
        v.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom) :=
    (Functor.mapDerivedCategorySquareIso β).hom.naturality _
  have h₃ : e.hom ≫ ad₁.unit.app K =
      ad₁.unit.app _ ≫
        g₁.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom) :=
    ad₁.unit.naturality _
  have h₄ : u.mapDerivedCategory.map (g₁.mapDerivedCategory.map
      (f₁.mapDerivedCategory.map e.hom)) ≫
      (Functor.mapDerivedCategorySquareIso τ).hom.app (f₁.mapDerivedCategory.obj K) =
      (Functor.mapDerivedCategorySquareIso τ).hom.app _ ≫
        g₂.mapDerivedCategory.map (v.mapDerivedCategory.map (f₁.mapDerivedCategory.map e.hom)) :=
    (Functor.mapDerivedCategorySquareIso τ).hom.naturality _
  rw [reassoc_of% h₁, ← Functor.map_comp, h₂, Functor.map_comp, ← Functor.map_comp_assoc, h₃,
    Functor.map_comp, Category.assoc, h₄,
    reassoc_of% (exact_unit_square_Qh adj₁ adj₂ ad₁ ad₂ hunit₁ hunit₂ u v τ β hβ _)]

private def exactAdj
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R) :
    L.mapDerivedCategory ⊣ R.mapDerivedCategory :=
  letI : CatCommSq (L.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q L.mapDerivedCategory :=
    ⟨L.mapDerivedCategoryFactors.symm⟩
  letI : CatCommSq (R.mapHomologicalComplex (.up ℤ))
      DerivedCategory.Q DerivedCategory.Q R.mapDerivedCategory :=
    ⟨R.mapDerivedCategoryFactors.symm⟩
  (a.mapHomologicalComplex (.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso D (.up ℤ))
    L.mapDerivedCategory R.mapDerivedCategory

private lemma exactAdj_unit_Qh
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R)
    (X : HomotopyCategory C (.up ℤ)) :
    (exactAdj a).unit.app (DerivedCategory.Qh.obj X) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app X) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app X) := by
  obtain ⟨J, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient]
  change (exactAdj a).unit.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient C (.up ℤ)).obj J)) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient C (.up ℤ)).obj J)) ≫
      R.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((L.mapHomologicalComplex (.up ℤ)).obj J)) = _
  simp only [mapDerivedCategoryFactorsh_hom_app, mapHomotopyCategoryFactors,
    DerivedCategory.quotientCompQhIso, HomologicalComplexUpToQuasiIso.quotientCompQhIso,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
  repeat first
    | erw [CategoryTheory.Functor.map_id]
    | erw [Category.id_comp]
    | erw [Category.comp_id]
  change (exactAdj a).unit.app (DerivedCategory.Q.obj J) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app J) ≫
      R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj J) = _
  dsimp only [exactAdj]
  rw [Adjunction.localization_unit_app]
  change (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app J) ≫
      R.mapDerivedCategoryFactors.inv.app ((L.mapHomologicalComplex (.up ℤ)).obj J) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app J)) ≫
      R.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app J) ≫
      R.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj J) = _
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  rfl



private lemma etale_exchange_eq_square {V T W : Scheme.{u}}
    (p : V ⟶ T) (i : W ⟶ T) :
    Etale.exactDerivedBaseChangeMap
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        (IsPullback.of_hasPullback p i).toCommSq =
      Etale.derivedSquare (Etale.baseChangeMap
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        (IsPullback.of_hasPullback p i).toCommSq) := by
  exact Etale.derived_mate_exact_eq_square
    (Etale.upperStarLowerStarAdjunction _ p)
    (Etale.upperStarLowerStarAdjunction _ (pullback.snd p i))
    (Etale.squareUpperStarIso
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (IsPullback.of_hasPullback p i).toCommSq)

private lemma comparison_derived_cube {V T W : Scheme.{u}}
    (p : V ⟶ T) (i : W ⟶ T) [IsOpenImmersion i]
    (K : DerivedCategory
      (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) W).mapDerivedCategory.map
        ((Etale.exactDerivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (IsPullback.of_hasPullback p i).toCommSq).app K) ≫
      (Etale.derivedSquare (ProEtale.lowerStarComparisonUpperStarBaseChange (pullback.snd p i)
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))).app
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (pullback.fst p i)).mapDerivedCategory.obj K) ≫
      (ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        (pullback.snd p i)).rightDerivedFunctor.map
        ((mapDerivedCategorySquareIso
          (ProEtale.comparisonUpperStarCompUpperStarIso
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i))).inv.app K) =
    (mapDerivedCategorySquareIso
        (ProEtale.comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i)).inv.app
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj K) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).mapDerivedCategory.map
        ((Etale.derivedSquare (ProEtale.lowerStarComparisonUpperStarBaseChange p
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))).app K) ≫
      (Etale.derivedSquare
        (ProEtale.baseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (IsPullback.of_hasPullback p i).flip.toCommSq)).app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) V).mapDerivedCategory.obj K) := by
  rw [etale_exchange_eq_square A p i]
  exact Etale.derivedSquare_cube
    (Etale.lowerStar _ p) (Etale.lowerStar _ (pullback.snd p i))
    (ProEtale.lowerStar _ p) (ProEtale.lowerStar _ (pullback.snd p i))
    (Etale.upperStar _ (pullback.fst p i)) (Etale.upperStar _ i)
    (ProEtale.upperStar _ (pullback.fst p i)) (ProEtale.upperStar _ i)
    (ProEtale.comparisonUpperStar _ V) (ProEtale.comparisonUpperStar _ T)
    (ProEtale.comparisonUpperStar _ (pullback p i)) (ProEtale.comparisonUpperStar _ W)
    (Etale.baseChangeMap _ (IsPullback.of_hasPullback p i).toCommSq)
    (ProEtale.baseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
      (IsPullback.of_hasPullback p i).flip.toCommSq)
    (ProEtale.lowerStarComparisonUpperStarBaseChange p _)
    (ProEtale.lowerStarComparisonUpperStarBaseChange (pullback.snd p i) _)
    (ProEtale.comparisonUpperStarCompUpperStarIso _ i)
    (ProEtale.comparisonUpperStarCompUpperStarIso _ (pullback.fst p i))
    (fun F => (comparison_underived_cube A p i F).equation) K

private lemma directImage_component {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (etaleOriginOpenDirectImageComparison A f K).hom =
      (sfIntrinsicDerivedEquivalence Y A).functor.map
        ((Etale.derivedSquare (ProEtale.lowerStarComparisonUpperStarBaseChange f
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))).app K.obj) ≫
      (sfIntrinsicDerivedDirectImageComparison f A).inv.app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory.obj K.obj) := by
  rw [fixed_directImage_component A f K]
  simp only [etaleOriginOpenDirectImageComparison, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, NatTrans.comp_app,
    mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.comp_id, asIso_hom, Functor.map_comp, Category.assoc]
  repeat first
    | erw [CategoryTheory.Functor.map_id]
    | erw [Category.id_comp]
    | erw [Category.comp_id]


private lemma realization_open_unit
    {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
    (E : C ≌ C') (J : D ≌ D') {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R)
    (F : C) :
    (((E.symm.toAdjunction.comp a).comp J.toAdjunction).unit.app
        (E.functor.obj F)) ≫
        (J.inverse ⋙ R ⋙ E.functor).map ((E.funInvIdAssoc (L ⋙ J.functor)).hom.app F) =
      E.functor.map (a.unit.app F) ≫
        (J.funInvIdAssoc (R ⋙ E.functor)).inv.app (L.obj F) := by
  simp only [Adjunction.comp_unit_app, Equivalence.funInvIdAssoc_hom_app,
    Equivalence.funInvIdAssoc_inv_app, Equivalence.symm_unit,
    Equivalence.symm_counit, Equivalence.toAdjunction_unit, Functor.comp_map, Category.assoc]
  change E.counitIso.inv.app (E.functor.obj F) ≫
      E.functor.map (a.unit.app (E.inverse.obj (E.functor.obj F))) ≫
      E.functor.map (R.map (J.unitIso.hom.app
        (L.obj (E.inverse.obj (E.functor.obj F))))) ≫
      E.functor.map (R.map (J.inverse.map
        (J.functor.map (L.map (E.unitIso.inv.app F))))) =
    E.functor.map (a.unit.app F) ≫
      E.functor.map (R.map (J.unitIso.hom.app (L.obj F)))
  rw [Equivalence.counitInv_app_functor]
  simp only [← Functor.map_comp, Category.assoc]
  apply congrArg E.functor.map
  have hJ := J.unitIso.hom.naturality (L.map (E.unitIso.inv.app F))
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hJ
  rw [← hJ]
  simp only [Functor.map_comp, ← Category.assoc]
  have hE := a.unit.naturality (E.unitIso.hom.app F)
  dsimp only [Functor.id_map, Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hE
  rw [hE]
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]


private def conjugateAdjunction
    {C D C' D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    (E : C ≌ C') (J : D ≌ D') {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) :
    (E.inverse ⋙ L ⋙ J.functor) ⊣ (J.inverse ⋙ R ⋙ E.functor) :=
  (E.symm.toAdjunction.comp a).comp J.toAdjunction

private lemma realization_open_mate_generic
    {C D C' D' : Type*}
    [Category C] [Category D] [Category C'] [Category D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory C'] [HasDerivedCategory D']
    (E : C ≌ C') (J : D ≌ D')
    [E.functor.Additive] [E.inverse.Additive]
    [J.functor.Additive] [J.inverse.Additive]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R] (a : L ⊣ R)
    (ad : L.mapDerivedCategory ⊣ R.mapDerivedCategory)
    (hunit : ∀ X : HomotopyCategory C (.up ℤ),
      ad.unit.app (DerivedCategory.Qh.obj X) ≫
        R.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app X) ≫
        R.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj X) =
      DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).unit.app X)) :
    (mateEquiv ad (exactAdj (conjugateAdjunction E J a))
      (TwoSquare.mk _ _ _ _
        (mapDerivedCategorySquareIso (E.funInvIdAssoc (L ⋙ J.functor))).hom)).natTrans =
      (mapDerivedCategorySquareIso (J.funInvIdAssoc (R ⋙ E.functor))).inv := by
  apply Etale.mate_eq_of_unit
  intro K
  have h := exact_unit_square a (conjugateAdjunction E J a)
    ad (exactAdj (conjugateAdjunction E J a)) hunit
    (exactAdj_unit_Qh (conjugateAdjunction E J a))
    E.functor J.functor
    (J.funInvIdAssoc (R ⋙ E.functor)).symm
    (E.funInvIdAssoc (L ⋙ J.functor))
    (realization_open_unit E J a) K
  rw [← Etale.exactComparison_inv] at h
  exact h

private lemma site_open_mate {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j] :
    (mateEquiv
      (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)
      ((ProEtale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategoryAdjunction)
      (TwoSquare.mk _ _ _ _
        (mapDerivedCategorySquareIso
          (ProEtale.openImmersionLowerShriekComparisonUpperStarIso
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)).inv)).natTrans =
      (mapDerivedCategorySquareIso
        (ProEtale.comparisonUpperStarCompUpperStarIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)).inv := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  apply Etale.mate_eq_of_unit
  intro K
  have h := Adjunction.mapDerivedCategoryAdjunction_mate
    (Etale.openImmersionLowerShriekUpperStarAdjunction B j)
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction B j)
    (ProEtale.comparisonUpperStarCompUpperStarIso B j).symm
    (ProEtale.openImmersionLowerShriekComparisonUpperStarIso B j).symm
    (ProEtale.comparison_open_inverse_unit (ULift.{u + 1, u} A) j) K
  rw [← Etale.exactComparison_inv, ← Etale.exactComparison_inv] at h
  exact h

private lemma realization_open_mate {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] :
    (mateEquiv
      ((ProEtale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategoryAdjunction)
      (exceptionalOpenAdjunction j A)
      (TwoSquare.mk _ _ _ _ (etaleOriginOpenCoordinates A j).hom)).natTrans =
      (mapDerivedCategorySquareIso (intrinsic_pullback_coordinates A j)).inv := by
  exact realization_open_mate_generic
    (sfIntrinsicModuleEquivalence X A) (sfIntrinsicModuleEquivalence Y A)
    (ProEtale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)
    (Adjunction.mapDerivedCategoryAdjunction
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j))
    (Adjunction.mapDerivedCategoryAdjunction_unit_app_fac
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j))


private def directImageMap {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Etale.lowerStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor ⋙
        etaleOriginOpenComparison A Y ⟶
      etaleOriginOpenComparison A X ⋙ proEtaleConstantDerivedDirectImage f A :=
  whiskerRight (Etale.derivedSquare
    (ProEtale.lowerStarComparisonUpperStarBaseChange f
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
      (sfIntrinsicDerivedEquivalence Y A).functor ≫
    whiskerLeft (ProEtale.comparisonUpperStar
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X).mapDerivedCategory
      (sfIntrinsicDerivedDirectImageComparison f A).inv

private lemma directImage_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    (K L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (φ : K.obj ⟶ L.obj) :
    (etaleOriginOpenComparison A Y).map
        ((Etale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) f).rightDerivedFunctor.map φ) ≫
      (etaleOriginOpenDirectImageComparison A f L).hom =
    (etaleOriginOpenDirectImageComparison A f K).hom ≫
      (proEtaleConstantDerivedDirectImage f A).map
        ((etaleOriginOpenComparison A X).map φ) := by
  simp only [directImage_component]
  exact (directImageMap A f).naturality φ

end DerivedCoordinates

attribute [local irreducible] etaleOriginOpenCoordinates
  etaleOriginOpenExtensionComparison etaleOriginOpenDirectImageComparison
  sfIntrinsicModuleEquivalence sfIntrinsicExtensionByZero
  sfIntrinsicPullback exceptionalOpenAdjunction
  Etale.lowerStar Etale.upperStar Etale.openImmersionLowerShriek

/-- The open-restriction comparison is the mate of inverse open-extension comparison.
Source: Stacks Tag 09AF, the common-right-adjoint normalization
(blueprint: lem-exc-etale-origin-open-restriction-transport). -/
def etaleOriginOpenRestrictionMate {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] :
    (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
        etaleOriginOpenComparison A X ⟶
      etaleOriginOpenComparison A Y ⋙ sfIntrinsicDerivedPullback A j :=
  (mateEquiv
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)
    (exceptionalOpenAdjunction j A)
    (TwoSquare.mk _ _ _ _ (etaleOriginOpenExtensionComparison A j).inv)).natTrans


private lemma restrictionMate_component {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j]
    (K : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Y) :
    (etaleOriginOpenRestrictionMate A j).app K =
      (sfIntrinsicDerivedEquivalence X A).functor.map
        ((mapDerivedCategorySquareIso
          (ProEtale.comparisonUpperStarCompUpperStarIso
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)).inv.app K) ≫
      (mapDerivedCategorySquareIso (intrinsic_pullback_coordinates A j)).inv.app
        ((ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).mapDerivedCategory.obj K) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let σ₁ := TwoSquare.mk _ _ _ _
    (mapDerivedCategorySquareIso
      (ProEtale.openImmersionLowerShriekComparisonUpperStarIso B j)).inv
  let σ₂ := TwoSquare.mk _ _ _ _ (etaleOriginOpenCoordinates A j).hom
  have hh : TwoSquare.hComp σ₁ σ₂ =
      TwoSquare.mk _ _ _ _ (etaleOriginOpenExtensionComparison A j).inv := by
    ext M : 1
    simp [σ₁, σ₂, TwoSquare.hComp, TwoSquare.mk, TwoSquare.natTrans,
      etaleOriginOpenExtensionComparison, Iso.trans_inv, Iso.symm_inv,
      NatTrans.comp_app, isoWhiskerLeft_inv, isoWhiskerRight_inv,
      whiskerLeft_app, whiskerRight_app, Category.assoc]
    rfl
  have hs : mateEquiv
      (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction B j)
      (Adjunction.mapDerivedCategoryAdjunction
        (ProEtale.openImmersionLowerShriekUpperStarAdjunction B j)) σ₁ =
      (mapDerivedCategorySquareIso
        (ProEtale.comparisonUpperStarCompUpperStarIso B j)).inv := site_open_mate A j
  have hr : mateEquiv
      (Adjunction.mapDerivedCategoryAdjunction
        (ProEtale.openImmersionLowerShriekUpperStarAdjunction B j))
      (exceptionalOpenAdjunction j A) σ₂ =
      (mapDerivedCategorySquareIso (intrinsic_pullback_coordinates A j)).inv :=
    realization_open_mate A j
  have h := mateEquiv_vcomp
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction B j)
    (Adjunction.mapDerivedCategoryAdjunction
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction B j))
    (exceptionalOpenAdjunction j A) σ₁ σ₂
  rw [hh, hs, hr] at h
  have hK := congrArg (fun t ↦ t.natTrans.app K) h
  simpa only [B, etaleOriginOpenRestrictionMate, etaleOriginOpenComparison,
    TwoSquare.vComp, TwoSquare.mk, TwoSquare.natTrans,
    NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id] using hK


private lemma comparison_exchange_square {V T W : Scheme.{u}}
    (p : V ⟶ T) (i : W ⟶ T) [IsOpenImmersion i]
    [QuasiCompact p] [QuasiSeparated p]
    [QuasiCompact (pullback.snd p i)] [QuasiSeparated (pullback.snd p i)]
    (K : DerivedCategory.Plus
      (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (etaleOriginOpenComparison A W).map
        ((Etale.exactDerivedBaseChangeMap
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (IsPullback.of_hasPullback p i).toCommSq).app K.obj) ≫
      (etaleOriginOpenDirectImageComparison A (pullback.snd p i)
        ((Etale.upperStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
          (pullback.fst p i)).mapDerivedCategoryPlus.obj K)).hom ≫
      (proEtaleConstantDerivedDirectImage (pullback.snd p i) A).map
        ((etaleOriginOpenRestrictionMate A (pullback.fst p i)).app K.obj) =
    (etaleOriginOpenRestrictionMate A i).app
        ((Etale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj K.obj) ≫
      (sfIntrinsicDerivedPullback A i).map
        (etaleOriginOpenDirectImageComparison A p K).hom ≫
      (sfProperOpenDerivedRestriction A (pullback.snd p i) (pullback.fst p i) i p
        (IsPullback.of_hasPullback p i).flip).hom.app
        ((etaleOriginOpenComparison A V).obj K.obj) := by
  let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
  let k := pullback.fst p i
  let r := pullback.snd p i
  let N := fun Z : Scheme.{u} ↦ (ProEtale.comparisonUpperStar B Z).mapDerivedCategory
  let E := fun Z : Scheme.{u} ↦ (sfIntrinsicDerivedEquivalence Z A).functor
  let a := Etale.derivedSquare (ProEtale.lowerStarComparisonUpperStarBaseChange p B)
  let b := Etale.derivedSquare (ProEtale.lowerStarComparisonUpperStarBaseChange r B)
  let c := mapDerivedCategorySquareIso (ProEtale.comparisonUpperStarCompUpperStarIso B i)
  let d := mapDerivedCategorySquareIso (ProEtale.comparisonUpperStarCompUpperStarIso B k)
  let ci := mapDerivedCategorySquareIso (intrinsic_pullback_coordinates A i)
  let di := mapDerivedCategorySquareIso (intrinsic_pullback_coordinates A k)
  have hs := congrArg (E W).map (comparison_derived_cube A p i K.obj)
  simp only [Functor.map_comp] at hs
  have hi := intrinsic_derived_cube A r k i p
    (IsPullback.of_hasPullback p i).flip ((N V).obj K.obj)
  have hn := (sfIntrinsicDerivedDirectImageComparison r A).inv.naturality
    (d.inv.app K.obj)
  have hm := ci.inv.naturality (a.app K.obj)
  dsimp only [Functor.comp_map] at hn hm
  simp only [directImage_component, restrictionMate_component,
    etaleOriginOpenComparison, Functor.comp_map, Functor.map_comp, Category.assoc]
  dsimp only [mapDerivedCategoryPlus, ObjectProperty.lift, Functor.comp_obj]
  erw [← reassoc_of% hn]
  erw [reassoc_of% hs]
  erw [hi]
  erw [reassoc_of% hm]
  rfl

private lemma open_mate_unit
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    {G : C ⥤ E} {H : D ⥤ F}
    (a : L ⊣ R) (b : L' ⊣ R') (e : L ⋙ H ≅ G ⋙ L') (K : C) :
    G.map (a.unit.app K) ≫
        (mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)).app (L.obj K) ≫
        R'.map (e.hom.app K) = b.unit.app (G.obj K) := by
  rw [← Category.assoc, unit_mateEquiv]
  simp only [TwoSquare.mk, Functor.id_obj, Category.assoc, ← R'.map_comp,
    Iso.inv_hom_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private lemma restriction_mate_unit {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (K : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X) :
    (etaleOriginOpenComparison A X).map
        ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).unit.app K) ≫
      (etaleOriginOpenRestrictionMate A j).app
        ((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory.obj K) ≫
      (sfIntrinsicDerivedPullback A j).map
        ((etaleOriginOpenExtensionComparison A j).hom.app K) =
    (exceptionalOpenAdjunction j A).unit.app ((etaleOriginOpenComparison A X).obj K) := by
  exact open_mate_unit
    (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)
    (exceptionalOpenAdjunction j A) (etaleOriginOpenExtensionComparison A j) K

/-- Compare the direct image of an open extension, inserting the specified D+ inclusion
comparisons. Every factor is one of the fixed canonical comparisons.
Source: retained blueprint Step 7, final two arrows and their D+ coordinates
(blueprint: lem-exc-etale-origin-open-restriction-transport). -/
def etaleOriginOpenTargetComparison {V T W : Scheme.{u}}
    (p : V ⟶ T) (i : W ⟶ T) [IsOpenImmersion i]
    [QuasiCompact p] [QuasiSeparated p]
    (K : DerivedCategory.Plus
      (Sheaf (pullback p i).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (etaleOriginOpenComparison A T).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)).mapDerivedCategory.obj
              K.obj)) ≅
      (proEtaleConstantDerivedDirectImage p A).obj
        ((sfIntrinsicDerivedOpen A (pullback.fst p i)).obj
          ((etaleOriginOpenComparison A (pullback p i)).obj K.obj)) :=
  let ke := Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)
  let pe := Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p
  (etaleOriginOpenComparison A T).mapIso
      (pe.rightDerivedFunctor.mapIso (ke.mapDerivedCategoryPlusCompatibility.app K).symm) ≪≫
    etaleOriginOpenDirectImageComparison A p (ke.mapDerivedCategoryPlus.obj K) ≪≫
    (proEtaleConstantDerivedDirectImage p A).mapIso
      ((etaleOriginOpenComparison A V).mapIso (ke.mapDerivedCategoryPlusCompatibility.app K) ≪≫
        (etaleOriginOpenExtensionComparison A (pullback.fst p i)).app K.obj)

/-- Canonical comparison carries inverse normalized etale open restriction to inverse
normalized intrinsic pro-etale open restriction. The assertion applies to any qcqs map,
any open immersion, and any bounded-below input; it does not use a proper/open interchange.
The etale isomorphism is fixed by its displayed exchange-and-inverse-unit formula.
Source: retained blueprint Step 7, restriction and mate-pasting calculation; Stacks
Tags 099R, 09AF and 09BN
(blueprint: lem-exc-etale-origin-open-restriction-transport).

Proof:
1. On sheaves, identify restriction of a direct image with direct image of restriction
   by evaluating on the same Cartesian fibre product. The constant scalar sections and
   their actions agree. The etale/pro-etale comparison and the intrinsic realization
   respect this section map, by their scalar-section normalization.
2. Restriction is right adjoint to exact open extension, so it preserves K-injectives.
   Derive the section square on K-injective representatives. The canonical comparison
   of direct images is its counit-normalized mate; uniqueness of right derivation gives
   the square with the specified D+ inclusion comparisons on its four edges.
3. The mate of inverse open-extension comparison is the canonical restriction
   comparison, by openComparison_unit_normalization. Exact termwise localization and
   canonical realization preserve this mate identity and both open units.
4. Apply the derived restriction square to the open extension of K. Replace its etale
   restriction followed by inverse open unit by lam.hom, using hlam. The corresponding
   pro-etale composite is the inverse of proEtaleOpenRestrictionLambdaInverse. Insert
   the unit equation from step 3 at the top open edge. Invert the two restriction
   isomorphisms and cancel their open units. The resulting square is the displayed
   equation, including all D+ compatibility factors in etaleOriginOpenTargetComparison.
   These calculations are natural and also apply to empty opens and the zero ring. -/
theorem etaleOriginOpenRestriction_transport {V T W : Scheme.{u}}
    (p : V ⟶ T) (i : W ⟶ T) [IsOpenImmersion i]
    [QuasiCompact p] [QuasiSeparated p]
    [QuasiCompact (pullback.snd p i)] [QuasiSeparated (pullback.snd p i)]
    (K : DerivedCategory.Plus
      (Sheaf (pullback p i).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (lam :
      (Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) i).mapDerivedCategory.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).rightDerivedFunctor.obj
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)).mapDerivedCategory.obj
              K.obj)) ≅
      (Etale.lowerStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.snd p i)).rightDerivedFunctor.obj
          K.obj)
    (hlam : lam.hom =
      (Etale.exactDerivedBaseChangeMap (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
        (IsPullback.of_hasPullback p i).toCommSq).app
          ((Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)).mapDerivedCategory.obj
              K.obj) ≫
        (Etale.lowerStar
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.snd p i)).rightDerivedFunctor.map
            (inv ((Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction
              (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) (pullback.fst p i)).unit.app K.obj))) :
    (etaleOriginOpenComparison A W).map lam.inv ≫
        (etaleOriginOpenRestrictionMate A i).app _ ≫
          (sfIntrinsicDerivedPullback A i).map (etaleOriginOpenTargetComparison A p i K).hom =
      (etaleOriginOpenDirectImageComparison A (pullback.snd p i) K).hom ≫
        (proEtaleOpenRestrictionLambdaInverse p i A).app
          ((etaleOriginOpenComparison A (pullback p i)).obj K.obj) := by
  let r := pullback.snd p i
  let k := pullback.fst p i
  let M := (etaleOriginOpenComparison A (pullback p i)).obj K.obj
  let ρ := sfProperOpenDerivedRestriction A r k i p
    (IsPullback.of_hasPullback p i).flip
  have hs :
      (etaleOriginOpenComparison A W).map lam.hom ≫
          (etaleOriginOpenDirectImageComparison A r K).hom ≫
          (proEtaleConstantDerivedDirectImage r A).map
            ((exceptionalOpenAdjunction k A).unit.app M) =
        (etaleOriginOpenRestrictionMate A i).app _ ≫
          (sfIntrinsicDerivedPullback A i).map
            (etaleOriginOpenTargetComparison A p i K).hom ≫
          ρ.hom.app ((sfIntrinsicDerivedOpen A k).obj M) := by
    let B := ModuleCat.{u + 1} (ULift.{u + 1, u} A)
    let ke := Etale.openImmersionLowerShriek B k
    let kr := Etale.upperStar B k
    let L := ke.mapDerivedCategoryPlus.obj K
    let η := (Etale.derivedOpenImmersionLowerShriekUpperStarAdjunction B k).unit.app K.obj
    have hu := restriction_mate_unit A k K.obj
    have hu' : (etaleOriginOpenComparison A (pullback p i)).map (inv η) ≫
        (exceptionalOpenAdjunction k A).unit.app M =
      (etaleOriginOpenRestrictionMate A k).app (ke.mapDerivedCategory.obj K.obj) ≫
        (sfIntrinsicDerivedPullback A k).map
          ((etaleOriginOpenExtensionComparison A k).hom.app K.obj) := by
      rw [← hu]
      dsimp only [η, B]
      simp only [← Category.assoc, ← Functor.map_comp]
      erw [IsIso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    have hx := comparison_exchange_square A p i L
    have hn := ρ.hom.naturality
      ((etaleOriginOpenExtensionComparison A k).hom.app K.obj)
    dsimp only [Functor.comp_map] at hn
    rw [hlam, Functor.map_comp]
    simp only [Category.assoc]
    erw [reassoc_of% (directImage_naturality A r (kr.mapDerivedCategoryPlus.obj L) K
      (inv η))]
    rw [← (proEtaleConstantDerivedDirectImage r A).map_comp, hu',
      (proEtaleConstantDerivedDirectImage r A).map_comp]
    erw [reassoc_of% hx]
    erw [← hn]
    simp only [etaleOriginOpenTargetComparison, mapDerivedCategoryPlusCompatibility,
      Iso.refl_hom, Iso.refl_inv, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, NatTrans.id_app,
      Functor.map_comp, Category.assoc]
    repeat first
      | erw [CategoryTheory.Functor.map_id]
      | erw [Category.id_comp]
      | erw [Category.comp_id]
    rfl
  apply (cancel_epi ((etaleOriginOpenComparison A W).map lam.hom)).1
  simp only [← Category.assoc, ← Functor.map_comp, Iso.hom_inv_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  dsimp only [proEtaleOpenRestrictionLambdaInverse, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app]
  simp only [Category.assoc]
  rw [reassoc_of% hs]
  erw [Iso.hom_inv_id_app, Category.comp_id]

end AlgebraicGeometry.Scheme
