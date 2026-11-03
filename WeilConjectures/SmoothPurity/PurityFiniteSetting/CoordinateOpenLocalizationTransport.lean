/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateBoundaryModel.CoordinateBoundaryGeometricPullbackDefs
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateBoundaryFromOpen
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinatePuncturedClassTransport
import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateOpenUnderivedTransport
import WeilConjectures.SmoothPurity.PurityFiniteSetting.CoordinateKummerPullbackAux
import all Mathlib.CategoryTheory.Iso
import all Mathlib.CategoryTheory.Equivalence
import all Mathlib.CategoryTheory.Limits.HasLimits
import all Mathlib.Logic.Small.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChangeComp
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp

/-! # Localization of coordinate section transport
Source: Milne Section 9, restriction to the complementary open.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option maxRecDepth 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

attribute [local implicit_reducible] Scheme.Etale Scheme.Hom.Etale Scheme.instCategoryEtale
  MorphismProperty MorphismProperty.Comma.instCategory Etale.lowerStar
  Functor.sheafPushforwardContinuous

/-- The specified map from punctured global cohomology to complement-object
cohomology on the ambient line. It uses the inverse of the actual pure-tensor
coefficient comparison, derived localization, and the unique over-line complement
isomorphism. Source: Milne Section 9
(blueprint: aux-lem-pur-coordinate-open-localization-transport). -/
def coordinateOpenPresentation (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    (eU : Scheme.Etale.mk (openImmersion Y) ≅
      Scheme.Etale.mk (zeroSection Y).openComplement.ι) :
    (Sheaf.sectionHypercohomologyFunctor (Punctured Y).smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient) (Scheme.Etale.mk (𝟙 (Punctured Y))) 1).obj
        (P.coordinateEtaleInput h (Punctured Y)) ⟶
    (Sheaf.sectionHypercohomologyFunctor (Line Y).smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)
      (Scheme.Etale.mk (zeroSection Y).openComplement.ι) 1).obj
        (P.coordinateEtaleInput h (Line Y)) := by
  let j := openImmersion Y
  let E := Etale.sectionsFunctor (ModuleCat.{u + 1} P.Coefficient) (Punctured Y)
  let := P.isIso_twistEtalePullback h j
    (P.exponent_isUnit (Line Y) (lineProjection Y ≫ a))
  let b := (DerivedCategory.Plus.singleFunctor _ 0).map
      (CategoryTheory.inv (P.twistEtalePullback h j)) ≫
    (Functor.mapDerivedCategoryPlusSingleFunctor
      (Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) j) 0).inv.app
        (P.twistEtale h (Line Y))
  exact (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) 1).map
      (E.rightDerivedFunctorPlus.map b ≫
        (P.coordinateOpenDerivedIso j).hom.app (P.coordinateEtaleInput h (Line Y))) ≫
    (Functor.isoWhiskerRight
      (Functor.rightDerivedFunctorPlusNatIso
        (F := sheafToPresheaf (Line Y).smallEtaleTopology
          (ModuleCat.{u + 1} P.Coefficient) ⋙
            (evaluation _ _).obj (op (Scheme.Etale.mk (openImmersion Y))))
        (G := sheafToPresheaf (Line Y).smallEtaleTopology
          (ModuleCat.{u + 1} P.Coefficient) ⋙
            (evaluation _ _).obj (op (Scheme.Etale.mk (zeroSection Y).openComplement.ι)))
        ((sheafSections (Line Y).smallEtaleTopology
          (ModuleCat.{u + 1} P.Coefficient)).mapIso eU.op).symm)
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) 1)).hom.app
        (P.coordinateEtaleInput h (Line Y))

/-- The open class is the image of the actual punctured Kummer evaluation under
the specified localization map. Source: the coordinate boundary definition.
Proof: expand the two definitions; morphism composition is function composition.
(blueprint: aux-lem-pur-coordinate-open-localization-transport). -/
theorem coordinateEtaleOpenClass_presentation (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    (eU : Scheme.Etale.mk (openImmersion Y) ≅
      Scheme.Etale.mk (zeroSection Y).openComplement.ι) :
    P.coordinateEtaleOpenClass h Y a eU =
      P.coordinateOpenPresentation h Y a eU
        (P.coordinateClassSection (Punctured Y) (P.twistEtale h (Punctured Y))
          (P.coordinateEtaleKummer h Y a)) := by
  rfl

private instance sectionFunctor_additive (P : PurityFiniteSetting.{u})
    (X : Scheme.{u}) (V : X.Etale) :
    ((sheafSections X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient)).obj
      (op V)).Additive := by
  change (sheafToPresheaf X.smallEtaleTopology (ModuleCat.{u + 1} P.Coefficient) ⋙
    (evaluation _ _).obj (op V)).Additive
  infer_instance

private theorem compositionIso_change
    {B M D : Type*} [Category* B] [Category* M] [Category* D]
    [Abelian B] [Abelian M] [Abelian D]
    [HasDerivedCategory B] [HasDerivedCategory M] [HasDerivedCategory D]
    [EnoughInjectives B] [EnoughInjectives M]
    (J : B ⥤ M) (E : M ⥤ D) (H H' : B ⥤ D)
    [J.Additive] [E.Additive] [H.Additive] [H'.Additive]
    [J.PreservesInjectiveObjects] (c : J ⋙ E ≅ H) (d : H ≅ H') :
    (Functor.rightDerivedFunctorPlusCompIso' J E (c ≪≫ d)).hom =
      (Functor.rightDerivedFunctorPlusCompIso' J E c).hom ≫
        (Functor.rightDerivedFunctorPlusNatIso d).hom := by
  simp only [Functor.rightDerivedFunctorPlusCompIso', Iso.trans_hom, Iso.symm_hom,
    Category.assoc]
  congr 1
  simp only [Functor.rightDerivedFunctorPlusNatIso,
    Functor.rightDerivedFunctorPlusNatTrans, Functor.rightDerivedNatTrans_comp,
    ← Functor.whiskerRight_comp, ← NatTrans.mapHomotopyCategoryPlus_comp]
  rfl

private theorem coordinateOpenPresentation_augmented (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (Y : Scheme.{u})
    (a : Y ⟶ Spec (CommRingCat.of P.field.k))
    (eU : Scheme.Etale.mk (openImmersion Y) ≅
      Scheme.Etale.mk (zeroSection Y).openComplement.ι) :
    let J := Etale.upperStar (ModuleCat.{u + 1} P.Coefficient) (openImmersion Y)
    let E := Etale.sectionsFunctor (ModuleCat.{u + 1} P.Coefficient) (Punctured Y)
    let c := P.coordinateOpenSectionsIso (openImmersion Y) ≪≫
      ((sheafSections (Line Y).smallEtaleTopology
        (ModuleCat.{u + 1} P.Coefficient)).mapIso eU.op).symm
    let := (Etale.openImmersionLowerShriekUpperStarAdjunction
      (ModuleCat.{u + 1} P.Coefficient)
      (openImmersion Y)).preservesInjectiveObjects_of_preservesFiniteLimits
    let := P.isIso_twistEtalePullback h (openImmersion Y)
      (P.exponent_isUnit (Line Y) (lineProjection Y ≫ a))
    P.coordinateOpenPresentation h Y a eU =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) 1).map
        (E.rightDerivedFunctorPlus.map
          ((DerivedCategory.Plus.singleFunctor _ 0).map
            (CategoryTheory.inv (P.twistEtalePullback h (openImmersion Y))) ≫
              J.rightDerivedPlusSingleUnit (P.twistEtale h (Line Y))) ≫
          (Functor.rightDerivedFunctorPlusCompIso' J E c).hom.app
            (P.coordinateEtaleInput h (Line Y))) := by
  intro J E c
  let := P.isIso_twistEtalePullback h (openImmersion Y)
    (P.exponent_isUnit (Line Y) (lineProjection Y ≫ a))
  let := (Etale.openImmersionLowerShriekUpperStarAdjunction
    (ModuleCat.{u + 1} P.Coefficient)
    (openImmersion Y)).preservesInjectiveObjects_of_preservesFiniteLimits
  have hu := Functor.coordinateExact_single_unit J (P.twistEtale h (Line Y))
  have hu' : (J.mapDerivedCategoryPlusSingleFunctor 0).inv.app
        (P.twistEtale h (Line Y)) ≫
      J.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app
        (P.coordinateEtaleInput h (Line Y)) =
    J.rightDerivedPlusSingleUnit (P.twistEtale h (Line Y)) := by
    apply (cancel_mono (J.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
      (P.coordinateEtaleInput h (Line Y)))).1
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact hu.symm
  dsimp only [coordinateOpenPresentation, coordinateOpenDerivedIso]
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  erw [← Functor.map_comp]
  have hc := compositionIso_change J E _ _
    (P.coordinateOpenSectionsIso (openImmersion Y))
    (((sheafSections (Line Y).smallEtaleTopology
      (ModuleCat.{u + 1} P.Coefficient)).mapIso eU.op).symm)
  dsimp only [c]
  rw [hc]
  simp only [NatTrans.comp_app, Functor.map_comp]
  have hh := congrArg (fun z ↦
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) 1).map
      (E.rightDerivedFunctorPlus.map z)) hu'
  simp only [Functor.map_comp] at hh
  have hh' := congrArg (fun z ↦
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) 1).map
      (E.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor _ 0).map
          (CategoryTheory.inv (P.twistEtalePullback h (openImmersion Y))))) ≫ z ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) 1).map
        ((Functor.rightDerivedFunctorPlusCompIso' J E
          (P.coordinateOpenSectionsIso (openImmersion Y))).hom.app
          (P.coordinateEtaleInput h (Line Y))) ≫
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} P.Coefficient) 1).map
        ((Functor.rightDerivedFunctorPlusNatIso
          (((sheafSections (Line Y).smallEtaleTopology
            (ModuleCat.{u + 1} P.Coefficient)).mapIso eU.op).symm)).hom.app
            (P.coordinateEtaleInput h (Line Y)))) hh
  simpa only [Category.assoc] using! hh'

set_option maxHeartbeats 2400000 in
-- The comparison expands two derived composition isomorphisms and their coefficient maps.
end WeilConjectures.PurityFiniteSetting
