/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionData.LocallyClosedExtensionCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
public import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
public import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
public import WeilConjectures.Compactification.Over
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
public import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleLisseModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleExtensionIso
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
public import Mathlib.CategoryTheory.Triangulated.Generators
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
public import WeilConjectures.ConstructibleSheaf.OpenClosed
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSheafConeWitness
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantModelLocalResolution
public import WeilConjectures.ProperBaseChange.IntegralLfpLocallyFreeResolution
public import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
public import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import Mathlib.Topology.Defs.Filter
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
public import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedOpenClosedInternalHomMaps
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsUnit
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Normalization of the open scalar comparison

Source: latest blueprint, det-lem-int-tensor-projection.proof.md, open and derived
paragraphs, and scalar-six-pullback proof (2); Stacks 09BN.
(blueprint: lem-sfb-immersion-open-scalar-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.CondensedRing

set_option maxHeartbeats 1600000 in
-- Elaborating the specified internal-module adjunctions involves large structural types.
private theorem coextend_unit_hom (Λ : ScalarSixRing.{u})
    {S Z : Scheme.{u}} (j : S ⟶ Z) [IsOpenImmersion j]
    (M : supportModules Λ.X S) :
    ((Mod.restrictCoextendAdjunction (condensedPullbackHom Λ.X j)).unit.app M).hom ≫
      ((Mod.coextendScalarsIsoComapInv (condensedPullbackHom Λ.X j)).hom.app
        ((Mod.comap (condensedPullbackHom Λ.X j)).obj M)).hom = 𝟙 M.X := by
  let φ := condensedPullbackHom Λ.X j
  have h := congrArg Mod.Hom.hom
    (Adjunction.unit_rightAdjointUniq_hom_app (Mod.restrictCoextendAdjunction φ)
      (Mod.comapEquivalenceOfIsIso φ).toAdjunction M)
  have hi := Mod.comapEquivalenceOfIsIso_unitIso_inv_app_hom φ M
  have hh := congrArg Mod.Hom.hom
    ((Mod.comapEquivalenceOfIsIso φ).unitIso.hom_inv_id_app M)
  simp only [Mod.comp_hom', Mod.id_hom', hi, Category.comp_id] at hh
  exact h.trans hh

set_option maxHeartbeats 1600000 in
-- Elaborating the specified internal-module adjunctions involves large structural types.
private theorem open_unit_hom (Λ : ScalarSixRing.{u})
    {S Z : Scheme.{u}} (j : S ⟶ Z) [IsOpenImmersion j]
    (M : supportModules Λ.X S) :
    ((openImmersionLowerShriekUpperStarAdjunction Λ.X j).unit.app M).hom =
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).unit.app M.X ≫
        ((Mod.extendRestrictAdjunction (condensedPullbackHom Λ.X j)).unit.app
          (((ProEtale.upperStar Ab.{u + 1} j).mapMod (condensedRingObj Λ.X Z)).obj
            ((openImmersionLowerShriek Λ.X j).obj M))).hom := by
  let φ := condensedPullbackHom Λ.X j
  let η := (linearOpenImmersionLowerShriekAdjunction Λ.X j).unit.app
    ((Mod.comap φ).obj M)
  have hn := congrArg Mod.Hom.hom
    ((Mod.coextendScalarsIsoComapInv φ).hom.naturality η)
  simp only [Mod.comp_hom', Mod.comap_map_hom] at hn
  have h := congrArg (fun t ↦
    ((Mod.restrictCoextendAdjunction φ).unit.app M).hom ≫ t) hn
  have he :
      ((Mod.restrictCoextendAdjunction φ).unit.app M).hom ≫
        ((Mod.coextendScalars φ).map η).hom ≫
          ((Mod.coextendScalarsIsoComapInv φ).hom.app _).hom = η.hom := by
    exact h.trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (fun t ↦ t ≫ η.hom) (coextend_unit_hom Λ j M)).trans
        (Category.id_comp η.hom)))
  have he' := congrArg (fun t ↦ t ≫
    ((Mod.extendScalarsIsoComapInv φ).inv.app _).hom) he
  have hη : η.hom =
      (ProEtale.openImmersionLowerShriekUpperStarAdjunction Ab.{u + 1} j).unit.app M.X := by
    simp only [η, linearOpenImmersionLowerShriekAdjunction,
      Adjunction.mapModLeftAdjunction_unit_app_hom]
    rfl
  rw [hη, Mod.extendScalarsIsoComapInv_inv_app_hom] at he'
  simp only [Category.assoc] at he'
  simp only [openImmersionLowerShriekUpperStarAdjunction,
    Adjunction.unit_ofNatIsoRight_app, Adjunction.comp_unit_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Mod.comp_hom', Mod.extendScalarsIsoCoextendScalars, Iso.trans_inv,
    NatTrans.comp_app, Iso.symm_inv, Category.assoc]
  exact he'

set_option maxHeartbeats 1600000 in
-- Elaborating the specified internal-module adjunctions involves large structural types.
private theorem open_comap_inv_hom {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {S Z : Scheme.{u}} (j : S ⟶ Z) [IsOpenImmersion j]
    (M : supportModules Λ'.X S) :
    ((comapOpenImmersionLowerShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j).inv.app
      M).hom = 𝟙 _ := by
  simp only [comapOpenImmersionLowerShriekIso, Iso.trans_inv, NatTrans.comp_app,
    Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_inv,
    Mod.comp_hom', Mod.id_hom', Mod.comapComp_hom_app_hom,
    Mod.comapComp_inv_app_hom, Mod.comapCongr_inv_app_hom,
    Functor.ProjectionFormula.mapModLeftComapIso, NatIso.ofComponents_inv_app,
    Mod.isoMk_inv_hom,
    linearOpenImmersionLowerShriek, Functor.ProjectionFormula.mapModLeft_map_hom]
  erw [CategoryTheory.Functor.map_id, Iso.refl_inv]
  repeat erw [Category.comp_id]
  rfl

set_option maxHeartbeats 1600000 in
-- Elaborating the specified internal-module adjunctions involves large structural types.
private theorem ordinary_unit_square {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {S Z : Scheme.{u}} (j : S ⟶ Z) [IsOpenImmersion j]
    (M : supportModules Λ'.X S) :
    (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom S)).map
        ((openImmersionLowerShriekUpperStarAdjunction Λ'.X j).unit.app M) ≫
      (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j).hom.app
        ((openImmersionLowerShriek Λ'.X j).obj M) =
      (openImmersionLowerShriekUpperStarAdjunction Λ.X j).unit.app
          ((Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom S)).obj M) ≫
        (upperStar Λ.X j).map
          ((comapOpenImmersionLowerShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j).inv.app M) := by
  apply Mod.hom_ext
  simp only [Mod.comp_hom', Mod.comap_map_hom, open_unit_hom]
  rw [Category.assoc, extendUnit_comapUpperStarIso_hom_app_hom (Λ := Λ.X) (Λ' := Λ'.X)]
  simp only [Mod.extendRestrictAdjunction_unit_app_hom]
  change _ = _ ≫ (Mod.extendUnitHom (condensedPullbackHom Λ.X j) _ ≫
    (Mod.extendScalarsMap (condensedPullbackHom Λ.X j)
      (((ProEtale.upperStar Ab.{u + 1} j).mapMod _).map
        ((comapOpenImmersionLowerShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j).inv.app M))).hom)
  erw [Mod.extendUnitHom_extendScalarsMap, Functor.mapMod_map_hom,
    open_comap_inv_hom, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

set_option maxHeartbeats 1600000 in
-- Elaborating the specified internal-module adjunctions involves large structural types.
private theorem derived_unit_square {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {S Z : Scheme.{u}} (j : S ⟶ Z) [IsOpenImmersion j]
    (M : DerivedCategory (supportModules Λ'.X S)) :
    (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom S)).mapDerivedCategory.map
        ((derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X j).unit.app M) ≫
      (derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j).hom.app
        ((openImmersionLowerShriek Λ'.X j).mapDerivedCategory.obj M) =
      (derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j).unit.app
          ((Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom S)).mapDerivedCategory.obj
            M) ≫
        (upperStar Λ.X j).mapDerivedCategory.map
          ((Functor.mapDerivedCategorySquareIso
            (comapOpenImmersionLowerShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j)).inv.app M) := by
  have h := Adjunction.mapDerivedCategoryAdjunction_mate
    (openImmersionLowerShriekUpperStarAdjunction Λ'.X j)
    (openImmersionLowerShriekUpperStarAdjunction Λ.X j)
    (comapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j)
    (comapOpenImmersionLowerShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j).symm
    (fun N ↦ (ordinary_unit_square a j N).symm) M
  have hs : (Functor.mapDerivedCategorySquareIso
      (comapOpenImmersionLowerShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j).symm).hom =
      (Functor.mapDerivedCategorySquareIso
        (comapOpenImmersionLowerShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j)).inv := by
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
      Iso.symm_hom, Iso.symm_inv, Functor.mapDerivedCategoryNatIso_symm,
      Category.assoc]
  rw [hs] at h
  exact h.symm

set_option maxHeartbeats 1600000 in
-- Elaborating the specified internal-module adjunctions involves large structural types.
/-- The scalar transpose of the literal open action square is the specified open conjugate.
Source: latest blueprint, immersion tensor projection proof, open coefficient normalization;
scalar-six-pullback proof (2); Stacks 09BN.
(blueprint: lem-sfb-immersion-open-scalar-normalization).

Proof: write J,J' for open extension, r,r' for restriction, V for scalar restriction,
d : J' V_Z = V_S J for the literal action comparison and e : r' V_S = V_Z r for the
published pullback comparison. First verify, for each new-coefficient sheaf M, the unit
identity V_S(eta'_M) followed by e at J'M equals eta at V_SM followed by r(d_M inverse).
The comparison d is identity on underlying sheaves. To compute the open units, expand
their specified composition with coextension along the invertible structural ring map.
The right-adjoint uniqueness unit equation identifies the coextension/restriction unit
with the identity after coextendScalarsIsoComapInv. Its composition with the inverse
extension/restriction comparison is the ordinary extension unit. The remaining equation
is extendUnit_comapUpperStarIso_hom_app_hom, precomposed with the abelian open unit.

The ordinary unit identity identifies the inverse geometric mate of the published
pullback comparison with the inverse literal action square. Exact localization
preserves this mate equation, with the specified functor factorizations. Injectivity
of the geometric Hom bijection therefore identifies the inner inverse mate on the
derived category. Apply the iterated mate/conjugate identity to the open and coefficient
adjunctions. The scalar adjunct of the resulting geometric conjugate is open extension
of the scalar unit followed by the inverse literal action square. This is exactly the
defining adjunct of immersionOpenScalarMap. Injectivity of the scalar Hom bijection
proves the equality on every unbounded object.
No coefficient flatness, nonemptiness, or boundedness is used. -/
theorem immersionOpenScalarNormalization {Λ Λ' : ScalarSixRing.{u}} (a : Λ ⟶ Λ')
    {S Z : Scheme.{u}} (j : S ⟶ Z) [IsOpenImmersion j]
    (L : DerivedCategory (supportModules Λ.X S)) :
    immersionOpenScalarMap a j L =
      (derivedOpenImmersionShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j).hom.app L := by
  let x := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom S)
  let z := Mod.derivedExtendMapDerivedCategoryAdjunction
    (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)
  let o := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ.X j
  let o' := derivedOpenImmersionLowerShriekUpperStarAdjunction Λ'.X j
  let e := derivedComapUpperStarIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j
  let d := Functor.mapDerivedCategorySquareIso
    (comapOpenImmersionLowerShriekIso (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom j)
  let δ := (mateEquiv o' o).symm (TwoSquare.mk _ _ _ _ e.hom)
  have hδ : δ.natTrans = d.inv := by
    ext M
    apply (o.homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit]
    exact (unit_mateEquiv_symm o' o (TwoSquare.mk _ _ _ _ e.hom) M).symm.trans
      (derived_unit_square a j M)
  have hit := congrArg TwoSquare.natTrans
    (iterated_mateEquiv_conjugateEquiv_symm x z o o'
      (TwoSquare.mk _ _ _ _ e.hom))
  have hmap : immersionOpenScalarMap a j L =
      ((mateEquiv x z).symm δ).natTrans.app L := by
    apply (z.homEquiv _ _).injective
    change (z.homEquiv _ _) ((z.homEquiv _ _).symm
      ((openImmersionLowerShriek Λ.X j).mapDerivedCategory.map (x.unit.app L) ≫
        d.inv.app ((scalarSixChange a S).obj L))) = _
    rw [Equiv.apply_symm_apply]
    change _ = z.unit.app _ ≫
      (Mod.comap (coefficientMap (Λ := Λ.X) (Λ' := Λ'.X) a.hom.hom Z)).mapDerivedCategory.map
        (((mateEquiv x z).symm δ).natTrans.app L)
    exact (congrArg (fun t ↦
      (openImmersionLowerShriek Λ.X j).mapDerivedCategory.map (x.unit.app L) ≫
        t.app ((scalarSixChange a S).obj L)) hδ.symm).trans
      (unit_mateEquiv_symm x z δ L)
  rw [hmap]
  exact congrArg (fun t ↦ t.app L) hit

end AlgebraicGeometry.ProEtale.CondensedRing
