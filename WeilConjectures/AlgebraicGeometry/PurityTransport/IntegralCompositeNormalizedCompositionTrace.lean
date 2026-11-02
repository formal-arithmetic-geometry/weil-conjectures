/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
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
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
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
public import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
public import WeilConjectures.Compactification.BaseChange
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
public import WeilConjectures.CategoryTheory.CompactObject
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingEtaleCompactGenerators
public import Mathlib.Algebra.CharP.CharAndCard
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTowerCoefficients
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTrace
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1Triangle
public import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafClosedLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafBaseChangeMates
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
public import WeilConjectures.AlgebraicGeometry.PurityTransport.Transport
public import WeilConjectures.AlgebraicGeometry.Picard.Purity.Condensed.NativeCompactSupportWeilTransport
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
public import WeilConjectures.AlgebraicGeometry.SepFinType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedFrobeniusComparisonCoherence
public import WeilConjectures.AlgebraicGeometry.PurityCoefficientChange.CondensedPurityCoefficientChange
public import WeilConjectures.SixFunctors.FiniteFieldDatum.FrobeniusSquareCartesian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportLinePull
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportPull
public import WeilConjectures.AlgebraicGeometry.RationalP1.Tate.RationalTateLineComposition
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsComapUnit
public import WeilConjectures.Compactification.CommonDenseRefinement
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.Compactification.NagataCompactification

/-! # Integral normalized trace on generated composite compactifications

This is the whole-tower realization step before arbitrary compactification
refinement.  The latter is isolated in `IntegralNormalizedTraceRefinement`.
(blueprint: lem-pur-integral-normalized-composition-trace)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  HasDerivedCategory.ofHasKInjectiveResolutions HasDerivedCategory.standard
namespace AlgebraicGeometry.ProEtale.PurityTransport

end AlgebraicGeometry.ProEtale.PurityTransport

namespace AlgebraicGeometry.ProEtale.CondensedRing

-- The exact/total-derived comparison, as in condensedTowerCompositor_normalization.
private theorem exactAdjunction_eq_finiteTrace
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (derivedUpperStarLowerStarAdjunction Λ f).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory Λ f) =
      (upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction := by
  have hd : derivedUpperStarLowerStarAdjunction Λ f =
      ((upperStarLowerStarAdjunction Λ f).mapDerivedCategoryRightDerivedAdjunction).ofNatIsoLeft
        (leftDerivedUpperStarIsoMapDerivedCategory Λ f).symm := by
    exact Adjunction.derived_eq_ofNatIsoLeft _ _ _ _ _ _
      (leftDerivedUpperStarIsoMapDerivedCategory Λ f)
      (Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac (upperStar Λ f)).symm
  rw [hd]
  apply Adjunction.ext
  ext M
  simp [Adjunction.ofNatIsoLeft_unit, ← Functor.map_comp, Category.assoc]

private theorem conjugateTransport_finiteTrace
    {C D : Type*} [Category C] [Category D]
    {L₁ L₂ L₁' L₂' : C ⥤ D} {R₁ R₂ : D ⥤ C}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂') (c : L₂' ≅ L₁') :
    conjugateIsoEquiv a₁ a₂ (e₂ ≪≫ c ≪≫ e₁.symm) =
      conjugateIsoEquiv (a₁.ofNatIsoLeft e₁) (a₂.ofNatIsoLeft e₂) c := by
  apply Iso.ext
  ext M
  simp [conjugateIsoEquiv_apply_hom, conjugateEquiv_apply_app,
    Adjunction.ofNatIsoLeft_unit, Adjunction.ofNatIsoLeft_counit,
    Functor.map_comp, Category.assoc]

private theorem compTransport_finiteTrace
    {C D E : Type*} [Category C] [Category D] [Category E]
    {L₁ L₁' : C ⥤ D} {R₁ : D ⥤ C} {L₂ L₂' : D ⥤ E} {R₂ : E ⥤ D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂)
    (e₁ : L₁ ≅ L₁') (e₂ : L₂ ≅ L₂') :
    (a₁.comp a₂).ofNatIsoLeft
        (Functor.isoWhiskerRight e₁ L₂ ≪≫ Functor.isoWhiskerLeft L₁' e₂) =
      (a₁.ofNatIsoLeft e₁).comp (a₂.ofNatIsoLeft e₂) := by
  apply Adjunction.ext
  ext M
  simp only [Adjunction.ofNatIsoLeft_unit, Adjunction.comp_unit_app,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.trans_hom,
    Functor.comp_map, Functor.map_comp, Category.assoc]
  rw [← R₁.map_comp_assoc]
  have hn := a₂.unit.naturality (e₁.hom.app M)
  change e₁.hom.app M ≫ a₂.unit.app (L₁'.obj M) =
    a₂.unit.app (L₁.obj M) ≫ R₂.map (L₂.map (e₁.hom.app M)) at hn
  rw [← hn]
  simp only [Functor.map_comp, Category.assoc]

private theorem directComp_eq_finiteTrace
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    rightDerivedLowerStarComp Λ f g = (PurityTransport.lowerComp Λ f g).symm := by
  let pc := Functor.mapDerivedCategoryNatIso (upperStarComp Λ f g) ≪≫
    Functor.mapDerivedCategoryCompIso _ _
  let ef := leftDerivedUpperStarIsoMapDerivedCategory Λ f
  let eg := leftDerivedUpperStarIsoMapDerivedCategory Λ g
  let efg := leftDerivedUpperStarIsoMapDerivedCategory Λ (f ≫ g)
  let ec := Functor.isoWhiskerRight eg ((upperStar Λ f).leftDerivedFunctor) ≪≫
    Functor.isoWhiskerLeft ((upperStar Λ g).mapDerivedCategory) ef
  have hc : leftDerivedUpperStarComp Λ f g =
      efg ≪≫ pc ≪≫ ec.symm := by
    apply Iso.ext
    ext M
    simp [leftDerivedUpperStarComp, Functor.leftDerivedFunctorNatIso,
      Functor.leftDerivedFunctorCompIso, ef, eg, efg, ec, pc,
      leftDerivedUpperStarIsoMapDerivedCategory]
  unfold rightDerivedLowerStarComp
  rw [hc, conjugateTransport_finiteTrace, compTransport_finiteTrace, exactAdjunction_eq_finiteTrace,
    exactAdjunction_eq_finiteTrace, exactAdjunction_eq_finiteTrace]
  rfl

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.PurityTransport

private theorem derived_identity_comparison
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Functor.rightDerivedFunctorNatIso (Iso.refl (CondensedRing.lowerStar R f)) =
      Iso.refl _ := by
  apply Iso.ext
  change Functor.rightDerivedFunctorNatTrans (𝟙 (CondensedRing.lowerStar R f)) = 𝟙 _
  simp only [Functor.rightDerivedFunctorNatTrans, NatTrans.mapHomotopyCategory_id,
    Functor.whiskerRight_id', Functor.rightDerivedNatTrans_id]

private theorem open_factor_identity
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    {X Y Z : Scheme.{u}} (i : X ⟶ Y) (j : Y ⟶ Z)
    [IsOpenImmersion i] [IsOpenImmersion j] :
    CompactSupportComposition.openFactor R i j (i ≫ j) rfl =
      CompactSupportComposition.openComp R i j := by
  unfold CompactSupportComposition.openFactor
  exact Iso.trans_refl _

set_option maxHeartbeats 6400000 in
-- These comparisons involve the full unbounded derived-category coherence laws.
private theorem model_composition
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (k : Type u) [Field k] (H : CompactSupportComposition.CoherentData R k)
    {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (cr : Compactification.BoundaryCompactification (cf.g ≫ cg.i))
    [QuasiCompact (cf.g ≫ cg.i)]
    (sq : IsPullback cf.g cr.obj.obj.i cg.i cr.obj.obj.g)
    (K : (localizingClosureProEtale R X.obj.left).FullSubcategory) :
    ∃ m, compositionInterchangeIsNormalized R cf.g cg.i cr
        ((actualOpen R cf.i).obj K.obj) m ∧
      (H.comp f g cf cg (compositeCompactification cf cg cr)).hom.app K =
        supportComp R cf cg cr K.obj m := by
  let T : Compactification.Triangle f.hom.left g.hom.left :=
    { cf := cf, cg := cg, cfg := compositeCompactification cf cg cr,
      q := cr.obj.obj.i, p := cr.obj.obj.g, i_q := rfl, p_g := rfl, isPullback := sq }
  obtain ⟨m, hm, he⟩ := H.laws.2.2.2.1 f g T K
  refine ⟨m, hm, he.trans ?_⟩
  dsimp only [T, compositeCompactification, CompactSupportComposition.middle,
    detSfBoundaryCompactification]
  erw [open_factor_identity R cf.i cr.obj.obj.i]
  rw [directComp_eq_finiteTrace R cr.obj.obj.g cg.g]
  erw [derived_identity_comparison R (cr.obj.obj.g ≫ cg.g)]
  simp only [Iso.refl_hom, NatTrans.id_app, Category.comp_id, Functor.map_comp,
    Category.assoc]
  change (actualPush R cg.g).map m ≫
      (actualPush R cg.g).map ((actualPush R cr.obj.obj.g).map
        ((openComp R cf.i cr.obj.obj.i).hom.app K.obj)) ≫
      (lowerComp R cr.obj.obj.g cg.g).inv.app _ =
    (actualPush R cg.g).map m ≫
      (lowerComp R cr.obj.obj.g cg.g).inv.app _ ≫
      (actualPush R (cr.obj.obj.g ≫ cg.g)).map
        ((openComp R cf.i cr.obj.obj.i).hom.app K.obj)
  exact congrArg (fun z ↦ (actualPush R cg.g).map m ≫ z)
    ((lowerComp R cr.obj.obj.g cg.g).inv.naturality _)

private theorem lineCoordinates_unique (ell : ℕ) [Fact ell.Prime]
    (c : Coefficient ell) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)]
    (p q : LinePullCoordinates ell c f) : p = q := by
  have hi : p.integral = q.integral :=
    (integralComparison ell f).unique p.integral_normalized q.integral_normalized
  have hf : p.first = q.first := by
    have hp := p.first_normalized
    rw [hi] at hp
    exact eq_of_heq (hp.trans q.first_normalized.symm)
  have hp : p.power = q.power := by
    funext d
    have hp := p.power_normalized d
    rw [hf] at hp
    exact eq_of_heq (hp.trans (q.power_normalized d).symm)
  cases p
  cases q
  cases hi
  cases hf
  cases hp
  rfl

private def identityDatum {D : WeilConjectures.FiniteFieldDatum.{u}}
    (s : SmoothDatum D) : SmoothDatum D :=
  { X := s.X, Y := s.X, map := 𝟙 s.X.left, dim := 0,
    compactification := Compactification.ofIsProper (𝟙 s.X.left) }

private def replaceCompactification {D : WeilConjectures.FiniteFieldDatum.{u}}
    (s : SmoothDatum D) (d : Compactification s.map) : SmoothDatum D :=
  { s with compactification := d }

set_option maxHeartbeats 3200000 in
-- These comparisons involve the full unbounded derived-category coherence laws.
private theorem model_trace
    (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (a : AdjunctionFamily ell D)
    (ha : CompositionCompatible ell D hEll a) (c : Coefficient ell)
    (s : SmoothDatum D) (Z : Over (Spec (.of D.k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (g : s.Y.left ⟶ Z.left) [g.IsOver (Spec (.of D.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (e : ℕ) [SmoothOfRelativeDimension e g] (cg : Compactification g)
    (cr : Compactification.BoundaryCompactification (s.compactification.g ≫ cg.i))
    (sq : IsPullback s.compactification.g cr.obj.obj.i cg.i cr.obj.obj.g)
    (H : CompactSupportComposition.CoherentData (c.obj ell) D.k)
    (p : LinePullCoordinates ell c s.map) :
    letI : ∀ x : s.X.left, Invertible (ell : s.X.left.residueField x) :=
      fun x ↦ (by
        simpa only [map_natCast] using (primeUnit D ell hEll).map
          ((s.X.left ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
            IsUnit (ell : s.X.left.residueField x)).invertible
    let t : SmoothDatum D :=
      { X := s.Y, Y := Z, map := g, dim := e, compactification := cg }
    let sh := s.comp Z g e cg cr
    ∀ K : c.ctf ell Z.left,
      (H.comp
        (SepFinType.homMk (X := s.X) (Y := s.Y)
          (Over.homMk s.map (comp_over s.map (Spec (.of D.k)))))
        (SepFinType.homMk (X := s.Y) (Y := Z)
          (Over.homMk g (comp_over g (Spec (.of D.k)))))
        s.compactification cg sh.compactification).hom.app
          ((inclusion ell c s.X.left).obj
            ((source ell c sh.map sh.dim (a c sh).source_closed).obj K)) ≫
        (a c sh).trace K =
      (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cg).map
        ((CondensedRing.rightDerivedLowerShriekOfCompactification
          (c.obj ell) s.compactification).map
          (sourceComp ell c s.map g s.dim e p K.obj).hom) ≫
      (CondensedRing.rightDerivedLowerShriekOfCompactification (c.obj ell) cg).map
        ((a c s).trace ((source ell c g e (a c t).source_closed).obj K)) ≫
      (a c t).trace K := by
  dsimp only
  letI : ∀ x : s.X.left, Invertible (ell : s.X.left.residueField x) :=
    fun x ↦ (by
      simpa only [map_natCast] using (primeUnit D ell hEll).map
        ((s.X.left ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
          IsUnit (ell : s.X.left.residueField x)).invertible
  letI : ∀ y : s.Y.left, Invertible (ell : s.Y.left.residueField y) :=
    fun y ↦ (by
      simpa only [map_natCast] using (primeUnit D ell hEll).map
        ((s.Y.left ↘ Spec (.of D.k)).residueFieldAlgebraMap y) :
          IsUnit (ell : s.Y.left.residueField y)).invertible
  obtain ⟨q, hq⟩ := ha c s Z g e cg cr
  cases lineCoordinates_unique ell c s.map q p
  intro K
  let KL := (inclusion ell c s.X.left).obj
    ((source ell c (s.map ≫ g) (s.dim + e)
      (a c (s.comp Z g e cg cr)).source_closed).obj K)
  letI : QuasiCompact cg.i := cg.quasiCompact_openImmersion inferInstance
  obtain ⟨m, hm, he⟩ := model_composition (c.obj ell) D.k H
    (SepFinType.homMk (X := s.X) (Y := s.Y)
      (Over.homMk s.map (comp_over s.map (Spec (.of D.k)))))
    (SepFinType.homMk (X := s.Y) (Y := Z)
      (Over.homMk g (comp_over g (Spec (.of D.k)))))
    s.compactification cg cr sq KL
  erw [he]
  exact (hq K m hm).symm

set_option maxHeartbeats 3200000 in
-- These comparisons involve the full unbounded derived-category coherence laws.
private theorem comp_change_total
    (R : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj R] [IsCommMonObj R]
    (k : Type u) [Field k] (H : CompactSupportComposition.CoherentData R k)
    {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : Compactification f.hom.left) (cg : Compactification g.hom.left)
    (ch ch' : Compactification (f.hom.left ≫ g.hom.left))
    (K : (localizingClosureProEtale R X.obj.left).FullSubcategory) :
    (H.comp f g cf cg ch).hom.app K ≫
      (H.comparison (f ≫ g) ch ch').hom.app K =
        (H.comp f g cf cg ch').hom.app K := by
  have h := H.laws.2.2.2.2.1 f g cf cf cg cg ch ch' K
  rw [H.laws.2.1 f cf, H.laws.2.1 g cg] at h
  dsimp only [Iso.refl_hom, NatTrans.id_app] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp] at h
  exact h

set_option maxHeartbeats 3200000 in
-- These comparisons involve the full unbounded derived-category coherence laws.
private theorem model_trace_comparison
    (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (a : AdjunctionFamily ell D)
    (ha : CompositionCompatible ell D hEll a) (c : Coefficient ell)
    (s : SmoothDatum D) (Z : Over (Spec (.of D.k)))
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (g : s.Y.left ⟶ Z.left) [g.IsOver (Spec (.of D.k))]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (e : ℕ) [SmoothOfRelativeDimension e g] (cg : Compactification g)
    (cr cr' : Compactification.BoundaryCompactification (s.compactification.g ≫ cg.i))
    (sq : IsPullback s.compactification.g cr.obj.obj.i cg.i cr.obj.obj.g)
    (sq' : IsPullback s.compactification.g cr'.obj.obj.i cg.i cr'.obj.obj.g)
    (H : CompactSupportComposition.CoherentData (c.obj ell) D.k) :
    let sh := s.comp Z g e cg cr
    let sh' := s.comp Z g e cg cr'
    ∀ K : c.ctf ell Z.left,
      (H.comparison
        (SepFinType.homMk (X := s.X) (Y := Z)
          (Over.homMk (s.map ≫ g) (comp_over (s.map ≫ g) (Spec (.of D.k)))))
        sh.compactification sh'.compactification).hom.app
          ((inclusion ell c s.X.left).obj
            ((source ell c sh.map sh.dim (a c sh).source_closed).obj K)) ≫
        (a c sh').trace K = (a c sh).trace K := by
  dsimp only
  letI : ∀ x : s.X.left, Invertible (ell : s.X.left.residueField x) :=
    fun x ↦ (by
      simpa only [map_natCast] using (primeUnit D ell hEll).map
        ((s.X.left ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
          IsUnit (ell : s.X.left.residueField x)).invertible
  letI : ∀ y : s.Y.left, Invertible (ell : s.Y.left.residueField y) :=
    fun y ↦ (by
      simpa only [map_natCast] using (primeUnit D ell hEll).map
        ((s.Y.left ↘ Spec (.of D.k)).residueFieldAlgebraMap y) :
          IsUnit (ell : s.Y.left.residueField y)).invertible
  obtain ⟨p⟩ := linePullCoordinates_nonempty ell c s.map
  intro K
  have h := model_trace ell D hEll a ha c s Z g e cg cr sq H p K
  have h' := model_trace ell D hEll a ha c s Z g e cg cr' sq' H p K
  let KL := (inclusion ell c s.X.left).obj
    ((source ell c (s.map ≫ g) (s.dim + e)
      (a c (s.comp Z g e cg cr)).source_closed).obj K)
  let f := SepFinType.homMk (X := s.X) (Y := s.Y)
    (Over.homMk s.map (comp_over s.map (Spec (.of D.k))))
  let gg := SepFinType.homMk (X := s.Y) (Y := Z)
    (Over.homMk g (comp_over g (Spec (.of D.k))))
  apply (cancel_epi ((H.comp f gg s.compactification cg
    (compositeCompactification s.compactification cg cr)).hom.app KL)).mp
  rw [← Category.assoc]
  erw [comp_change_total]
  exact h'.trans h.symm

/-- A trace comparison with its geometric data given as independent arguments.
This private wrapper permits transport of the maps before constructing the
corresponding dependent smooth-data records. -/
@[irreducible] private def rawTraceComparison
    (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
    (a : AdjunctionFamily ell D) (c : Coefficient ell)
    (H : CompactSupportComposition.CoherentData (c.obj ell) D.k)
    (X Y : Over (Spec (.of D.k)))
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (f : X.left ⟶ Y.left) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (e : ℕ) [SmoothOfRelativeDimension e f]
    (Z₀ Z₁ : Scheme.{u}) (g₀ : Z₀ ⟶ Y.left) (i₀ : X.left ⟶ Z₀)
    (g₁ : Z₁ ⟶ Y.left) (i₁ : X.left ⟶ Z₁)
    (h₀ : f = i₀ ≫ g₀) (h₁ : f = i₁ ≫ g₁)
    (hp₀ : IsProper g₀) (hi₀ : IsOpenImmersion i₀)
    (hp₁ : IsProper g₁) (hi₁ : IsOpenImmersion i₁)
    (K : c.ctf ell Y.left) : Prop :=
  let c₀ : Compactification f := ⟨Z₀, g₀, i₀, h₀, hp₀, hi₀⟩
  let c₁ : Compactification f := ⟨Z₁, g₁, i₁, h₁, hp₁, hi₁⟩
  let s₀ : SmoothDatum D := { X := X, Y := Y, map := f, dim := e, compactification := c₀ }
  let s₁ : SmoothDatum D := { X := X, Y := Y, map := f, dim := e, compactification := c₁ }
  (H.comparison
    (SepFinType.homMk (X := X) (Y := Y)
      (Over.homMk f (comp_over f (Spec (.of D.k))))) c₀ c₁).hom.app
        ((inclusion ell c X.left).obj
          ((source ell c f e (a c s₀).source_closed).obj K)) ≫
    (a c s₁).trace K = (a c s₀).trace K

set_option maxHeartbeats 3200000 in
-- These comparisons involve the full unbounded derived-category coherence laws.
private theorem trace_refinement
    (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (a : AdjunctionFamily ell D)
    (ha : CompositionCompatible ell D hEll a) (c : Coefficient ell)
    (s : SmoothDatum D) (d : Compactification s.map)
    (r : d.Refinement s.compactification)
    (sq : IsPullback (𝟙 s.X.left) d.i s.compactification.i r.hom)
    (H : CompactSupportComposition.CoherentData (c.obj ell) D.k)
    (K : c.ctf ell s.Y.left) :
    (H.comparison
      (SepFinType.homMk (X := s.X) (Y := s.Y)
        (Over.homMk s.map (comp_over s.map (Spec (.of D.k)))))
      s.compactification d).hom.app
        ((inclusion ell c s.X.left).obj
          ((source ell c s.map s.dim (a c s).source_closed).obj K)) ≫
      (a c (replaceCompactification s d)).trace K = (a c s).trace K := by
  letI : QuasiCompact s.compactification.i :=
    s.compactification.quasiCompact_openImmersion inferInstance
  letI : QuasiCompact d.i := d.quasiCompact_openImmersion inferInstance
  let cr : Compactification ((𝟙 s.X.left) ≫ s.compactification.i) :=
    (Compactification.ofIsOpenImmersion s.compactification.i).copy (Category.id_comp _)
  let cr' : Compactification ((𝟙 s.X.left) ≫ s.compactification.i) :=
    { Z := d.Z, i := d.i, g := r.hom,
      comm := (Category.id_comp _).trans r.i_hom.symm,
      isProper := inferInstance, isOpenImmersion := inferInstance }
  letI : QuasiCompact ((𝟙 s.X.left) ≫ s.compactification.i) := inferInstance
  have hs : IsPullback (𝟙 s.X.left) cr.i s.compactification.i cr.g :=
    by
      change IsPullback (𝟙 s.X.left) s.compactification.i s.compactification.i
        (𝟙 s.compactification.Z)
      exact IsPullback.of_horiz_isIso ⟨by simp⟩
  have h := model_trace_comparison ell D hEll a ha c (identityDatum s)
    s.Y s.map s.dim s.compactification
    (detSfBoundaryCompactification cr) (detSfBoundaryCompactification cr') hs sq H K
  -- Transport the independent geometric fields before rebuilding the records.
  cases s with
  | mk X Y f e cf =>
    have h₀ := cf.comm
    have h₁ := d.comm
    have hp₀ : IsProper cf.g := inferInstance
    have hi₀ : IsOpenImmersion cf.i := inferInstance
    have hp₁ : IsProper d.g := inferInstance
    have hi₁ : IsOpenImmersion d.i := inferInstance
    cases cf with
    | mk Z₀ g₀ i₀ =>
      cases d with
      | mk Z₁ g₁ i₁ =>
        letI : IsProper g₀ := hp₀
        letI : IsOpenImmersion i₀ := hi₀
        letI : IsProper g₁ := hp₁
        letI : IsOpenImmersion i₁ := hi₁
        have hr := r.hom_g
        dsimp only at hr
        have hh : rawTraceComparison ell D a c H X Y (𝟙 X.left ≫ f) (0 + e)
            Z₀ Z₁ (𝟙 Z₀ ≫ g₀) (𝟙 X.left ≫ i₀)
            (r.hom ≫ g₀) (𝟙 X.left ≫ i₁)
            (by simpa only [Category.id_comp] using h₀)
            (by simpa only [Category.id_comp, hr] using h₁)
            (by infer_instance) (by infer_instance) (by infer_instance) (by infer_instance)
            K := by
          unfold rawTraceComparison
          dsimp only [identityDatum, SmoothDatum.comp, compositeCompactification,
            Compactification.ofIsProper, cr, cr', Compactification.ofIsOpenImmersion,
            Compactification.copy, detSfBoundaryCompactification] at h
          exact h
        have hh' : rawTraceComparison ell D a c H X Y f e Z₀ Z₁ g₀ i₀ g₁ i₁
            h₀ h₁ hp₀ hi₀ hp₁ hi₁ K := by
          simpa only [Category.id_comp, Nat.zero_add, hr] using hh
        unfold rawTraceComparison at hh'
        exact hh'

set_option maxHeartbeats 3200000 in
-- These comparisons involve the full unbounded derived-category coherence laws.
private theorem trace_change_compactification
    (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (a : AdjunctionFamily ell D)
    (ha : CompositionCompatible ell D hEll a) (c : Coefficient ell)
    (s : SmoothDatum D) (d : Compactification s.map)
    (H : CompactSupportComposition.CoherentData (c.obj ell) D.k)
    (K : c.ctf ell s.Y.left) :
    (H.comparison
      (SepFinType.homMk (X := s.X) (Y := s.Y)
        (Over.homMk s.map (comp_over s.map (Spec (.of D.k)))))
      s.compactification d).hom.app
        ((inclusion ell c s.X.left).obj
          ((source ell c s.map s.dim (a c s).source_closed).obj K)) ≫
      (a c (replaceCompactification s d)).trace K = (a c s).trace K := by
  let r := Compactification.inf s.compactification d
  have h₁ := trace_refinement ell D hEll a ha c s r
    (Compactification.infFst s.compactification d)
    (Compactification.isPullback_infFst s.compactification d).flip H K
  have h₂ := trace_refinement ell D hEll a ha c (replaceCompactification s d) r
    (Compactification.infSnd s.compactification d)
    (Compactification.isPullback_infSnd s.compactification d).flip H K
  rw [← h₂, ← Category.assoc]
  have hc := H.laws.2.2.1
    (SepFinType.homMk (X := s.X) (Y := s.Y)
      (Over.homMk s.map (comp_over s.map (Spec (.of D.k))))) s.compactification d r
  erw [← NatTrans.comp_app, ← Iso.trans_hom, hc]
  exact h₁

set_option maxHeartbeats 3200000 in
-- The categorical finite-trace transport expands substantially after coefficient
-- generalization, so this declaration needs the larger heartbeat budget.
/--
Source: current blueprint `sk-prop-sp-composition.proof.md`, Towers paragraph
(blueprint: lem-pur-integral-composite-normalized-composition-trace).

Proof in words.  In the normalized `𝒪_E / ℓ^•` tower, use the finite
composition-factors equations to identify the two orientations of the composite
purity map.  Apply the total derived-limit comparison to this equality of tower
morphisms, then use the native integral compositor realization and the integral
counit realization to identify the resulting support and trace pastes with the
selected normalized family.  The same construction with the base-field integral
presentation gives the `ℤ_ℓ` conjunct; the argument is uniform for every finite
intermediate field, including ramified fields. -/
theorem integralCompositeNormalizedCompositionTrace
    (ell : ℕ) [Fact ell.Prime] (D : WeilConjectures.FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) :
    CompositeNormalizedCompositionTrace ell D hEll .integers ∧
      ∀ E : PadicAlgCl.FiniteIntermediateField ell,
        CompositeNormalizedCompositionTrace ell D hEll (.integral E) := by
  have composite (c : Coefficient ell) : CompositeNormalizedCompositionTrace ell D hEll c := by
    intro s Z _ _ _ g _ _ _ _ e _ cg cr H
    exact normalized_trace ell D hEll c s Z g e
      cg (compositeCompactification s.compactification cg cr) H
  exact ⟨composite .integers, fun E ↦ composite (.integral E)⟩

end AlgebraicGeometry.ProEtale.PurityTransport

-- final refresh
