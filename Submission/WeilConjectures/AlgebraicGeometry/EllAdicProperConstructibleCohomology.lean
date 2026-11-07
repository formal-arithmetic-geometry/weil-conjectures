/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperLowerStarCoproducts
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarExtensionRingIso
import Submission.WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.DerivedTensor
import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients
import Submission.WeilConjectures.Algebra.Homology.OpenCoverMateComplexShortExact
import Submission.WeilConjectures.Algebra.Homology.RingedSpaceModuleExactnessLocalLifting
import Submission.WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Submission.WeilConjectures.AlgebraicGeometry.AdicConstructibilityPredicateComparison
import Submission.WeilConjectures.AlgebraicGeometry.AffineCapSectionOpen
import Submission.WeilConjectures.AlgebraicGeometry.AffineLocusOfCompatibleComponentSections
import Submission.WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import Submission.WeilConjectures.AlgebraicGeometry.AmpleFiniteAffineCover
import Submission.WeilConjectures.AlgebraicGeometry.AmpleIdealSection
import Submission.WeilConjectures.AlgebraicGeometry.AmpleImmersionAffineBase
import Submission.WeilConjectures.AlgebraicGeometry.AmpleIso
import Submission.WeilConjectures.AlgebraicGeometry.AmplePositiveTensorPower
import Submission.WeilConjectures.AlgebraicGeometry.AmpleProjCanonicalMap
import Submission.WeilConjectures.AlgebraicGeometry.AmplePullback
import Submission.WeilConjectures.AlgebraicGeometry.AmpleSeparated
import Submission.WeilConjectures.AlgebraicGeometry.BoundaryCechInjectiveMiddle
import Submission.WeilConjectures.AlgebraicGeometry.BoundaryCoefficientDegreeSplit
import Submission.WeilConjectures.AlgebraicGeometry.BoundaryCoefficientTensorProduct
import Submission.WeilConjectures.AlgebraicGeometry.BoundaryPullbackTensorUnit
import all Submission.WeilConjectures.AlgebraicGeometry.BoundedConstructibleExtendScalars
import Submission.WeilConjectures.AlgebraicGeometry.BoundedConstructibleTower
import Submission.WeilConjectures.AlgebraicGeometry.CechH1Injective
import Submission.WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Submission.WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitEpi
import Submission.WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitKernel
import Submission.WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitQuotient
import Submission.WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitsCohomologyComparison
import Submission.WeilConjectures.AlgebraicGeometry.ClosedImmersionUnitsEpi
import Submission.WeilConjectures.AlgebraicGeometry.CohomologyPullbackDerivedUnit
import Submission.WeilConjectures.AlgebraicGeometry.CohomologyTorInterval
import Submission.WeilConjectures.AlgebraicGeometry.CompletedIntegralCoefficients
import Submission.WeilConjectures.AlgebraicGeometry.ComponentIntersectionsFinite
import Submission.WeilConjectures.AlgebraicGeometry.ComponentSupportedAffineSection
import Submission.WeilConjectures.AlgebraicGeometry.CondensedQbarScalarBasis
import Submission.WeilConjectures.AlgebraicGeometry.CondensedSubfieldBoundedCopowers
import Submission.WeilConjectures.AlgebraicGeometry.ConstructibleColimitFactorization
import Submission.WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleLimitDescent
import Submission.WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import Submission.WeilConjectures.AlgebraicGeometry.ConstructibleModuleSheafColimit
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousIntegralPushComparison
import Submission.WeilConjectures.AlgebraicGeometry.Curve.DisjointOpenExtensionBiproduct
import Submission.WeilConjectures.AlgebraicGeometry.Curve.SmoothCalculations
import Submission.WeilConjectures.AlgebraicGeometry.DerivedCohomologyGermIso
import Submission.WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit
import Submission.WeilConjectures.AlgebraicGeometry.DerivedGlobalGermExchange
import all Submission.WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import Submission.WeilConjectures.AlgebraicGeometry.DescendFinite
import Submission.WeilConjectures.AlgebraicGeometry.DescendMonomorphism
import Submission.WeilConjectures.AlgebraicGeometry.DescendSurjective
import Submission.WeilConjectures.AlgebraicGeometry.Dimension
import Submission.WeilConjectures.AlgebraicGeometry.DimensionAtPointFieldExtension
import Submission.WeilConjectures.AlgebraicGeometry.DirectImageSplitCoverProduct
import Submission.WeilConjectures.AlgebraicGeometry.EtaleDirectedCohomologyColimitExtension
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInjectiveSectionsComparison
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import Submission.WeilConjectures.AlgebraicGeometry.EtaleInverseLimitDescent
import Submission.WeilConjectures.AlgebraicGeometry.EtaleLocalFiniteAtPoint
import Submission.WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
import Submission.WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import Submission.WeilConjectures.AlgebraicGeometry.EtaleProperOpenHorizontalNormalization
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSectionGermIso
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSectionsTriangleNaturality
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import Submission.WeilConjectures.AlgebraicGeometry.EtaleSplitResiduePoints
import Submission.WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore
import Submission.WeilConjectures.AlgebraicGeometry.EventuallyProper
import Submission.WeilConjectures.AlgebraicGeometry.FibreDimensionBoundedOpenUpstairs
import Submission.WeilConjectures.AlgebraicGeometry.FieldExtensionFpqcCover
import Submission.WeilConjectures.AlgebraicGeometry.FiniteClosedImmersionNearFibre
import Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingCompactification
import all Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingConstructibility
import Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteEncodingTensorTor
import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import Submission.WeilConjectures.AlgebraicGeometry.FiniteEtaleUnitStalkInclusion
import Submission.WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantModuleValues
import Submission.WeilConjectures.AlgebraicGeometry.FinitePiecePersistence
import Submission.WeilConjectures.AlgebraicGeometry.FiniteSurjectiveAffineTargetNoetherian
import Submission.WeilConjectures.AlgebraicGeometry.FractionZeroTensorPower
import Submission.WeilConjectures.AlgebraicGeometry.GeometricallyConnectedCheckAfterExtension
import Submission.WeilConjectures.AlgebraicGeometry.GlobalCohomologyContinuityPresentation
import Submission.WeilConjectures.AlgebraicGeometry.GlobalSectionsProper
import Submission.WeilConjectures.AlgebraicGeometry.GlueComponentLineBundles
import Submission.WeilConjectures.AlgebraicGeometry.HomeomorphPurelyInseparableBaseChange
import Submission.WeilConjectures.AlgebraicGeometry.IntegralDimOneAmple
import Submission.WeilConjectures.AlgebraicGeometry.IntegralLfpConstantModelComparison
import Submission.WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import Submission.WeilConjectures.AlgebraicGeometry.InvertSCOhomology
import Submission.WeilConjectures.AlgebraicGeometry.InvertibleSectionLocalization
import Submission.WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
import Submission.WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility
import Submission.WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.AffineDiagramSmoothStage
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.FiniteNormalDenseOpenIso
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationDominantLift
import Submission.WeilConjectures.AlgebraicGeometry.Morphisms.ProperQuasiFinite
import Submission.WeilConjectures.AlgebraicGeometry.NoetherNormalization
import Submission.WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import Submission.WeilConjectures.AlgebraicGeometry.NonvanishingTensorPullback
import Submission.WeilConjectures.AlgebraicGeometry.ObjectSectionsNaturality
import Submission.WeilConjectures.AlgebraicGeometry.OpenExtendedInjectiveProperAcyclic
import Submission.WeilConjectures.AlgebraicGeometry.PadicConstantLocalModelTor
import Submission.WeilConjectures.AlgebraicGeometry.PicardH1RestrictionCompatibility
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesImage
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleConstantModuleEncoding
import all Submission.WeilConjectures.AlgebraicGeometry.ProEtaleConstructibleOrigin
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelLocalConstancy
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModelStalks
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleLisseFiniteModelsFromLisse
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Submission.WeilConjectures.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Submission.WeilConjectures.AlgebraicGeometry.ProjStandardOpenProperties
import Submission.WeilConjectures.AlgebraicGeometry.ProjectiveSpaceFiniteIndexIso
import Submission.WeilConjectures.AlgebraicGeometry.ProperCoproduct
import Submission.WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import Submission.WeilConjectures.AlgebraicGeometry.PullbackFiniteConstantLocalModel
import Submission.WeilConjectures.AlgebraicGeometry.PullbackTensorUnitSection
import Submission.WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange
import Submission.WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphism
import Submission.WeilConjectures.AlgebraicGeometry.QuasiFinitePolynomialChart.CoordinateFibreDimension
import Submission.WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus
import Submission.WeilConjectures.AlgebraicGeometry.SectionRingVeroneseFractions
import Submission.WeilConjectures.AlgebraicGeometry.SectionRingVeroneseNumeratorTransition
import Submission.WeilConjectures.AlgebraicGeometry.SheafTensorPushoutCancellation
import Submission.WeilConjectures.AlgebraicGeometry.SiteRestrictionInjectives
import Submission.WeilConjectures.AlgebraicGeometry.Sites.PointConstantSheaf
import Submission.WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
import Submission.WeilConjectures.AlgebraicGeometry.SmoothBaseChange.HigherDirectImageForgetComparison
import Submission.WeilConjectures.AlgebraicGeometry.SpecAlgClosedEtaleSheafConstant
import Submission.WeilConjectures.AlgebraicGeometry.SquareZeroQuotientLocalAction
import Submission.WeilConjectures.AlgebraicGeometry.SquareZeroTensorSectionProductComparison
import Submission.WeilConjectures.AlgebraicGeometry.StratifiedTorIntervalDevissage
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationAbelianStalkExchangeLocalization
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationClosedFiberForward
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import Submission.WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import Submission.WeilConjectures.AlgebraicGeometry.StrictLocalDerivedGlobalExchange
import Submission.WeilConjectures.AlgebraicGeometry.StrictLocalNeighbourhoodGeometryExistence
import Submission.WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import Submission.WeilConjectures.AlgebraicGeometry.TensorPullbackPowerAppend
import Submission.WeilConjectures.AlgebraicGeometry.Thickening
import Submission.WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import Submission.WeilConjectures.AlgebraicGeometry.UnrestrictedStrictHenselizationStalk
import Submission.WeilConjectures.AlgebraicGeometry.ZariskiEtaleCore
import Submission.WeilConjectures.AlgebraicGeometry.ZeroDimNoetherianAffine
import Submission.WeilConjectures.CategoryTheory.Abelian.HorseshoeResolutions
import Submission.WeilConjectures.CategoryTheory.Abelian.ResolvedBoundaryNaturality
import Submission.WeilConjectures.CategoryTheory.Abelian.RightDerivedTriangleConnecting
import Submission.WeilConjectures.CategoryTheory.CoefficientPushCopowerCriterion
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import Submission.WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import Submission.WeilConjectures.CategoryTheory.RightDerivedPlusCube
import Submission.WeilConjectures.CategoryTheory.RightDerivedSingleUnitHomologyComparison
import Submission.WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Submission.WeilConjectures.CategoryTheory.Sites.Point.Linear
import Submission.WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
import Submission.WeilConjectures.Compactification.CategoryBaseChange
import Submission.WeilConjectures.ConstructibleSheaf.AffineStratification
import Submission.WeilConjectures.ConstructibleSheaf.ConnectedTorsorSubgroupQuotient
import Submission.WeilConjectures.ConstructibleSheaf.ConstantModuleLocallyConstant
import Submission.WeilConjectures.ConstructibleSheaf.FiniteSetMonodromyTorsor
import Submission.WeilConjectures.ConstructibleSheaf.ModuleConstantOfSetPullback
import Submission.WeilConjectures.ConstructibleSheaf.TorsorDiagonalEvaluationBijective
import Submission.WeilConjectures.ConstructibleSheaf.TorsorSectionRepresentation
import Submission.WeilConjectures.FieldTheory.CommonExtensionFields
import Submission.WeilConjectures.FieldTheory.GeometricallyReducedExtensionSeparable
import Submission.WeilConjectures.FieldTheory.MakeSeparable
import Submission.WeilConjectures.FieldTheory.SeparableExtensionFractionFieldOfSmoothAlgebra
import Submission.WeilConjectures.FieldTheory.SeparableSmoothColimit
import Submission.WeilConjectures.FieldTheory.SeparablyGeneratedTensorReduced
import Submission.WeilConjectures.Mathlib.CategoryTheory.Extensive
import Submission.WeilConjectures.RepresentationTheory.PrimaryPGroupFiltration
import Submission.WeilConjectures.RingTheory.BoundedProjectiveResolutionDimension
import Submission.WeilConjectures.RingTheory.FilteredColimitNormalRing
import Submission.WeilConjectures.RingTheory.GradedPrimeAvoidance
import Submission.WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal
import Submission.WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions
import Submission.WeilConjectures.RingTheory.RegularLocalOfFormallySmoothAdic
import Submission.WeilConjectures.RingTheory.RegularLocalSeparableResidueSmooth
import Submission.WeilConjectures.RingTheory.SmoothAtPrimeFieldExtensionDescent
import Submission.WeilConjectures.RingTheory.SmoothNormalRing
import Submission.WeilConjectures.RingTheory.SymmetricAlgebraBaseChange
import Submission.WeilConjectures.SixFunctors.Etale.Derived.LowerShriekPlusBaseChange
import Submission.WeilConjectures.SixFunctors.Etale.Derived.Stability.Generation
import Submission.WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import Submission.WeilConjectures.SixFunctors.ProEtale.ConstructibleSheaf
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.HomComparison
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerStarCoproducts
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Stalk
import Submission.WeilConjectures.SixFunctors.ProEtale.IntegralDirectImageLimits
import Submission.WeilConjectures.SixFunctors.ProEtale.IntegralResidueCriterion
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit
import Submission.WeilConjectures.Topology.DimensionSupremumLocalDimensions
import Submission.WeilConjectures.Topology.InverseImageOperationExt
import Submission.WeilConjectures.Topology.InverseImageRegularExtension
import Submission.WeilConjectures.Topology.NoetherianTopologicalCohomologyVanishing

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

set_option linter.privateModule false

/-!
# Constructibility of proper ell-adic direct-image cohomology

This is the constructibility assertion of proper finiteness, separated from the
uniform cohomological-dimension estimate.
(auxiliary; not a blueprint node)
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits ZeroObject
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] Sheaf.monObj_sheafCompose_obj
  Mod.monoidalClosed
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.rightAdjoint Mod.extendScalars upperStarFromPoint
  ProEtale.CondensedRing.upperStar
  ProEtale.FiniteDiscreteOrdinary.Encoding.fixedDerived
  ProEtale.FiniteDiscreteOrdinary.Encoding.ordinaryDerived

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

open _root_.DerivedCategory CategoryTheory.Pretriangulated in
private lemma proper_bounded_induction (P : ObjectProperty (_root_.DerivedCategory C))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (h : ∀ G : C, P ((singleFunctor C 0).obj G)) (K : _root_.DerivedCategory C) (a b : ℤ)
    [K.IsGE a] [K.IsLE b] : P K := by
  exact prop_of_bounded P ⊤ (fun G _ ↦ h G) K
    ⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩⟩ (fun _ ↦ trivial)

private theorem proper_finite_field_tor
    (F : Type (u + 1)) [Field F] (X : Scheme.{u})
    {K : _root_.DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} F))}
    (hK : Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} F) X K) :
    Etale.DerivedCategory.finiteTorAmplitude (ModuleCat.{u + 1} F) X K := by
  obtain ⟨⟨⟨a, _⟩, ⟨b, _⟩⟩, -⟩ := hK
  refine proper_bounded_induction _ (fun G ↦ ?_) K a b
  refine ⟨0, 0, Etale.torAmplitudeIn_singleFunctor_zero_of_flat _ G ?_⟩
  exact (Etale.flat_iff_forall_flat_sheafFiber_obj G).2 fun _ ↦
    (ModuleCat.flat_iff_flat _).2 inferInstance

/-- The prime `l` vanishes in the residue field of the integers of a finite extension
of `ℚ_l`: its absolute value `1 / l` is below one, so it lies in the maximal ideal. -/
private noncomputable def continuousRingIso
    {A B : Type u} [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    [TopologicalSpace B] [CommRing B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hi : Continuous e.symm) :
    Mon.mk (Profinite.continuousCoefficientRingObj A) ≅
      Mon.mk (Profinite.continuousCoefficientRingObj B) := by
  let eR : Profinite.continuousCoefficientRingSheaf A ≅
      Profinite.continuousCoefficientRingSheaf B :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous S.unop he).comp
              ULift.ringEquiv.toRingHom))
        naturality := by
          intro S T f
          ext x
          rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous S.unop hi).comp
              ULift.ringEquiv.toRingHom))
        naturality := by
          intro S T f
          ext x
          rfl }⟩
      hom_inv_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.apply_symm_apply _ }
  let eAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom eAb.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  have : IsMonHom eAb.inv := Sheaf.isMonHom_sheafCompose_map _ eR.inv
  exact
    { hom := Mon.ofHom eAb.hom
      inv := Mon.ofHom eAb.inv
      hom_inv_id := Mon.Hom.ext eAb.hom_inv_id
      inv_hom_id := Mon.Hom.ext eAb.inv_hom_id }

private noncomputable def continuousSmallRingIso
    {A : Type u} {B : Type} [TopologicalSpace A] [CommRing A] [IsTopologicalRing A]
    [TopologicalSpace B] [CommRing B] [IsTopologicalRing B]
    (e : A ≃+* B) (he : Continuous e) (hi : Continuous e.symm) :
    Mon.mk (Profinite.continuousCoefficientRingObj A) ≅
      Mon.mk (Profinite.continuousMapRingObj B) := by
  let eR : Profinite.continuousCoefficientRingSheaf A ≅
      Profinite.continuousMapRingSheaf B :=
    { hom := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.toRingHom.compLeftContinuous S.unop he).comp
              ULift.ringEquiv.toRingHom))
        naturality := by
          intro S T f
          ext x
          rfl }⟩
      inv := ⟨{
        app := fun S ↦ RingCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((e.symm.toRingHom.compLeftContinuous S.unop hi).comp
              ULift.ringEquiv.toRingHom))
        naturality := by
          intro S T f
          ext x
          rfl }⟩
      hom_inv_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.symm_apply_apply _
      inv_hom_id := by
        ext S x
        apply ULift.ext
        apply ContinuousMap.ext
        intro t
        exact e.apply_symm_apply _ }
  let eAb := (sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).mapIso eR
  have : IsMonHom eAb.hom := Sheaf.isMonHom_sheafCompose_map _ eR.hom
  have : IsMonHom eAb.inv := Sheaf.isMonHom_sheafCompose_map _ eR.inv
  exact
    { hom := Mon.ofHom eAb.hom
      inv := Mon.ofHom eAb.inv
      hom_inv_id := Mon.Hom.ext eAb.hom_inv_id
      inv_hom_id := Mon.Hom.ext eAb.inv_hom_id }

@[irreducible] private noncomputable def integerLatticeIso
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Mon.mk (ProEtale.integralCondensedRing l E) ≅
      Mon.mk (ProEtale.DerivedNakayama.integerRing l E) := by
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A := ProEtale.latticeCoefficientIntegers l E
  let B := Padic.coefficientExtensionIntegers l E
  let e : A ≃+* B :=
    { toFun := fun x ↦ ⟨x.val.ofAbs, x.property⟩
      invFun := fun x ↦ ⟨WithAbs.toAbs _ x.val, x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    intro x
    rfl
  have he' : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  exact continuousRingIso e he.continuous he'.continuous

private theorem integerModel_comparison
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsNoetherian X]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (ProEtale.DerivedNakayama.integerRing l E) X)) :
    IsConstructibleModuleObject (condensedRingObj
      (ProEtale.DerivedNakayama.integerRing l E) X) M ↔
      ProEtale.IsConstantModelConstructible (ProEtale.DerivedNakayama.integerRing l E) X M :=
  ProEtale.comparison_transport (integerLatticeIso l E) X
    (ProEtale.integralLfpConstantModelComparison l E X) M

@[irreducible] private noncomputable def integerNormedIso
    (l : ℕ) [Fact l.Prime] (E : Type) [NormedField E]
    [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    Mon.mk (integralCoeff.{u} l E) ≅
      Mon.mk (ProEtale.DerivedNakayama.integerRing l (ULift.{u} E)) := by
  let F := ULift.{u} E
  let : FiniteDimensional ℚ_[l] F :=
    (ULift.moduleEquiv (R := ℚ_[l]) (M := E)).symm.finiteDimensional
  letI : NormedField F :=
    { (inferInstance : Field F), (inferInstance : NormedCommRing F) with
      dist_eq x y := dist_eq_norm_neg_add x.down y.down
      norm_mul x y := norm_mul x.down y.down }
  letI : NormedAlgebra ℚ_[l] F := ⟨fun a x ↦ norm_smul_le a x.down⟩
  have hn (x : F) : spectralNorm ℚ_[l] F x = ‖x.down‖ :=
    (NormedAlgebra.norm_eq_spectralNorm ℚ_[l] (L := F) x).symm
  have hm (x : F) : x ∈ Padic.coefficientExtensionIntegers l F ↔
      x.down ∈ continuousIntegers l E := by
    have h := Padic.mem_coefficientExtensionIntegers l F x
    change _ ↔ ‖x.down‖₊ ≤ 1
    rw [h]
    change spectralNorm ℚ_[l] F x ≤ 1 ↔ _
    rw [hn]
    simpa only [NNReal.coe_one, coe_nnnorm] using
      (NNReal.coe_le_coe : (‖x.down‖₊ : ℝ) ≤ ((1 : NNReal) : ℝ) ↔ ‖x.down‖₊ ≤ 1)
  let A := ProEtale.latticeCoefficientIntegers l F
  let e : A ≃+* continuousIntegers l E :=
    { toFun := fun x ↦ ⟨x.val.ofAbs.down, (hm x.val.ofAbs).mp x.property⟩
      invFun := fun x ↦ ⟨WithAbs.toAbs _ (ULift.up x.val), (hm _).mpr x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }
  have he : Isometry e := by
    apply AddMonoidHomClass.isometry_of_norm e
    intro x
    change ‖x.val.ofAbs.down‖ = spectralNorm ℚ_[l] F x.val.ofAbs
    exact (hn x.val.ofAbs).symm
  have he' : Isometry e.symm := by
    intro x y
    simpa only [e.apply_symm_apply] using (he (e.symm x) (e.symm y)).symm
  exact (continuousSmallRingIso e he.continuous he'.continuous).symm ≪≫
    integerLatticeIso l F

/-- A prime different from the characteristic of `k` is a unit in every stalk of a
scheme over `k`. -/
private theorem constructible_derived_extend
    (X : Scheme.{u})
    (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
    (φ : R ⟶ S) [IsMonHom φ] [PreservesFiniteLimits (Mod.extendScalars φ)]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) R))
    (L : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S))
    (e : (Mod.extendScalars φ).leftDerivedFunctor.obj K ≅ L)
    (q : ℤ) (h : IsConstructibleModuleObject R
      ((DerivedCategory.homologyFunctor _ q).obj K)) :
    IsConstructibleModuleObject S ((DerivedCategory.homologyFunctor _ q).obj L) := by
  have h' := ProEtale.constructible_extend R S φ h
  have h'' := _root_.constructible_of_iso
    (((Mod.extendScalars φ).leftDerivedFunctorHomologyFunctorIso q).app K) h'
  exact _root_.constructible_of_iso ((DerivedCategory.homologyFunctor _ q).mapIso e) h''

end AlgebraicGeometry.ProEtale.CondensedRing
