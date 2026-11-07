/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
public import Submission.WeilConjectures.CategoryTheory.RingedIdealGenerators
public import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import Submission.WeilConjectures.CategoryTheory.RingedDerivedRestriction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
public import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Submission.WeilConjectures.CategoryTheory.RingedSectionLocalization
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.RingTheory.Localization.Away.Basic
public import Submission.WeilConjectures.CategoryTheory.LocalExtendedCechDescription
public import Submission.WeilConjectures.CategoryTheory.RingedExtendedCech
public import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
public import Mathlib.Algebra.Homology.Monoidal
public import Submission.WeilConjectures.CategoryTheory.RingedCompletionUnit
public import Submission.WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
public import Submission.WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
public import Submission.WeilConjectures.Algebra.Homology.HomComplexComponents
public import Submission.WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import Submission.WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality
import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHom
import Submission.WeilConjectures.AlgebraicGeometry.ExtendedCechReflectorCore
import Submission.WeilConjectures.CategoryTheory.LocallyDerivedRingedIdealComplete
import Submission.WeilConjectures.CategoryTheory.RingedIdealGenerators
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Submission.WeilConjectures.CategoryTheory.RingedDerivedRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Continuous
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Submission.WeilConjectures.CategoryTheory.RingedSectionLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.RingTheory.Localization.Away.Basic
import Submission.WeilConjectures.CategoryTheory.LocalExtendedCechDescription
import Submission.WeilConjectures.CategoryTheory.RingedExtendedCech
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import Mathlib.Algebra.Homology.Monoidal
import Submission.WeilConjectures.CategoryTheory.RingedCompletionUnit
import Submission.WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import Submission.WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import Submission.WeilConjectures.Algebra.Homology.HomComplexComponents
import Submission.WeilConjectures.AlgebraicGeometry.ExtendedCechCompleteUnitCriterion
import Submission.WeilConjectures.AlgebraicGeometry.ExtendedCechCompleteImpliesUnitIso
import Submission.WeilConjectures.CategoryTheory.RingedCechCompletionUnitIdempotence
import Submission.WeilConjectures.CategoryTheory.RingedKoszulSystem
import Submission.WeilConjectures.Algebra.Homology.HomComplex
import Submission.WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
import Submission.WeilConjectures.CategoryTheory.RingedSiteGrothendieckAbelian
import Submission.WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Submission.WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Submission.WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import Submission.WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
import Submission.WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import Mathlib.Algebra.BigOperators.Ring.Finset
import Submission.WeilConjectures.CategoryTheory.Ringed.RingedInternalHomExactRestrictionSupplement
import Mathlib.Algebra.Homology.Double
import Mathlib.CategoryTheory.Endomorphism
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import Submission.WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import Submission.WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import Submission.WeilConjectures.Algebra.Homology.KFlatRHomCurrying
import Submission.WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Submission.WeilConjectures.Algebra.Homology.KInjectiveHomComplex
import Submission.WeilConjectures.Algebra.Homology.HomTensorDegreewise
import Submission.WeilConjectures.Algebra.Homology.HomTensorDifferential
import Submission.WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import Submission.WeilConjectures.Algebra.Homology.HomTensorNaturality
import Submission.WeilConjectures.CategoryTheory.RingedCechTensorIdempotence
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Tactic.Basic
import Submission.WeilConjectures.CategoryTheory.RingedLocalizationFactorTensorAugmentation
import Submission.WeilConjectures.FromJoel.Algebra.Homology.Bifunctor
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationTensor
import Mathlib.RingTheory.Localization.BaseChange
import Submission.WeilConjectures.CategoryTheory.Ringed.RingedLocalizationModelsSupplement
import Submission.WeilConjectures.Algebra.Homology.KFlatComparison
import Submission.WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Submission.WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Submission.WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import Submission.WeilConjectures.Algebra.Homology.RingedInternalHomContravariantExact
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import Submission.WeilConjectures.Algebra.Homology.SixFunctors.BifunctorHomHomotopyExactSupplement
import Submission.WeilConjectures.Algebra.Homology.HomComplexInternalHomComparison
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Submission.WeilConjectures.CategoryTheory.Monoidal.Closed.IhomComparison
import Submission.WeilConjectures.Algebra.Homology.DerivedInternalHomShiftLeft
import Submission.WeilConjectures.AlgebraicGeometry.FiniteIdealGeneratingCover
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Sites.LocalProperties
import Submission.WeilConjectures.FromJoel.Algebra.Homology.Embedding.ComplementaryTrunc
import Submission.WeilConjectures.AlgebraicGeometry.ExtendedCechUnitIsoImpliesComplete
import Submission.WeilConjectures.CategoryTheory.RingedSiteCompleteElementsIdeal
import Submission.WeilConjectures.CategoryTheory.RingedSiteCompleteElement
import Submission.WeilConjectures.CategoryTheory.RingedSiteLocalization
import Mathlib.CategoryTheory.Sites.LeftExact
import Submission.WeilConjectures.CategoryTheory.RingedSiteDerivedRestriction
import Submission.WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import Mathlib.RingTheory.Ideal.Span
import Submission.WeilConjectures.CategoryTheory.RingedSiteCompleteElementMultiplication
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
import Submission.WeilConjectures.Algebra.Homology.HomTensorTotal
import Submission.WeilConjectures.CategoryTheory.RingedSiteCompleteElementAddition
import Submission.WeilConjectures.CategoryTheory.RingedSiteLocalizationCech
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Submission.WeilConjectures.RingTheory.ModuleLocalizationFilteredColimit
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Submission.WeilConjectures.RingTheory.TwoLocalizationExact
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Algebra.Exact.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import Submission.WeilConjectures.CategoryTheory.RingedSiteCompleteElementsLocal
import Submission.WeilConjectures.AlgebraicGeometry.LocalCompletenessModels
import Submission.WeilConjectures.CategoryTheory.LocalCoefficientLocalization
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.InternalHom
import Submission.WeilConjectures.CategoryTheory.SliceAwayLocalizationFreeResolution
import Submission.WeilConjectures.CategoryTheory.SliceAwayLocalization
import Mathlib.CategoryTheory.Sites.Over
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationFlat
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.RingTheory.Flat.Localization
import Submission.WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Submission.WeilConjectures.AlgebraicGeometry.FiniteGeneratorsLocalSpan
import Mathlib.CategoryTheory.Sites.Abelian
import Submission.WeilConjectures.CategoryTheory.FiniteSectionsEpiLift
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafSections
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Abelian.Exact
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Submission.WeilConjectures.AlgebraicGeometry.FunctorialRingComplexDescentData
import Submission.WeilConjectures.AlgebraicGeometry.FunctorialRingComplexSheaf
import Submission.WeilConjectures.AlgebraicGeometry.RingComplexCechData
import Submission.WeilConjectures.CategoryTheory.Ring.RingHomExtensionDefsSupplement
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.CategoryTheory.Adjunction.Additive
import Submission.WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Submission.WeilConjectures.CategoryTheory.AugmentedComplexGluing
import Submission.WeilConjectures.CategoryTheory.SiteModuleCompatibleTuples
import Mathlib.Algebra.Homology.Additive
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import Submission.WeilConjectures.AlgebraicGeometry.FunctorialRingComplexIdealDescent
import Submission.WeilConjectures.AlgebraicGeometry.RingFamilyLocallyEqualModels
import Submission.WeilConjectures.CategoryTheory.ModuleSheafificationLocalIso
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import Submission.WeilConjectures.AlgebraicGeometry.RingFamilyRestriction
import Submission.WeilConjectures.CategoryTheory.ModuleSheafificationRestriction
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import Submission.WeilConjectures.AlgebraicGeometry.RingedGeneratingListsLocalEquality
import Submission.WeilConjectures.AlgebraicGeometry.FunctorialRingComplexCechComparison
import Submission.WeilConjectures.AlgebraicGeometry.RingComplexGodementConstruction
import Submission.WeilConjectures.AlgebraicGeometry.ModuleCupGodementModel
import Submission.WeilConjectures.AlgebraicGeometry.Modules.FlatPullbackStalk
import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Submission.WeilConjectures.AlgebraicGeometry.ModuleCupGodementModelsExist
import Submission.WeilConjectures.AlgebraicGeometry.ModuleCupGodementCodegeneracies
import Submission.WeilConjectures.AlgebraicGeometry.ModuleCupGodementCosimplicialExists
import Submission.WeilConjectures.CategoryTheory.SimplexPresentationFaithful
import Submission.WeilConjectures.AlgebraicGeometry.ModuleCupGodementRelations
import Mathlib.AlgebraicTopology.SimplexCategory.GeneratorsRelations.Basic
import Submission.WeilConjectures.AlgebraicGeometry.ModuleCupGodementAugmentation
import Submission.WeilConjectures.Topology.RingedSpaceModuleCohomology
import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.AlgebraicGeometry.OpenImmersion
import Submission.WeilConjectures.AlgebraicGeometry.RingComplexGodementCech
import Submission.WeilConjectures.AlgebraicGeometry.FiniteOrderedFlasqueCechComparison
import Submission.WeilConjectures.CategoryTheory.DoubleComplexTotal
import Submission.WeilConjectures.CategoryTheory.CanonicalFiltration
import Submission.WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
import Mathlib.Topology.Sheaves.Flasque
import Submission.WeilConjectures.AlgebraicGeometry.FiniteOrderedFlasqueCechComparisonAlpha
import Submission.WeilConjectures.AlgebraicGeometry.FlasqueAlternatingCechRowAugmentation
import Submission.WeilConjectures.AlgebraicGeometry.AlternatingCechRestrictionHomotopy
import Submission.WeilConjectures.Topology.Sheaves.CechFlasque
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Submission.WeilConjectures.AlgebraicGeometry.InjectiveAlternatingCechRowAugmentation
import Submission.WeilConjectures.AlgebraicGeometry.InjectiveTermsAlternatingCechAugmentation
import Submission.WeilConjectures.AlgebraicGeometry.FiniteOrderedFlasqueCechComparisonBeta
import Submission.WeilConjectures.AlgebraicGeometry.FiniteOrderedCechCoefficientMap
import Submission.WeilConjectures.AlgebraicGeometry.FiniteOrderedCechTotalMap
import Submission.WeilConjectures.AlgebraicGeometry.QCohAlternatingCechResolutionQuasiIso
import Submission.WeilConjectures.AlgebraicGeometry.ModuleCupGodementModelQuasiIso
import Submission.WeilConjectures.AlgebraicGeometry.ModuleCupGodementStalkContraction
import Submission.WeilConjectures.Algebra.Homology.ModuleStalkFunctor
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Topology.Sheaves.Abelian
import Submission.WeilConjectures.Algebra.Homology.ModuleStalkExact
import Submission.WeilConjectures.AlgebraicGeometry.ModuleCupGodementObjectFlasque
import Submission.WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Types.Products
import Submission.WeilConjectures.AlgebraicGeometry.RingComplexOrderedCechCoordinates
import Submission.WeilConjectures.AlgebraicGeometry.RingComplexOrderedCechConstruction
import Submission.WeilConjectures.AlgebraicGeometry.RingComplexOrderedCechSectionCoordinates
import Submission.WeilConjectures.AlgebraicGeometry.RingComplexGodementAffineSections
import Submission.WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import Submission.WeilConjectures.AlgebraicGeometry.Cohomology.Flasque
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Submission.WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Submission.WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import Submission.WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Submission.WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Submission.WeilConjectures.AlgebraicGeometry.GlobalSectionRingFamilyBaseChange
import Submission.WeilConjectures.AlgebraicGeometry.GlobalSectionScalarExtension
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
import Submission.WeilConjectures.AlgebraicGeometry.RingComplexSemilinearExtension
import Submission.WeilConjectures.CategoryTheory.Ring.RingHomExtensionTransportSupplement
import Submission.WeilConjectures.AlgebraicGeometry.RingComplexCechBaseChange
import Submission.WeilConjectures.AlgebraicGeometry.RingComplexCechScalarModel
import Submission.WeilConjectures.AlgebraicGeometry.RingComplexOrderedScalarIso
import Submission.WeilConjectures.AlgebraicGeometry.RingComplexScalarAugmentation
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Submission.WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import Submission.WeilConjectures.AlgebraicGeometry.RingComplexCechAugmentationHom
import Submission.WeilConjectures.AlgebraicGeometry.RingComplexCechLocalizedOrthogonality
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Submission.WeilConjectures.AlgebraicGeometry.RingComplexCechCohomologyPowerTorsion
import Mathlib.Algebra.Category.ModuleCat.Descent
import Submission.WeilConjectures.AlgebraicGeometry.PowerTorsionLocalizedShiftHom
import Submission.WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import Mathlib.CategoryTheory.Adjunction.Limits
import Submission.WeilConjectures.FromJoel.Algebra.Homology.PreservesQuasiIso
import Submission.WeilConjectures.AlgebraicGeometry.RingComplexCechConeFiltration
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.BoundedComplexTriangulatedDevissage
import Mathlib.Algebra.Category.ModuleCat.Products
import Submission.WeilConjectures.AlgebraicGeometry.GlobalSectionScalarCechModel
import Submission.WeilConjectures.AlgebraicGeometry.GlobalSectionScalarKFlatQuasiIso
import Submission.WeilConjectures.AlgebraicGeometry.GlobalSectionOrderedCechTensor
import Submission.WeilConjectures.AlgebraicGeometry.GlobalSectionTensorBaseChange
import Submission.WeilConjectures.AlgebraicGeometry.RingTensorCechCoordinates
import Submission.WeilConjectures.AlgebraicGeometry.RingCechCoordinateTensorStep
import Submission.WeilConjectures.AlgebraicGeometry.RingLocalizationTensorBlocks
import Mathlib.LinearAlgebra.TensorProduct.Map
import Mathlib.LinearAlgebra.Prod
import Submission.WeilConjectures.AlgebraicGeometry.RingPointTensorComparison
import Submission.WeilConjectures.AlgebraicGeometry.RingCechAlgebraicConeCoordinates
import Submission.WeilConjectures.AlgebraicGeometry.RingCechConeLinearEquiv
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.Ring.Basic
import Mathlib.Order.Fin.SuccAboveOrderIso
import Mathlib.Order.Fin.Tuple
import Submission.WeilConjectures.AlgebraicGeometry.RingCechConeDifferential
import Submission.WeilConjectures.AlgebraicGeometry.GlobalSectionComplexMonoidal
import Mathlib.CategoryTheory.Monoidal.Closed.Braided
import Submission.WeilConjectures.AlgebraicGeometry.GlobalSectionModuleMonoidal
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
import Submission.WeilConjectures.AlgebraicGeometry.GlobalSectionModuleOplaxNormalized
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Presheaf.ScalarExtensionMonoidal
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.MonoidalCompat
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Submission.WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
import Submission.WeilConjectures.AlgebraicGeometry.GlobalSectionLocalizationFactor
import Submission.WeilConjectures.CategoryTheory.RingedKoszulFactorColimit
import Submission.WeilConjectures.CategoryTheory.RingedLocalizationFactorRestriction
import Submission.WeilConjectures.CategoryTheory.LocalizationRHom.RingedLocalizationRestrictionSupplement
import Submission.WeilConjectures.AlgebraicGeometry.RingComplexGodementFunctorial
import Submission.WeilConjectures.AlgebraicGeometry.ProperBaseChange.RingComplexGodementModelMapsSupplement
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Submission.WeilConjectures.AlgebraicGeometry.ExtendedCechCompletionModel

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!
# Global extended Cech model and its derived completion unit

Source: Stacks Project, algebraization.tex, Tags 099E and 099F
(blueprint: lem-weil-pbc-extended-cech-completion-model).
-/

@[expose] public section
set_option linter.privateModule false

universe u w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace CategoryTheory

private theorem compose_three_squares {D : Type*} [Category D]
    {A₁ A₂ B₁ B₂ C₁ C₂ D₁ D₂ : D}
    {f : A₁ ⟶ A₂} {g : B₁ ⟶ B₂} {h : C₁ ⟶ C₂} {k : D₁ ⟶ D₂}
    {a : A₁ ⟶ B₁} {a' : A₂ ⟶ B₂} {b : B₁ ⟶ C₁} {b' : B₂ ⟶ C₂}
    {c : C₁ ⟶ D₁} {c' : C₂ ⟶ D₂}
    (ha : f ≫ a' = a ≫ g) (hb : g ≫ b' = b ≫ h) (hc : h ≫ c' = c ≫ k) :
    f ≫ (a' ≫ b' ≫ c') = (a ≫ b ≫ c) ≫ k := by
  calc
    _ = (f ≫ a') ≫ b' ≫ c' := by simp only [Category.assoc]
    _ = a ≫ (g ≫ b') ≫ c' := by rw [ha]; simp only [Category.assoc]
    _ = a ≫ b ≫ (h ≫ c') := by rw [hb]; simp only [Category.assoc]
    _ = _ := by rw [hc]; simp only [Category.assoc]

set_option maxHeartbeats 1200000 in
-- Descending evaluation compares several expanded product-localization functors.
set_option backward.isDefEq.respectTransparency false in
private theorem unit_isIso_of_complete_universal
    {D : Type*} [Category D] (P : D → Prop) (F : D ⥤ D)
    (η : ∀ E, E ⟶ F.obj E)
    (hc : ∀ E, P (F.obj E))
    (hu : ∀ E L, P L → Function.Bijective (fun h : F.obj E ⟶ L ↦ η E ≫ h))
    (E : D) (hE : P E) : IsIso (η E) := by
  obtain ⟨r, hr⟩ := (hu E E hE).2 (𝟙 E)
  have hs : r ≫ η E = 𝟙 (F.obj E) := by
    apply (hu E (F.obj E) (hc E)).1
    simp only [← Category.assoc, hr, Category.id_comp, Category.comp_id]
  exact ⟨⟨r, hr, hs⟩⟩

end CategoryTheory
