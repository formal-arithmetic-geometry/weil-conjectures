/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImageCurrent
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Mathlib.Data.Finset.Max
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenFiltrationSuccessor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.ConstructibleSheaf.Devissage
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
public import WeilConjectures.AlgebraicGeometry.FiniteCondensedCtfEquivalence
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteScalarConstantModels
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
public import Mathlib.RingTheory.Finiteness.Projective
public import WeilConjectures.AlgebraicGeometry.EtaleLocallyConstantPerfectComplex
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Retract
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartOrderedRefinement
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.EtaleDomainPullbackCalculus
public import WeilConjectures.AlgebraicGeometry.EtaleLisseCtfPerfectLocalModel
public import WeilConjectures.AlgebraicGeometry.RefinementPreservesFiniteLisse
public import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
public import WeilConjectures.ConstructibleSheaf.KernelCokernel
public import WeilConjectures.ConstructibleSheaf.Refinement
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.SixFunctors.OpenClosed.Complex
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
public import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
public import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartGeneration
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
public import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
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
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
public import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
public import WeilConjectures.Compactification.Dense
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedSiteComparison
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction
public import WeilConjectures.CategoryTheory.Monoidal.Closed.EvaluationBidualComparisonTransport
public import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BidualityCoefficients
public import WeilConjectures.CategoryTheory.ObjectProperty.Duality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
public import WeilConjectures.SixFunctors.Etale.Derived.Stability.Typing
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperShriekPreservation
public import WeilConjectures.AlgebraicGeometry.FiniteRingHomTorBound
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.SitePerfectComplex
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
import WeilConjectures.TraceFormula.CategoricalTraceBiproduct
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.DualizableProjectiveUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedDualizableIndependent
import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.AlgebraicGeometry.SixFunctors.SiteHomComparisonThick
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenCover
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimension
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import Mathlib.Data.Finset.Max
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenFiltrationSuccessor
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.ConstructibleSheaf.Devissage
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.AlgebraicGeometry.CondensedIntegralCriterion
import WeilConjectures.AlgebraicGeometry.FiniteCondensedCtfEquivalence
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteScalarConstantModels
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
import Mathlib.RingTheory.Finiteness.Projective
import WeilConjectures.AlgebraicGeometry.EtaleLocallyConstantPerfectComplex
import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.Retract
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartOrderedRefinement
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.EtaleDomainPullbackCalculus
import WeilConjectures.AlgebraicGeometry.EtaleLisseCtfPerfectLocalModel
import WeilConjectures.AlgebraicGeometry.RefinementPreservesFiniteLisse
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingPullbackFixed
import WeilConjectures.SixFunctors.ProEtale.Comparison.UpperStar
import WeilConjectures.SixFunctors.ProEtale.Comparison.ConstantSheaf
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartGeneration
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Braided
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Triangulated.Opposite.Pretriangulated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.AlgebraicGeometry.SixFunctors.DualityPairing
import WeilConjectures.Compactification.Dense
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedSiteComparison
import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
import WeilConjectures.SixFunctors.Etale.Derived.GeometricBidualityInduction
import WeilConjectures.CategoryTheory.Monoidal.Closed.EvaluationBidualComparisonTransport
import WeilConjectures.AlgebraicGeometry.Base.BaseFieldCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ExceptionalInverseImageCurrent
import WeilConjectures.AlgebraicGeometry.ProEtale.Extension.ProEtaleExtensionZeroComparison
import WeilConjectures.SixFunctors.Etale.Derived.DoubleDual
import WeilConjectures.CategoryTheory.FiniteCondensedNormalizedAdjunction
import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeTensorComparison
import WeilConjectures.SixFunctors.Etale.Derived.VerdierBiduality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
import Mathlib.CategoryTheory.Yoneda
import WeilConjectures.CategoryTheory.Constant.ConstantScalarRestrictionTensorSupplement
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Triangulated.Opposite.OpOp
import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedHomSignedExact
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
import WeilConjectures.SixFunctors.Etale.Derived.ClosedSupportAssembly
import WeilConjectures.ZetaWeil.PodCtfAdjunctionData.PodCtfAdjunctions
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleOrigin

/-! # Current six-operation typing table

Source: latest blueprint, sk-rem-sf-typing.md, all eight rows and its enumeration sentence
(blueprint: sk-rem-sf-typing). The standing coefficients are pulled-back condensed rings;
all ambient categories are ordinary uncompleted derived categories. Finite coefficients
are arbitrary finite commutative ell-primary rings, including the zero ring.

The declarations below are the clauses of the table, not new operations. `etaleWindow`
and `proetaleWindow` only abbreviate its two interval assertions. Finite-site statements
are read in the existing ordinary constant-ring presentation, identified with internal
modules by the recorded normalized coefficient equivalence. The optional ambient pro-etale
right adjoint is neither assumed nor asserted.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj MonoidalCategory
open CategoryTheory.Pretriangulated CategoryTheory.Pretriangulated.Opposite

namespace AlgebraicGeometry.SixOperationsTyping

set_option quotPrecheck false in
local notation "dim₀(" T ")" => ((topologicalKrullDim T).unbotD 0).toNat

/-- The two exceptional bounds in the table: constructible cohomological intervals and
constructible Tor intervals, with the same endpoints.
Source: latest blueprint, exceptional row (blueprint: sk-rem-sf-typing). -/
def etaleWindow (A : Type (u + 1)) [CommRing A] (X Y : Scheme.{u})
    (F : Etale.DerivedCategoryModule A Y ⥤ Etale.DerivedCategoryModule A X)
    (a b c d : ℤ) : Prop :=
  (∀ K : Etale.DerivedCategoryModule A Y,
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Y K →
    DerivedCategory.homologyConcentratedIn a b K →
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X (F.obj K) ∧
      DerivedCategory.homologyConcentratedIn c d (F.obj K)) ∧
  (∀ K : Etale.DerivedCategoryModule A Y,
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Y K →
    Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) Y a b K →
    Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X (F.obj K) ∧
      Etale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) X c d (F.obj K))

/-- The same two bounds in the ordinary pro-etale presentation of finite coefficients.
Source: latest blueprint, exceptional row and finite comparison
(blueprint: sk-rem-sf-typing). -/
def proetaleWindow (A : Type (u + 1)) [CommRing A] (X Y : Scheme.{u})
    (F : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)) ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A)))
    (a b c d : ℤ) : Prop :=
  (∀ K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)),
    ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Y K →
    DerivedCategory.homologyConcentratedIn a b K →
    ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X (F.obj K) ∧
      DerivedCategory.homologyConcentratedIn c d (F.obj K)) ∧
  (∀ K : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} A)),
    ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Y K →
    ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) Y a b K →
    ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X (F.obj K) ∧
      ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat.{u + 1} A) X c d (F.obj K))

private theorem realizedBoundedConstructible_iff
    (B : Type) [CommRing B] [TopologicalSpace B] [DiscreteTopology B]
    [IsTopologicalRing B] [Finite B] (T : Scheme.{u})
    [CompactSpace T] [QuasiSeparatedSpace T]
    (eR : Sheaf.sheafifyRingPresheaf.{u + 1, u, u + 1} (coherentTopology Profinite.{u})
      ((Functor.const Profinite.{u}ᵒᵖ).obj (RingCat.of (ULift.{u + 1} B))) ≅
        Profinite.continuousMapRingObj.{u} B) [IsMonHom eR.hom]
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology T)
      (ModuleCat.{u + 1} (ULift.{u + 1} B)))) :
    ProEtale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} (ULift.{u + 1} B)) T K ↔
      ProEtale.constantModelBoundedConstructible (Profinite.continuousMapRingObj B) T
        ((ProEtale.finiteComparisonRealization B T eR).mapDerivedCategory.obj K) := by
  let G := ProEtale.finiteComparisonRealization B T eR
  have : G.IsEquivalence := (ProEtale.finiteComparisonRealization_exact B T eR).1
  rw [← ProEtale.DerivedCategory.boundedConstructibleIntrinsic_eq]
  let : ObjectProperty.IsClosedUnderIsomorphisms (ProEtale.IsConstantModelConstructible
      (Profinite.continuousMapRingObj B) T) :=
    (ProEtale.constantModelConstructibleFiniteTor_wellDefined _ T).1
  constructor
  · rintro ⟨hb, hc⟩
    refine ⟨G.bounded_mapDerivedCategory_obj hb, fun q ↦ ?_⟩
    have h := (ProEtale.realized_constructible_iff B T eR _).1 (hc q)
    exact ObjectProperty.prop_of_iso (ProEtale.IsConstantModelConstructible _ T)
      ((G.mapDerivedCategoryHomologyFunctorIso q).app K) h
  · intro h
    refine ⟨G.bounded_of_bounded_mapDerivedCategory_obj h.1, fun q ↦ ?_⟩
    apply (ProEtale.realized_constructible_iff B T eR _).2
    exact ObjectProperty.prop_of_iso (ProEtale.IsConstantModelConstructible _ T)
      ((G.mapDerivedCategoryHomologyFunctorIso q).app K).symm (h.2 q)

private theorem finiteMixedTensor
    (B : Type) [CommRing B] [TopologicalSpace B] [DiscreteTopology B]
    [IsTopologicalRing B] [Finite B] (T : Scheme.{u})
    [CompactSpace T] [QuasiSeparatedSpace T]
    (K M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (ProEtale.condensedRingObj (Profinite.continuousMapRingObj B) T)))
    (hK : ProEtale.constantModelBoundedConstructible (Profinite.continuousMapRingObj B) T K ∧
      DerivedCategory.finiteTorAmplitude _ K)
    (hM : ProEtale.constantModelBoundedConstructible (Profinite.continuousMapRingObj B) T M) :
    ProEtale.constantModelBoundedConstructible (Profinite.continuousMapRingObj B) T
      (((ProEtale.CondensedRing.derivedTensor
        (Profinite.continuousMapRingObj B) T).obj K).obj M) := by
  obtain ⟨eR, heR⟩ := Profinite.finiteDiscreteCondensedRing_constant.{u} B
  let := heR
  let G := ProEtale.finiteComparisonRealization B T eR
  have : G.IsEquivalence := (ProEtale.finiteComparisonRealization_exact B T eR).1
  obtain ⟨hG⟩ := ProEtale.finiteRealizationMonoidal_exists B T eR
  let := hG
  have : G.PreservesFlat := Functor.preservesFlat_of_isEquivalence G
  let F := G.mapDerivedCategory
  let K₀ := F.objPreimage K
  let M₀ := F.objPreimage M
  let eK := F.objObjPreimageIso K
  let eM := F.objObjPreimageIso M
  let P := ProEtale.constantModelBoundedConstructible (Profinite.continuousMapRingObj B) T
  let : P.IsClosedUnderIsomorphisms :=
    (ProEtale.constantModelConstructibleFiniteTor_wellDefined _ T).2.1
  have hK₀ := (realizedBoundedConstructible_iff B T eR K₀).2
    (P.prop_of_iso eK.symm hK.1)
  have hM₀ := (realizedBoundedConstructible_iff B T eR M₀).2
    (P.prop_of_iso eM.symm hM)
  have hKt₀ : DerivedCategory.finiteTorAmplitude _ K₀ := by
    obtain ⟨a, b, ht⟩ := hK.2
    refine ⟨a, b, (DerivedCategory.torAmplitudeIn_mapDerivedCategory_obj_iff G a b K₀).1 ?_⟩
    exact (DerivedCategory.torAmplitudeIn _ a b).prop_of_iso eK.symm ht
  obtain ⟨K', hK', ⟨dK⟩⟩ := hK₀
  obtain ⟨M', hM', ⟨dM⟩⟩ := hM₀
  obtain ⟨a, b, ht⟩ := hKt₀
  have ht' := (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b K').1
    ((ProEtale.DerivedCategory.torAmplitudeIn _ T a b).prop_of_iso dK.symm ht)
  let : BraidedCategory (Etale.DerivedCategoryModule (ULift.{u + 1} B) T) :=
    DerivedCategory.braidedCategory' _
  have hN := (Etale.DerivedCategory.boundedConstructible _ T).prop_of_iso (β_ M' K')
    (Etale.boundedConstructible_tensor _ T hM' hK' ⟨a, b, ht'⟩)
  have hNp :=
    ProEtale.DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj hN
  let t := (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
    (ModuleCat.{u + 1} (ULift.{u + 1} B)) K').app M' ≪≫
      MonoidalCategory.tensorIso dK dM
  have hT := (ProEtale.DerivedCategory.boundedConstructible _ T).prop_of_iso t hNp
  apply P.prop_of_iso
    ((DerivedCategory.tensorLeftCompMapDerivedCategoryIso G K₀).app M₀ ≪≫
      MonoidalCategory.tensorIso eK eM)
  exact (realizedBoundedConstructible_iff B T eR _).1 hT

private theorem mixedTensorCoefficientIso
    {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
    [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
    (e : Mon.mk Λ ≅ Mon.mk Λ') (T : Scheme.{u})
    (h : ∀ K M, (ProEtale.constantModelBoundedConstructible Λ' T K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      ProEtale.constantModelBoundedConstructible Λ' T M →
      ProEtale.constantModelBoundedConstructible Λ' T
        (((ProEtale.CondensedRing.derivedTensor Λ' T).obj K).obj M)) :
    ∀ K M, (ProEtale.constantModelBoundedConstructible Λ T K ∧
        DerivedCategory.finiteTorAmplitude _ K) →
      ProEtale.constantModelBoundedConstructible Λ T M →
      ProEtale.constantModelBoundedConstructible Λ T
        (((ProEtale.CondensedRing.derivedTensor Λ T).obj K).obj M) := by
  let φ := e.inv.hom
  have : IsIso φ := inferInstanceAs (IsIso e.inv.hom)
  let F := Mod.comap (D := Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (ProEtale.coefficientMap φ T)
  have : F.IsEquivalence :=
    inferInstanceAs (Mod.comapEquivalenceOfIsIso
      (ProEtale.coefficientMap φ T)).functor.IsEquivalence
  let : (ProEtale.constantModelBoundedConstructible Λ' T).IsClosedUnderIsomorphisms :=
    (ProEtale.constantModelConstructibleFiniteTor_wellDefined Λ' T).2.1
  intro K M hK hM
  apply (ProEtale.CondensedRing.constantModel_derived_comap_iff φ T _).mp
  apply (ProEtale.constantModelBoundedConstructible Λ' T).prop_of_iso
    ((DerivedCategory.tensorLeftCompMapDerivedCategoryIso F K).app M).symm
  exact h _ _ (ProEtale.constantModelCtf_coefficientIso e T ⟨K, hK⟩)
    ((ProEtale.CondensedRing.constantModel_derived_comap_iff φ T M).2 hM)

section Condensed
open ProEtale ProEtale.CondensedRing
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
local notation "BC(" T ")" => constantModelBoundedConstructible Λ T
local notation "CTF(" T ")" =>
  (constantModelBoundedConstructible Λ T ⊓ DerivedCategory.finiteTorAmplitude _)

end Condensed

private theorem finiteCoefficientExponent
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    (hne : ringChar k ≠ ell) (A : Type (u + 1)) [CommRing A]
    (hA : ∃ r : ℕ, 1 ≤ r ∧ (ell : A) ^ r = 0) :
    HasInvertibleExponent A (Spec (.of k)) := by
  obtain ⟨r, _, hkill⟩ := hA
  refine ⟨ell ^ r, pow_pos (Fact.out : ell.Prime).pos r, ?_, ?_⟩
  · simpa only [Nat.cast_pow] using hkill
  · have hunit : (ell : k) ≠ 0 := by
      intro hzero
      exact hne (CharP.ringChar_of_prime_eq_zero (Fact.out : ell.Prime) hzero)
    simpa using (((isUnit_iff_ne_zero.mpr hunit).pow r).map
      (Scheme.ΓSpecIso (.of k)).inv.hom)

private theorem finiteDimensionBound {k : Type u} [Field k] {T : Scheme.{u}}
    (aT : T ⟶ Spec (.of k)) [LocallyOfFiniteType aT] [QuasiCompact aT] :
    topologicalKrullDim T ≤
      (((topologicalKrullDim T).unbotD 0).toNat : WithBot ℕ∞) := by
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_le aT
  have hfinite : (topologicalKrullDim T).unbotD 0 ≠ ⊤ := by
    apply ne_top_of_le_ne_top (show (n : ℕ∞) ≠ ⊤ by simp)
    exact (WithBot.unbotD_le_iff (by simp)).2 hn
  change topologicalKrullDim T ≤
    ((((topologicalKrullDim T).unbotD 0).toNat : ℕ∞) : WithBot ℕ∞)
  rw [ENat.natCast_toNat hfinite]
  exact WithBot.le_coe_unbotD _ _

/-- Transport both exceptional windows through the finite comparison. -/
private theorem proetaleExceptionalWindow
    (A : Type (u + 1)) [CommRing A] [Finite A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [HasCompactification f] (a b c d : ℤ)
    (h : etaleWindow A X Y (Etale.rightDerivedUpperShriek A f) a b c d) :
    proetaleWindow A X Y (ProEtale.rightDerivedUpperShriek A f) a b c d := by
  refine ⟨?_, ?_⟩
  · intro K hK hKab
    obtain ⟨G, hG, ⟨e⟩⟩ := hK
    have hGab := Functor.homologyConcentratedIn_of_homologyConcentratedIn_mapDerivedCategory_obj
      (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y)
      ((DerivedCategory.homologyConcentratedIn a b).prop_of_iso e.symm hKab)
    have hF := h.1 G hG hGab
    let E := (ProEtale.rightDerivedUpperShriek A f).mapIso e.symm ≪≫
      ProEtale.rightDerivedUpperShriekMapDerivedCategoryObjIso f G hG.1.1
    exact ⟨(ProEtale.DerivedCategory.boundedConstructible _ X).prop_of_iso E.symm
        (ProEtale.DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
          hF.1),
      (DerivedCategory.homologyConcentratedIn c d).prop_of_iso E.symm
        (Functor.homologyConcentratedIn_mapDerivedCategory_obj _ hF.2)⟩
  · intro K hK hKt
    obtain ⟨G, hG, ⟨e⟩⟩ := hK
    have hGt := (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b G).1
      ((ProEtale.DerivedCategory.torAmplitudeIn _ Y a b).prop_of_iso e.symm hKt)
    have hF := h.2 G hG hGt
    let E := (ProEtale.rightDerivedUpperShriek A f).mapIso e.symm ≪≫
      ProEtale.rightDerivedUpperShriekMapDerivedCategoryObjIso f G hG.1.1
    exact ⟨(ProEtale.DerivedCategory.boundedConstructible _ X).prop_of_iso E.symm
        (ProEtale.DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
          hF.1),
      (ProEtale.DerivedCategory.torAmplitudeIn _ X c d).prop_of_iso E.symm
        ((ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff c d _).2 hF.2)⟩

section Finite
variable (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
  (hk : Finite k ∨ IsAlgClosed k)
  (A : Type (u + 1)) [CommRing A] [Finite A]
  (hA : ∃ r : ℕ, 1 ≤ r ∧ (ell : A) ^ r = 0)
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

include hk hA

set_option quotPrecheck false in
local notation "EtaleD(" T ")" =>
  DerivedCategory (Sheaf (Scheme.smallEtaleTopology T) (ModuleCat A))
set_option quotPrecheck false in
local notation "EtaleBC(" T ")" =>
  Etale.DerivedCategory.boundedConstructible (ModuleCat A) T
set_option quotPrecheck false in
local notation "EtaleTor(" T ")" =>
  Etale.DerivedCategory.torAmplitudeIn (ModuleCat A) T

/-- Finite pullback and tensor rows on the Etale site, including the mixed cohomological
bound and the sum of Tor intervals.
Source: latest blueprint, pullback and tensor rows (blueprint: sk-rem-sf-typing).

Proof: exact cartesian inverse image preserves finite scalar local models and bounded
constructible cohomology. Resolve the first tensor argument by a bounded flat constructible
model, refine the finite term/cohomology stratifications, and use its stupid filtration.
For the mixed interval apply the source tensor-cohomology interval lemma. Test with an
arbitrary degree-zero module and use tensor associativity to obtain the Tor sum interval.
The normalized finite coefficient and site comparisons identify both site presentations. -/
theorem finiteEtalePullbackTensorTyping :
    (∀ K : EtaleD(Y.left), EtaleBC(Y.left) K →
      EtaleBC(X.left)
        ((Etale.upperStar (ModuleCat.{u + 1} A) f.left).leftDerivedFunctor.obj K)) ∧
    (∀ K : EtaleD(Y.left), EtaleBC(Y.left) K →
      DerivedCategory.finiteTorAmplitude _ K →
      DerivedCategory.finiteTorAmplitude _
        ((Etale.upperStar (ModuleCat.{u + 1} A) f.left).leftDerivedFunctor.obj K)) ∧
    (∀ K L : EtaleD(Y.left),
      EtaleBC(Y.left) K → DerivedCategory.finiteTorAmplitude _ K →
      EtaleBC(Y.left) L →
      EtaleBC(Y.left) (((Etale.derivedTensor (ModuleCat.{u + 1} A) Y.left).obj K).obj L)) ∧
    (∀ (a b c d : ℤ) (K L : EtaleD(Y.left)),
      a ≤ b → c ≤ d → EtaleBC(Y.left) K → EtaleBC(Y.left) L →
      EtaleTor(Y.left) a b K → EtaleTor(Y.left) c d L →
      EtaleTor(Y.left) (a + c) (b + d)
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) Y.left).obj K).obj L)) ∧
    (∀ (a b c d : ℤ) (K L : EtaleD(Y.left)),
      a ≤ b → c ≤ d → EtaleBC(Y.left) K → EtaleTor(Y.left) a b K →
      EtaleBC(Y.left) L → DerivedCategory.homologyConcentratedIn c d L →
      EtaleBC(Y.left) (((Etale.derivedTensor (ModuleCat.{u + 1} A) Y.left).obj K).obj L) ∧
      DerivedCategory.homologyConcentratedIn (a + c) (b + d)
        (((Etale.derivedTensor (ModuleCat.{u + 1} A) Y.left).obj K).obj L)) := by
  letI : BraidedCategory (EtaleD(Y.left)) := DerivedCategory.braidedCategory' _
  have htensor (K L : EtaleD(Y.left)) (hK : EtaleBC(Y.left) K)
      (hKt : DerivedCategory.finiteTorAmplitude _ K) (hL : EtaleBC(Y.left) L) :
      EtaleBC(Y.left) (((Etale.derivedTensor (ModuleCat.{u + 1} A) Y.left).obj K).obj L) := by
    exact (Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Y.left).prop_of_iso
      (β_ L K) (Etale.boundedConstructible_tensor A Y.left hL hK hKt)
  refine ⟨fun K hK ↦ Etale.boundedConstructible_leftDerivedUpperStar _ f.left hK,
    ?_, htensor, ?_, ?_⟩
  · rintro K hK ⟨a, b, hKt⟩
    exact ⟨a, b, Etale.torAmplitudeIn_leftDerivedUpperStar _ f.left a b hKt⟩
  · intro a b c d K L hab hcd hK hL hKt hLt
    exact Etale.torAmplitudeIn_tensor _ Y.left a b c d hKt hLt
  · intro a b c d K L hab hcd hK hKt hL hLc
    exact ⟨htensor K L hK ⟨a, b, hKt⟩ hL,
      DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_left hKt hLc⟩

set_option quotPrecheck false in
local notation "ProEtaleD(" T ")" =>
  DerivedCategory (Sheaf (Scheme.ProEt.topology T) (ModuleCat A))
set_option quotPrecheck false in
local notation "ProEtaleBC(" T ")" =>
  ProEtale.DerivedCategory.boundedConstructible (ModuleCat A) T
set_option quotPrecheck false in
local notation "ProEtaleTor(" T ")" =>
  ProEtale.DerivedCategory.torAmplitudeIn (ModuleCat A) T

/-- Finite pullback and tensor rows on the ProEtale site, including the mixed cohomological
bound and the sum of Tor intervals.
Source: latest blueprint, pullback and tensor rows (blueprint: sk-rem-sf-typing).

Proof: exact cartesian inverse image preserves finite scalar local models and bounded
constructible cohomology. Resolve the first tensor argument by a bounded flat constructible
model, refine the finite term/cohomology stratifications, and use its stupid filtration.
For the mixed interval apply the source tensor-cohomology interval lemma. Test with an
arbitrary degree-zero module and use tensor associativity to obtain the Tor sum interval.
The normalized finite coefficient and site comparisons identify both site presentations. -/
theorem finiteProEtalePullbackTensorTyping :
    (∀ K : ProEtaleD(Y.left), ProEtaleBC(Y.left) K →
      ProEtaleBC(X.left)
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) f.left).leftDerivedFunctor.obj K)) ∧
    (∀ K : ProEtaleD(Y.left), ProEtaleBC(Y.left) K →
      DerivedCategory.finiteTorAmplitude _ K →
      DerivedCategory.finiteTorAmplitude _
        ((ProEtale.upperStar (ModuleCat.{u + 1} A) f.left).leftDerivedFunctor.obj K)) ∧
    (∀ K L : ProEtaleD(Y.left),
      ProEtaleBC(Y.left) K → DerivedCategory.finiteTorAmplitude _ K →
      ProEtaleBC(Y.left) L →
      ProEtaleBC(Y.left) (((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y.left).obj K).obj L)) ∧
    (∀ (a b c d : ℤ) (K L : ProEtaleD(Y.left)),
      a ≤ b → c ≤ d → ProEtaleBC(Y.left) K → ProEtaleBC(Y.left) L →
      ProEtaleTor(Y.left) a b K → ProEtaleTor(Y.left) c d L →
      ProEtaleTor(Y.left) (a + c) (b + d)
        (((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y.left).obj K).obj L)) ∧
    (∀ (a b c d : ℤ) (K L : ProEtaleD(Y.left)),
      a ≤ b → c ≤ d → ProEtaleBC(Y.left) K → ProEtaleTor(Y.left) a b K →
      ProEtaleBC(Y.left) L → DerivedCategory.homologyConcentratedIn c d L →
      ProEtaleBC(Y.left) (((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y.left).obj K).obj L) ∧
      DerivedCategory.homologyConcentratedIn (a + c) (b + d)
        (((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y.left).obj K).obj L)) := by
  letI : BraidedCategory (EtaleD(Y.left)) := DerivedCategory.braidedCategory' _
  have htensor (K L : ProEtaleD(Y.left)) (hK : ProEtaleBC(Y.left) K)
      (hKt : DerivedCategory.finiteTorAmplitude _ K) (hL : ProEtaleBC(Y.left) L) :
      ProEtaleBC(Y.left)
        (((ProEtale.derivedTensor (ModuleCat.{u + 1} A) Y.left).obj K).obj L) := by
    obtain ⟨K₀, hK₀, ⟨eK⟩⟩ := hK
    obtain ⟨L₀, hL₀, ⟨eL⟩⟩ := hL
    obtain ⟨a, b, hKt⟩ := hKt
    have hKt₀ := (ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff a b K₀).1
      ((ProEtale.DerivedCategory.torAmplitudeIn _ Y.left a b).prop_of_iso eK.symm hKt)
    have hT := (Etale.DerivedCategory.boundedConstructible _ Y.left).prop_of_iso
      (β_ L₀ K₀) (Etale.boundedConstructible_tensor A Y.left hL₀ hK₀ ⟨a, b, hKt₀⟩)
    let e := (ProEtale.derivedTensorObjCompMapDerivedCategoryComparisonUpperStarIso
      (ModuleCat.{u + 1} A) K₀).app L₀ ≪≫ CategoryTheory.MonoidalCategory.tensorIso eK eL
    exact (ProEtale.DerivedCategory.boundedConstructible _ Y.left).prop_of_iso e
      (ProEtale.DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
        hT)
  refine ⟨fun K hK ↦ ProEtale.boundedConstructible_leftDerivedFunctor_upperStar_obj
      f.left hK, ?_, htensor, ?_, ?_⟩
  · rintro K hK ⟨a, b, hKt⟩
    exact ⟨a, b, ProEtale.torAmplitudeIn_leftDerivedUpperStar _ f.left a b hKt⟩
  · intro a b c d K L hab hcd hK hL hKt hLt
    exact DerivedCategory.torAmplitudeIn_tensor hKt hLt
  · intro a b c d K L hab hcd hK hKt hL hLc
    exact ⟨htensor K L hK ⟨a, b, hKt⟩ hL,
      DerivedCategory.homologyConcentratedIn_tensor_of_torAmplitudeIn_left hKt hLc⟩

omit hk hA in
private lemma finiteBoundedConstructible_iff
    (T : Scheme.{u}) (K : Etale.DerivedCategoryModule A T) :
    Etale.DerivedCategory.isBoundedConstructible A T K ↔
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) T K := by
  constructor
  · rintro ⟨hc, a, b, hab, hz⟩
    refine ⟨⟨⟨a, ?_⟩, ⟨b, ?_⟩⟩, fun i ↦ ?_⟩
    · exact (DerivedCategory.isGE_iff K a).2 fun i hi ↦ hz i (.inl hi)
    · exact (DerivedCategory.isLE_iff K b).2 fun i hi ↦ hz i (.inr hi)
    · exact (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).1 (hc i)
  · rintro ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hc⟩
    refine ⟨fun i ↦ (Scheme.isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf _).2
      (hc i), min a b, b, min_le_right _ _, fun i hi ↦ ?_⟩
    rcases hi with hi | hi
    · exact (DerivedCategory.isGE_iff K a).1 ha i (hi.trans_le (min_le_left _ _))
    · exact (DerivedCategory.isLE_iff K b).1 hb i hi

/-- Internal Hom for arbitrary etale pairs and their pro-etale pullbacks. The perfect
improvement uses site-perfectness, not stalkwise perfectness.
Source: latest blueprint, internal-Hom row (blueprint: sk-rem-sf-typing).

Proof: the internal Hom is bounded below. The evaluation-transpose comparison identifies
its pullback with condensed internal Hom, which is Dctf by stability. Full faithfulness
on bounded-below objects and bounded constructible origin recover bounded constructibility
on etale, and finite-Tor comparison reflects Tor amplitude. The finite-ring Hom Tor bound
gives the dimension interval, improved by the finite-projective dual window for a
site-perfect first input. The same evaluation comparison transfers the bounds to proetale.
-/
theorem finiteInternalHomTyping (m : ℕ)
    (hm : topologicalKrullDim Y.left ≤ (m : WithBot ℕ∞))
    (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d)
    (K L : EtaleD(Y.left))
    (hK : EtaleBC(Y.left) K) (hKt : EtaleTor(Y.left) a b K)
    (hL : EtaleBC(Y.left) L) (hLt : EtaleTor(Y.left) c d L) :
    let H := ((Etale.derivedHom (ModuleCat.{u + 1} A) Y.left).obj (op K)).obj L
    let ν := (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} A) Y.left).mapDerivedCategory
    let Hp := ((ProEtale.derivedHom (ModuleCat.{u + 1} A) Y.left).obj
      (op (ν.obj K))).obj (ν.obj L)
    (EtaleBC(Y.left) H ∧
      EtaleTor(Y.left) (c - b - 2 * m) (d - a + 2 * m) H) ∧
    (ProEtaleBC(Y.left) Hp ∧
      ProEtaleTor(Y.left) (c - b - 2 * m) (d - a + 2 * m) Hp) ∧
    (Etale.DerivedCategory.IsSitePerfect K →
      EtaleTor(Y.left) (c - b) (d - a) H ∧
      ProEtaleTor(Y.left) (c - b) (d - a) Hp) := by
  obtain ⟨r, hr, hkill⟩ := hA
  have hellk : (ell : k) ≠ 0 := fun h ↦
    (Fact.out : ringChar k ≠ ell)
      (CharP.ringChar_of_prime_eq_zero (Fact.out : ell.Prime) h)
  letI : HasInvertibleExponent A (Spec (.of k)) := by
    refine ⟨ell ^ r, pow_pos (Fact.out : ell.Prime).pos r, ?_, ?_⟩
    · simpa only [Nat.cast_pow] using hkill
    · have hu : IsUnit ((ell ^ r : ℕ) : k) := by
        simpa only [Nat.cast_pow] using hellk.isUnit.pow r
      simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of k)).inv.hom
  letI : HasInvertibleExponent A Y.left := .of_hom Y.hom
  letI : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  letI : IsNoetherian Y.left :=
    { __ := LocallyOfFiniteType.isLocallyNoetherian Y.hom }
  have hK' := (finiteBoundedConstructible_iff A Y.left K).2 hK
  have hL' := (finiteBoundedConstructible_iff A Y.left L).2 hL
  have hKt' := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 hKt
  have hLt' := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.2 hLt
  have hH := Etale.constructibleFiniteTor_derivedHom_of_field A Y.hom
    ⟨hK, a, b, hKt⟩ ⟨hL, c, d, hLt⟩
  have hkill' (x : A) : (ell ^ r) • x = 0 := by
    rw [nsmul_eq_mul, Nat.cast_pow, hkill, zero_mul]
  obtain ⟨hbound, hperfect⟩ := Etale.finiteRingHomTorBound (ringChar k) ell hk
    (Fact.out : ringChar k ≠ ell) A r hr hkill' Y.hom m hm hab hcd
    hK' hKt' hL' hLt'
  have hbound' := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 hbound
  have hcomp := (ProEtale.DerivedCategory.isIso_finiteSiteInternalHomComparison
    A K L hK' ⟨a, b, hKt'⟩ hL.1.1).1
  letI := hcomp
  let e := asIso (ProEtale.siteComparisonEvaluationHom (ModuleCat.{u + 1} A)
    Y.left K L)
  have hprobc := (ProEtale.DerivedCategory.boundedConstructible _ Y.left).prop_of_iso e
    (ProEtale.DerivedCategory.boundedConstructible_comparisonUpperStar_mapDerivedCategory_obj
      hH.1)
  have hprotor := (ProEtale.DerivedCategory.torAmplitudeIn _ Y.left
    (c - b - 2 * m) (d - a + 2 * m)).prop_of_iso e
      ((ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff _ _ _).2 hbound')
  refine ⟨⟨hH.1, hbound'⟩, ⟨hprobc, hprotor⟩, ?_⟩
  intro hp
  have ht := Etale.DerivedCategory.hasTorAmplitudeIn_iff_torAmplitudeIn.1 (hperfect hp)
  exact ⟨ht, (ProEtale.DerivedCategory.torAmplitudeIn _ Y.left
    (c - b) (d - a)).prop_of_iso e
      ((ProEtale.DerivedCategory.torAmplitudeIn_mapDerivedCategory_iff _ _ _).2 ht)⟩

/-- Compact-support finiteness at finite coefficients, with the chosen compactification.
Source: latest blueprint, compact-support row (blueprint: sk-rem-sf-typing).

Proof: the chosen Nagata compactification gives Rp_* j_!. Open extension by zero preserves
constructibility and is exact; proper direct-image finiteness supplies bounded constructible
output. Apply finite-Tor stability and the ordinary site and module-object comparisons
for the all-coefficient Dctf assertion, which is recorded separately above. -/
theorem finiteCompactSupportTyping :
    (∀ K : EtaleD(X.left), EtaleBC(X.left) K →
      EtaleBC(Y.left)
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (ProEtale.CondensedRing.compactificationOverField f)).obj K)) ∧
    (∀ K : EtaleD(X.left), EtaleBC(X.left) K →
      DerivedCategory.finiteTorAmplitude _ K →
      DerivedCategory.finiteTorAmplitude _
        ((Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A)
          (ProEtale.CondensedRing.compactificationOverField f)).obj K) ∧
      DerivedCategory.finiteTorAmplitude _
        ((Etale.lowerStar (ModuleCat.{u + 1} A) f.left).rightDerivedFunctor.obj K)) := by
  obtain ⟨r, hr, hkill⟩ := hA
  have hellk : (ell : k) ≠ 0 := fun h ↦
    (Fact.out : ringChar k ≠ ell)
      (CharP.ringChar_of_prime_eq_zero (Fact.out : ell.Prime) h)
  letI : HasInvertibleExponent A (Spec (.of k)) := by
    refine ⟨ell ^ r, pow_pos (Fact.out : ell.Prime).pos r, ?_, ?_⟩
    · simpa only [Nat.cast_pow] using hkill
    · have hu : IsUnit ((ell ^ r : ℕ) : k) := by
        simpa only [Nat.cast_pow] using hellk.isUnit.pow r
      simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of k)).inv.hom
  letI : HasInvertibleExponent A X.left := .of_hom X.hom
  letI : HasInvertibleExponent A Y.left := .of_hom Y.hom
  letI : HasCompactification f.left := HasCompactification.of_over f
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by
    simpa only [Over.w f] using (inferInstance : LocallyOfFiniteType X.hom)
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have : IsSeparated (f.left ≫ Y.hom) := by
    simpa only [Over.w f] using (inferInstance : IsSeparated X.hom)
  have : IsSeparated f.left := IsSeparated.of_comp f.left Y.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have : QuasiCompact f.left := quasiCompact_of_compactSpace f.left
  let c := ProEtale.CondensedRing.compactificationOverField f
  let e := Etale.rightDerivedLowerShriekIso A c
  constructor
  · intro K hK
    exact (Etale.DerivedCategory.boundedConstructible _ Y.left).prop_of_iso
      (e.app K).symm
      (Etale.boundedConstructible_rightDerivedLowerShriek A f.left X.hom Y.hom
        (Over.w f) K hK)
  · intro K hK hKt
    have hshriek := Etale.constructibleFiniteTor_rightDerivedLowerShriek A Y.hom
      f.left ⟨hK, hKt⟩
    have hpush := Etale.constructibleFiniteTor_rightDerivedLowerStar A X.hom Y.hom
      f.left (Over.w f) ⟨hK, hKt⟩
    exact ⟨(DerivedCategory.finiteTorAmplitude _).prop_of_iso
      (e.app K).symm hshriek.2, hpush.2⟩

/-- The numerical direct-image row, with precisely its finite-field-closure qualification.
Source: latest blueprint, Rf_* row (blueprint: sk-rem-sf-typing).

Proof: apply the Noetherian coefficient direct-image Tor theorem with the invertible
annihilator ell^r and d = dim X, taking zero for an empty X. All inputs are bounded
constructible. The ordinary finite comparison identifies direct images on both sites and
preserves and reflects Tor intervals, giving the identical pro-etale bound. -/
theorem finiteDirectImageTorTyping
    (D : WeilConjectures.FiniteFieldDatum.{u}) (ek : k ≃+* D.k)
    (a b : ℤ) (hab : a ≤ b) :
    (∀ K : EtaleD(X.left), EtaleBC(X.left) K → EtaleTor(X.left) a b K →
      EtaleBC(Y.left) ((Etale.lowerStar (ModuleCat.{u + 1} A) f.left).rightDerivedFunctor.obj K) ∧
      EtaleTor(Y.left) a (b + 2 * dim₀(X.left))
        ((Etale.lowerStar (ModuleCat.{u + 1} A) f.left).rightDerivedFunctor.obj K)) ∧
    (∀ K : ProEtaleD(X.left), ProEtaleBC(X.left) K → ProEtaleTor(X.left) a b K →
      ProEtaleBC(Y.left)
        ((ProEtale.lowerStar (ModuleCat.{u + 1} A) f.left).rightDerivedFunctor.obj K) ∧
      ProEtaleTor(Y.left) a (b + 2 * dim₀(X.left))
        ((ProEtale.lowerStar (ModuleCat.{u + 1} A) f.left).rightDerivedFunctor.obj K)) := by
  obtain ⟨r, hr, hkill⟩ := hA
  have hellk : (ell : k) ≠ 0 := fun h ↦
    (Fact.out : ringChar k ≠ ell)
      (CharP.ringChar_of_prime_eq_zero (Fact.out : ell.Prime) h)
  have hkill' : ((ell ^ r : ℕ) : A) = 0 := by
    simpa only [Nat.cast_pow] using hkill
  have hN : ((ell ^ r : ℕ) : k) ≠ 0 := by
    simpa only [Nat.cast_pow] using pow_ne_zero r hellk
  letI : NeZero (ell ^ r) := ⟨pow_ne_zero r (Fact.out : ell.Prime).ne_zero⟩
  letI : HasInvertibleExponent A (Spec (.of k)) := by
    refine ⟨ell ^ r, pow_pos (Fact.out : ell.Prime).pos r, hkill', ?_⟩
    simpa only [map_natCast] using hN.isUnit.map (Scheme.ΓSpecIso (.of k)).inv.hom
  letI : HasInvertibleExponent A Y.left := .of_hom Y.hom
  have : LocallyOfFiniteType (f.left ≫ Y.hom) := by
    simpa only [Over.w f] using (inferInstance : LocallyOfFiniteType X.hom)
  have : LocallyOfFiniteType f.left := locallyOfFiniteType_of_comp f.left Y.hom
  have : IsSeparated (f.left ≫ Y.hom) := by
    simpa only [Over.w f] using (inferInstance : IsSeparated X.hom)
  have : IsSeparated f.left := IsSeparated.of_comp f.left Y.hom
  have : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  have : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  have : QuasiCompact f.left := quasiCompact_of_compactSpace f.left
  obtain ⟨n, hn⟩ := exists_topologicalKrullDim_le X.hom
  have hdim : topologicalKrullDim X.left ≤ (dim₀(X.left) : WithBot ℕ∞) := by
    generalize topologicalKrullDim X.left = t at *
    induction t using WithBot.recBotCoe with
    | bot => exact bot_le
    | coe t =>
      induction t using ENat.recTopCoe with
      | top => exact False.elim ((ENat.natCast_ne_top n)
          (top_le_iff.mp (WithBot.coe_le_coe.mp hn)))
      | coe t => simp
  constructor
  · intro K hK hKt
    refine ⟨Etale.boundedConstructible_rightDerivedLowerStar_of_finite A X.hom Y.hom
      f.left (Over.w f) hK, ?_⟩
    exact Etale.torAmplitudeIn_rightDerivedLowerStar_of_isNoetherianRing A X.hom Y.hom
      f.left (Over.w f) dim₀(X.left) hdim a b (ell ^ r)
      (Etale.nsmul_id_eq_zero_of_natCast_eq_zero hkill' K)
      (by
        simpa only [map_natCast] using hN.isUnit.map
          (Y.hom.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)) hK hKt
  · intro K hK hKt
    exact ProEtale.boundedConstructible_and_torAmplitudeIn_rightDerivedLowerStar A
      (ell ^ r) hN (ProEtale.nsmul_id_eq_zero (ell ^ r) hkill') Y.hom f.left
      dim₀(X.left) hdim a b hK hKt

/-- The exceptional row on both finite sites, with smooth, closed-immersion and the
specified finite-chart maximum bounds. The nonnegative target dimension is zero for
empty Y, and Finset.sup is zero for an empty chart family.
Source: latest blueprint, exceptional row (blueprint: sk-rem-sf-typing).

Proof: at finite coefficients the ordinary etale compact-support right adjoint exists.
The finite condensed comparison identifies its restriction with the Brown adjoint, including
units and counits, without an ambient pro-etale adjunction. Smooth tensor duality is exact
pullback tensored with a locally free rank-one twist shifted by [2d], giving both smooth
intervals. On a chart U closed in A^r_V, apply finiteRingAffineExceptionalWindow with
 e = dim Y, using dimension monotonicity for V. The open exceptional comparison identifies
the chart output with restriction of the global one. Enlarge to the maximum r and detect
outside-degree vanishing on the open cover, also after tensoring with every degree-zero
module; glue constructibility. A closed immersion has r = 0 on affine target charts,
giving the target-dimension bound. Finite origin and Tor comparison transfer every bound
to the transported pro-etale functor. Empty-source categories are zero, so empty chart
families are included. -/
theorem finiteExceptionalTyping (a b : ℤ) (hab : a ≤ b) :
    letI : HasCompactification f.left := HasCompactification.of_over f
    let G := Etale.rightDerivedUpperShriek A f.left
    let Gp := ProEtale.rightDerivedUpperShriek A f.left
    (∀ d : ℕ, SmoothOfRelativeDimension d f.left →
      etaleWindow A X.left Y.left G a b (a - 2 * d) (b - 2 * d) ∧
      proetaleWindow A X.left Y.left Gp a b (a - 2 * d) (b - 2 * d)) ∧
    (IsClosedImmersion f.left → ∀ d : ℕ,
      topologicalKrullDim Y.left ≤ (d : WithBot ℕ∞) →
      etaleWindow A X.left Y.left G a b a (b + 2 * d + 1) ∧
      proetaleWindow A X.left Y.left Gp a b a (b + 2 * d + 1)) ∧
    (∀ (m : ℕ) (U : Fin m → X.left.affineOpens)
      (V : Fin m → Y.left.affineOpens) (n : Fin m → ℕ)
      (c : ∀ i, ((U i : X.left.Opens) : Scheme.{u}) ⟶
        AffineSpace (ULift.{u} (Fin (n i))) ((V i : Y.left.Opens) : Scheme.{u})),
      (∀ x : X.left, ∃ i, x ∈ (U i : X.left.Opens)) →
      (∀ i, IsClosedImmersion (c i)) →
      (∀ i, c i ≫ (AffineSpace.over (ULift.{u} (Fin (n i)))
          ((V i : Y.left.Opens) : Scheme.{u})).hom ≫ (V i : Y.left.Opens).ι =
        (U i : X.left.Opens).ι ≫ f.left) →
      let D : ℕ := Finset.univ.sup n
      etaleWindow A X.left Y.left G a b (a - 2 * D) (b + 2 * dim₀(Y.left) + 1) ∧
      proetaleWindow A X.left Y.left Gp a b
        (a - 2 * D) (b + 2 * dim₀(Y.left) + 1)) := by
  classical
  have _ := hk
  have _ := hab
  let : HasInvertibleExponent A (Spec (.of k)) :=
    finiteCoefficientExponent ell k (Fact.out : ringChar k ≠ ell) A hA
  let : HasInvertibleExponent A Y.left := .of_hom Y.hom
  let : HasCompactification f.left := HasCompactification.of_over f
  let : QuasiSeparatedSpace Y.left := quasiSeparatedSpace_of_quasiSeparated Y.hom
  let : CompactSpace X.left := QuasiCompact.compactSpace_of_compactSpace X.hom
  let : CompactSpace Y.left := QuasiCompact.compactSpace_of_compactSpace Y.hom
  let : QuasiCompact f.left := quasiCompact_of_compactSpace f.left
  let : IsNoetherian Y.left := { __ := LocallyOfFiniteType.isLocallyNoetherian Y.hom }
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    let := hd
    obtain ⟨hc, ht⟩ := Etale.smooth_preservationClauses A f.left d
    have h : etaleWindow A X.left Y.left (Etale.rightDerivedUpperShriek A f.left)
        a b (a - 2 * d) (b - 2 * d) :=
      ⟨fun K hK hKab ↦ hc a b K ⟨hK, hKab⟩, fun K hK hKt ↦ ht a b K hK hKt⟩
    exact ⟨h, proetaleExceptionalWindow A f.left a b _ _ h⟩
  · intro hf d hd
    let := hf
    let W : Y.left.Opens :=
      ⟨(Set.range f.left.base)ᶜ, f.left.isClosedEmbedding.isClosed_range.isOpen_compl⟩
    have hW : Set.range f.left.base = (Set.range W.ι.base)ᶜ := by
      rw [Scheme.Opens.range_ι]
      exact (compl_compl _).symm
    obtain ⟨_, hc, ht⟩ :=
      Etale.isLeftAdjoint_and_constructibleIn_and_torAmplitudeIn_of_isClosedImmersion
        Y.hom d hd f.left W.ι hW A
    have h : etaleWindow A X.left Y.left (Etale.rightDerivedUpperShriek A f.left)
        a b a (b + 2 * d + 1) := by
      constructor
      · intro K hK hKab
        have hC := hc a b K ⟨hK, hKab⟩
        exact ⟨hC.1, by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hC.2⟩
      · intro K hK hKt
        simpa only [Nat.cast_mul, Nat.cast_ofNat] using ht a b K hK hKt
    exact ⟨h, proetaleExceptionalWindow A f.left a b _ _ h⟩
  · intro m U V n c hU hc he
    let := hc
    obtain ⟨hcoh, htor⟩ :=
      Etale.preservationClauses_of_charts_of_topologicalKrullDim_le A Y.hom f.left
        _ (finiteDimensionBound Y.hom) U hU V n c he (Finset.univ.sup n)
        (fun i ↦ Finset.le_sup (Finset.mem_univ i))
    have h : etaleWindow A X.left Y.left (Etale.rightDerivedUpperShriek A f.left)
        a b (a - 2 * Finset.univ.sup n) (b + 2 * dim₀(Y.left) + 1) :=
      ⟨fun K hK hKab ↦ hcoh a b K ⟨hK, hKab⟩,
        fun K hK hKt ↦ htor a b K hK hKt⟩
    exact ⟨h, proetaleExceptionalWindow A f.left a b _ _ h⟩
end Finite

/-- The sharper pro-etale Hom window uses perfectness on that very coefficient site.
Source: latest blueprint, internal-Hom row, site-perfect first input
(blueprint: sk-rem-sf-typing).

Proof: site-perfect duality identifies RHom(K,L) with the coefficient dual of K
 tensored with L. A bounded local complex of finite projectives has dual Tor interval
[-b,-a]. Tensoring the dual with L adds intervals to [c-b,d-a]. This computation is
local on the pro-etale cover and tests every degree-zero module, so it supplies the
stated interval without imposing an etale-perfect hypothesis on the first input.
Finite constructible origin identifies these objects with pulled-back finite pairs. -/
theorem finiteProetalePerfectHomTyping
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (A : Type u) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, 1 ≤ r ∧ (ell : A) ^ r = 0)
    (Y : Over (Spec (.of k)))
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    (K L : DerivedCategory (CategoryTheory.Mod
      (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
      (ProEtale.condensedRingObj (ProEtale.cartesianFinitePointRing A) Y.left)))
    (a b c d : ℤ) (hab : a ≤ b) (hcd : c ≤ d)
    (hK : ProEtale.constantModelBoundedConstructible
      (ProEtale.cartesianFinitePointRing A) Y.left K)
    (hL : ProEtale.constantModelBoundedConstructible
      (ProEtale.cartesianFinitePointRing A) Y.left L)
    (hperfect : ProEtale.CondensedRing.IsPerfectOnCoefficientSite
      (ProEtale.cartesianFinitePointRing A) Y.left K)
    (hKt : DerivedCategory.torAmplitudeIn _ a b K)
    (hLt : DerivedCategory.torAmplitudeIn _ c d L) :
    DerivedCategory.torAmplitudeIn _ (c - b) (d - a)
      (((ProEtale.CondensedRing.derivedHom
        (ProEtale.cartesianFinitePointRing A) Y.left).obj (op K)).obj L) := by
  classical
  have _ := hA
  let C := CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
    (ProEtale.condensedRingObj (ProEtale.cartesianFinitePointRing A) Y.left)
  letI : BraidedCategory (DerivedCategory C) :=
    (DerivedCategory.nonempty_braidedCategory C).some
  obtain ⟨_, ep, _⟩ := ProEtale.CondensedRing.native_sitePerfect_dual
    (ProEtale.cartesianFinitePointRing A) Y.left K hperfect
  letI := ep
  letI : ExactPairing K ((ihom K).obj (𝟙_ _)) :=
    BraidedCategory.exactPairing_swap _ _
  haveI := MonoidalClosed.isIso_ihomUnitTensorToIhom ((ihom K).obj (𝟙_ _)) K L
  have hdual : DerivedCategory.torAmplitudeIn C (-b) (-a) ((ihom K).obj (𝟙_ _)) :=
    DerivedCategory.torAmplitudeIn_of_exactPairing hKt
  have htensor := DerivedCategory.torAmplitudeIn_tensor hdual hLt
  have hhom := (DerivedCategory.torAmplitudeIn C (-b + c) (-a + d)).prop_of_iso
    (asIso (MonoidalClosed.ihomUnitTensorToIhom K L)) htensor
  simpa only [ProEtale.CondensedRing.derivedHom, MonoidalClosed.internalHom,
    sub_eq_add_neg, add_comm] using hhom

/-- Finite-coefficient direct-image constructibility requires no separatedness of f.
Source: latest blueprint, Rf_* row (blueprint: sk-rem-sf-typing).

Proof: use finite-type direct-image finiteness on etale. A finite-type target is
Noetherian and quasi-compact, and the map is quasi-compact. That finiteness clause does
not assume separatedness. The invertible ell-power annihilator gives torsion coefficients.
-/
theorem finiteDirectImageConstructibleTyping
    (ell : ℕ) [Fact ell.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ell)]
    (hk : Finite k ∨ IsAlgClosed k)
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (hA : ∃ r : ℕ, 1 ≤ r ∧ (ell : A) ^ r = 0)
    {X Y : Scheme.{u}} (aX : X ⟶ Spec (.of k)) (aY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType aX] [QuasiCompact aX]
    [LocallyOfFiniteType aY] [QuasiCompact aY]
    (f : X ⟶ Y) (hf : f ≫ aY = aX) [LocallyOfFiniteType f] [QuasiCompact f] :
    ∀ K : Etale.DerivedCategoryModule A X,
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) X K →
      Etale.DerivedCategory.boundedConstructible (ModuleCat.{u + 1} A) Y
        ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj K) := by
  obtain ⟨r, hr, hkill⟩ := hA
  have hellk : (ell : k) ≠ 0 := fun h ↦
    (Fact.out : ringChar k ≠ ell)
      (CharP.ringChar_of_prime_eq_zero (Fact.out : ell.Prime) h)
  letI : HasInvertibleExponent A (Spec (.of k)) := by
    refine ⟨ell ^ r, pow_pos (Fact.out : ell.Prime).pos r, ?_, ?_⟩
    · simpa only [Nat.cast_pow] using hkill
    · have hu : IsUnit ((ell ^ r : ℕ) : k) := by
        simpa only [Nat.cast_pow] using hellk.isUnit.pow r
      simpa only [map_natCast] using hu.map (Scheme.ΓSpecIso (.of k)).inv.hom
  letI : HasInvertibleExponent A X := .of_hom aX
  intro K hK
  exact Etale.boundedConstructible_rightDerivedLowerStar_of_hasInvertibleExponent
    A f aX aY hf K hK

end AlgebraicGeometry.SixOperationsTyping
