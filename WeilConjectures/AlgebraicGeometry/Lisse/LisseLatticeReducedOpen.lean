/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Continuous.ContinuousConstructibleModule
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.LatticePullbackProof.ContinuousCoefficientPullbackIsoSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.EtaleStratifiedFinite
import WeilConjectures.Topology.StratificationDense
import WeilConjectures.AlgebraicGeometry.ContinuousFiniteEtaleLatticeDescent
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.NumberTheory.Padics.ProperSpace
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionLocalModel
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.ContinuousLatticeIntersectionSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionRationalModel
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionSplitModel
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionSplitData
import WeilConjectures.AlgebraicGeometry.FiniteEtaleLocallyFreeModels
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.CategoryTheory.ModuleObjects.Free
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit
import WeilConjectures.AlgebraicGeometry.SplitProEtaleModuleProductMap
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.ProfinitePointPullback
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.Site.SiteInverseImageTensor
import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import WeilConjectures.CategoryTheory.Monoidal.Conjugate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.CategoryTheory.Sites.MonObj
import WeilConjectures.AlgebraicGeometry.SplitProEtaleAbelianProductMap
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
import WeilConjectures.Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.NumberTheory.Padics.FiniteCoefficientFields
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Algebra.Field.ULift
import Mathlib.CategoryTheory.Sites.EpiMono
import WeilConjectures.ConstructibleSheaf.Refinement
import WeilConjectures.AlgebraicGeometry.CondensedFieldLfpLocalTriviality
import WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.Topology.NoetherianSpace
import WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.Topology.Category.Profinite.AsLimit
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Mathlib.Topology.Connected.TotallyDisconnected
import WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationCorank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationMatrix
import Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.AlgebraicGeometry.CondensedFieldPresentationEvaluation
import Mathlib.Algebra.Category.ModuleCat.Basic
import WeilConjectures.AlgebraicGeometry.CondensedFieldRegularModuleScalars
import WeilConjectures.AlgebraicGeometry.CondensedFieldEvaluationFunctors
import WeilConjectures.AlgebraicGeometry.GeometricFieldProEtaleEvaluation
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.AlgebraicGeometry.GeometricFieldProfiniteDenseSubsite
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import WeilConjectures.CategoryTheory.DenseSubsiteModuleRestriction
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Ab
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.AlgebraicGeometry.CondensedFieldGeometricRegularCoefficient
import WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Mathlib.Data.Matrix.Basic
import WeilConjectures.AlgebraicGeometry.IntegralRegularCoefficientPullback
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Kernels
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.CondensedFieldRankDescent
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import WeilConjectures.AlgebraicGeometry.ContinuousFieldCokernelLocalFree
import WeilConjectures.AlgebraicGeometry.ContinuousFieldPresentationNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm
import WeilConjectures.AlgebraicGeometry.ContinuousFieldMatrixElimination
import Mathlib.Logic.Equiv.Set
import Mathlib.Data.Fintype.Basic
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Analysis.Normed.Field.Lemmas
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.Rank
import WeilConjectures.Mathlib.LinearAlgebra.Matrix.SchurComplement
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpLocalTriviality
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpMatrixRefinement
import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionPresentations
import Mathlib.LinearAlgebra.Matrix.ToLin
import WeilConjectures.AlgebraicGeometry.CondensedQbarFunctionCoefficients
import WeilConjectures.AlgebraicGeometry.CondensedQbarCoefficientConstruction
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
import WeilConjectures.CategoryTheory.Monoidal.Mod.EvaluationPairing
import WeilConjectures.AlgebraicGeometry.CondensedQbarScalarPullback
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldFiberExtension
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldEvaluationLinearity
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldCoefficientSquare
import WeilConjectures.AlgebraicGeometry.CondensedQbarFieldPointCoefficientValue
import WeilConjectures.AlgebraicGeometry.CondensedCoefficientPointUnitPasting
import WeilConjectures.AlgebraicGeometry.CondensedQbarLfpCoverComposition
import WeilConjectures.AlgebraicGeometry.RegularExtensionComparison
import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralUnderivedPushComparison
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralModuleTelescope
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralLocalizationSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralRegularTelescope
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationLegs
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralDenominators
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientTelescope
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralScalarExact
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSequentialHom
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleSheafHom
import WeilConjectures.CategoryTheory.HomColimitExtension
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.CategoryTheory.Filtered.Basic
import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.CategoryTheory.Triangulated.Yoneda
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
import Mathlib.CategoryTheory.Category.ULift
import WeilConjectures.CategoryTheory.HomColimitTruncation
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedPiece
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedOneStep
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.CondensedConstructibleGenericLfp
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import WeilConjectures.ConstructibleSheaf.OpenClosed
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpImmersionTransport
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleLfpClosedReflection
import WeilConjectures.AlgebraicGeometry.ProEtaleSurjectiveClosedCoverRefinement
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProEtale.AffineClosedSiteFunctorProperties
import WeilConjectures.AlgebraicGeometry.ProEtaleAbelianClosedSupport
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAbelianClosedCounit
import WeilConjectures.Mathlib.AlgebraicGeometry.Cover.QuasiCompact
import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
import WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedLocalPresentation
import WeilConjectures.AlgebraicGeometry.CondensedSurjectiveClosedEquivalence
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusHomology
import WeilConjectures.Algebra.Homology.FunctorialBoundedInjectiveResolution
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Data.Int.Interval
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexRows
import WeilConjectures.CategoryTheory.DoubleComplexBoundedBelowTotal
import Mathlib.Algebra.Homology.TotalComplex
import Mathlib.CategoryTheory.Abelian.Basic
import WeilConjectures.Algebra.Homology.FunctorialObjectResolution
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryAdjunctionShift
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.WeaklyEtale
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.EffectiveEpi.Comp
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.GradedObject.Bifunctor
import Mathlib.CategoryTheory.GradedObject.Monoidal
import Mathlib.CategoryTheory.GradedObject.Trifunctor
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.Filtered
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.CategoryTheory.Limits.Shapes.Multiequalizer
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Monoidal.Action.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.CommMon_
import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
import Mathlib.CategoryTheory.Monoidal.Mon
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.CategoryTheory.MorphismProperty.OverAdjunction
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.CategoryTheory.Sites.Coherent.Basic
import Mathlib.CategoryTheory.Sites.Coherent.Comparison
import Mathlib.CategoryTheory.Sites.ConcreteSheafification
import Mathlib.CategoryTheory.Sites.Grothendieck
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import Mathlib.Geometry.RingedSpace.PresheafedSpace
import Mathlib.Geometry.RingedSpace.SheafedSpace
import Mathlib.Topology.Category.CompHausLike.Basic
import Mathlib.Topology.Category.CompHausLike.Limits
import Mathlib.Topology.Category.Profinite.Basic
import Mathlib.Topology.Category.Profinite.Limits
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.ContinuousMap.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormula
import WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Mathlib.CategoryTheory.Sites.Sheaf
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Monoidal
import WeilConjectures.AlgebraicGeometry.CondensedLocalPieceHomContinuity
import WeilConjectures.AlgebraicGeometry.CondensedConstructiblePiece
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.AlgebraicGeometry.CondensedLfpHomContinuity
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeDerivedHom
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedQcqsPushforwardContinuitySupplement
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeInternalHomColimits
import WeilConjectures.CategoryTheory.Monoidal.Mod.Tensor
import WeilConjectures.CategoryTheory.Monoidal.Mod.TensorRegular
import WeilConjectures.CategoryTheory.Monoidal.Mod.InternalHom
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Basic
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomEvaluation
import WeilConjectures.CategoryTheory.DerivedCoyonedaEvaluation
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.CategoryTheory.ProperBaseChange.LocallyFreeDerivedHomSupplement
import WeilConjectures.AlgebraicGeometry.CondensedInternalHomSections
import WeilConjectures.CategoryTheory.ModuleObjects.ProperBaseChange.GrothendieckAbelian
import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluation
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeTensorExact
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.AlgebraicGeometry.CondensedFiniteFreeHomContinuity
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import WeilConjectures.AlgebraicGeometry.CondensedLocalPieceCostalkModel
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
import WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkDerivedContinuity
import WeilConjectures.AlgebraicGeometry.CondensedClosedCostalkInjectiveContinuity
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.AlgebraicGeometry.IntegralLfpHomContinuity
import WeilConjectures.AlgebraicGeometry.IntegralLfpLocallyFreeResolution
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.IntegralConstructibleKernels
import Mathlib.CategoryTheory.ObjectProperty.Kernels
import WeilConjectures.AlgebraicGeometry.IntegralMatrixPivotCover
import WeilConjectures.AlgebraicGeometry.IntegralMatrixEntryProperties
import WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticCover
import WeilConjectures.AlgebraicGeometry.FiniteContinuousUltrametricPivot
import Mathlib.Topology.MetricSpace.Ultra.Basic
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Finset.Max
import WeilConjectures.AlgebraicGeometry.IntegralMatrixZeroNeighborhood
import WeilConjectures.AlgebraicGeometry.IntegralMatrixFunctionsPullback
import WeilConjectures.AlgebraicGeometry.ContinuousRegularFunctions
import WeilConjectures.AlgebraicGeometry.IntegralMatrixPointwiseRank
import WeilConjectures.AlgebraicGeometry.IntegralMatrixCoefficientTransport
import WeilConjectures.AlgebraicGeometry.IntegralRegularRationalUnit
import WeilConjectures.AlgebraicGeometry.FiniteBiproductPivot
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.Fin.Tuple.Basic
import WeilConjectures.AlgebraicGeometry.ConstructibleCokernelsExtensions
import Mathlib.CategoryTheory.ObjectProperty.Extensions
import WeilConjectures.AlgebraicGeometry.PullbackExtendScalarsComparison
import WeilConjectures.AlgebraicGeometry.LocallyFinitelyPresentedExtendScalars
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
import WeilConjectures.AlgebraicGeometry.IntegralLfpEventualFreeImage
import WeilConjectures.AlgebraicGeometry.ModuleObjectFreeGenerators
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Algebra.Category.Grp.Adjunctions
import WeilConjectures.AlgebraicGeometry.IntegralLfpFiniteQuotientCharts
import WeilConjectures.AlgebraicGeometry.IntegralLfpLocalTorsionCharts
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Images
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.CategoryTheory.DerivedCategory.Constructible
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
import WeilConjectures.CategoryTheory.ProperBaseChange.CondensedUnderivedPushforwardContinuitySupplement
import WeilConjectures.AlgebraicGeometry.ContinuousFiniteFreeKernelModel
import WeilConjectures.AlgebraicGeometry.ContinuousFiniteFreeDenominators
import WeilConjectures.AlgebraicGeometry.ContinuousLatticeIntersectionRationalization
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralLocalizationCounit
import WeilConjectures.AlgebraicGeometry.IntegralMatrixKernelLocallyFree
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.Algebra.Homology.Site.SiteModuleSheafGluing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingLocalFreeness
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
import WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficientNormalization
import WeilConjectures.AlgebraicGeometry.Lisse.LisseLatticeCoefficientsSupplement
import WeilConjectures.AlgebraicGeometry.LatticeSheafLocallyConstant
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.LatticeSheafBasicSupplement
import WeilConjectures.AlgebraicGeometry.LatticeClassDescent
import WeilConjectures.AlgebraicGeometry.LatticePairEffectiveDescent
import WeilConjectures.AlgebraicGeometry.LatticeClassPresheaf
import WeilConjectures.AlgebraicGeometry.LatticePairRestriction
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import WeilConjectures.AlgebraicGeometry.LatticeGluedRationalizationIso
import WeilConjectures.AlgebraicGeometry.LatticeGluedRationalization
import WeilConjectures.AlgebraicGeometry.LatticePairDescentData
import WeilConjectures.CategoryTheory.SiteModuleCompatibleTuples
import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.CoversTop.Over
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.LocalProperties
import WeilConjectures.AlgebraicGeometry.LatticeCosetLocalSurjectivity
import WeilConjectures.AlgebraicGeometry.LatticeCosetMap
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.LargeSetSheafification
import WeilConjectures.AlgebraicGeometry.LatticePairLocalMatrix
import WeilConjectures.AlgebraicGeometry.LatticeSectionMatrix
import WeilConjectures.AlgebraicGeometry.LatticePairMatrixAtBasis
import WeilConjectures.AlgebraicGeometry.LocalFreeTensorUnit
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.TensorProduct.Basis
import WeilConjectures.AlgebraicGeometry.LatticeMatrixNeighborhoods
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.GroupTheory.Coset.Defs
import WeilConjectures.NumberTheory.Padics.LatticeStabilizerOpen
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.RingTheory.Flat.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.CategoryTheory.Sites.Over
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingSliceFreeness
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingRestriction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.InternalHom
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
import Mathlib.CategoryTheory.Sites.CoverLifting
import Mathlib.CategoryTheory.Sites.CoversTop.Basic
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingScalarExtension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import Mathlib.Algebra.Field.Shrink
import Mathlib.Algebra.Algebra.TransferInstance
import all WeilConjectures.AlgebraicGeometry.IntegralLatticeCoefficientTransport
import all Mathlib.LinearAlgebra.TensorProduct.Map
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLocallyFreePullbackSupplement
import WeilConjectures.AlgebraicGeometry.ContinuousEtaleLocalLattices
import WeilConjectures.AlgebraicGeometry.ContinuousAffineEtaleLattice
import WeilConjectures.AlgebraicGeometry.LisseLatticeEtaleLocal
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalEtaleCover
import WeilConjectures.AlgebraicGeometry.ProEtaleLocallyClassicalContinuity
import WeilConjectures.AlgebraicGeometry.ProEtaleComparisonSections
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types
import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
import WeilConjectures.CategoryTheory.LanContinuityFromRepresentables
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.ProEtaleSiteComparison
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Sites.Precoverage.Generates
import Mathlib.CategoryTheory.Sites.Finite
import Mathlib.CategoryTheory.Limits.Connected
import Mathlib.CategoryTheory.Filtered.Connected
import Mathlib.CategoryTheory.Filtered.Final
import Mathlib.Data.Finite.Prod
import WeilConjectures.Mathlib.CategoryTheory.Sites.LocallySurjective
import WeilConjectures.AlgebraicGeometry.LisseLatticeClassSheaf
import WeilConjectures.AlgebraicGeometry.LisseLatticePresentationTransport
import Mathlib.CategoryTheory.ShrinkYoneda
import Mathlib.CategoryTheory.Limits.Preserves.Ulift
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import WeilConjectures.AlgebraicGeometry.LisseLatticeSliceTransport
import WeilConjectures.AlgebraicGeometry.ContinuousModuleEncodingLattices
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousLatticeFiniteCoproductSupplement
import Mathlib.RingTheory.Finiteness.Small

/-!
# An integral lattice on a nonempty reduced open

Source: Bhatt--Scholze, The pro-etale topology for schemes, Lemma 6.8.13,
first paragraph, and Stacks Tag 03S0.
(blueprint: lem-weil-pbc-lisse-lattice-reduced-open)
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Scheme.proEtaleRingModuleAdjunction
  CondensedRing.pullIso CondensedRing.upperStarComp
  CondensedRing.integralScalarMap

private theorem baseChange_cont {X Y : Scheme.{u}} (f : Y ⟶ X) :
    (Scheme.proEtaleBaseChange f).IsContinuous (Scheme.ProEt.topology X)
      (Scheme.ProEt.topology Y) := AlgebraicGeometry.Scheme.ProEt.isContinuous_overPullback f

attribute [local instance] baseChange_cont

set_option backward.isDefEq.respectTransparency false in
private def continuous_restriction_adjunction {X Y : Scheme.{u}}
    (f : Y ⟶ X) [WeaklyEtale f] (T : Type u)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T] :
    let F := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)
    let : F.IsContinuous (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
      Scheme.ProEt.isContinuous_overMap (inferInstance : WeaklyEtale f)
    letI : (Scheme.proEtaleBaseChange f).IsContinuous
        (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y) := baseChange_cont f
    let R := latticeModuleRing X T
    let S := latticeModuleRing Y T
    let a : S ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj R :=
      ⟨{ app := fun _ ↦ 𝟙 _
         naturality := fun _ _ _ ↦ rfl }⟩
    let b : R ⟶ ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuous
        RingCat.{u + 1} (Scheme.ProEt.topology X) (Scheme.ProEt.topology Y)).obj S :=
      ⟨Functor.whiskerRight (continuousCoefficientDirectImageMap f T).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
    SheafOfModules.pushforward a ⊣ SheafOfModules.pushforward b := by
  dsimp only
  let adj := MorphismProperty.Over.mapPullbackAdj @WeaklyEtale ⊤ f
    (inferInstance : WeaklyEtale f) trivial
  apply SheafOfModules.pushforwardPushforwardAdj.{u + 1} adj
  · apply NatTrans.ext
    funext V
    apply RingCat.hom_ext
    ext s : 1
    apply ULift.ext
    ext x
    rfl
  · apply NatTrans.ext
    funext V
    apply RingCat.hom_ext
    ext s : 1
    apply ULift.ext
    ext x
    change s.down _ = s.down x
    congr 1
    change ((pullback.fst (V.unop.hom ≫ f) f).base
      ((pullback.lift (𝟙 V.unop.left) V.unop.hom (by simp)).base x)) = x
    simp only [← Scheme.Hom.comp_apply, pullback.lift_fst]
    rfl

set_option backward.isDefEq.respectTransparency false in
private theorem continuous_restriction_iso {X Y : Scheme.{u}}
    (f : Y ⟶ X) [WeaklyEtale f] (T : Type u)
    [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TotallyDisconnectedSpace T]
    (M : SheafOfModules.{u + 1} (latticeModuleRing X T)) :
    let F := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale f)
    let : F.IsContinuous (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
      Scheme.ProEt.isContinuous_overMap (inferInstance : WeaklyEtale f)
    let a : latticeModuleRing Y T ⟶ (F.sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj (latticeModuleRing X T) :=
      ⟨{ app := fun _ ↦ 𝟙 _
         naturality := fun _ _ _ ↦ rfl }⟩
    Nonempty (continuousModulePullback f T M ≅ (SheafOfModules.pushforward a).obj M) := by
  let := LatticePullbackProof.continuousCoefficientInverseImageMap_isIso f T
  let c := asIso (continuousCoefficientInverseImageMap f T)
  let a := continuous_restriction_adjunction f T
  let b := Scheme.proEtaleRingModuleAdjunction f
    (latticeCoefficientSheaf X T) (latticeCoefficientSheaf Y T) c
  have hd : Scheme.proEtaleRingDirectImageMap f
      (latticeCoefficientSheaf X T) (latticeCoefficientSheaf Y T) c =
      continuousCoefficientDirectImageMap f T := by
    exact ((Scheme.proEtaleSheafAdjunction f CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply
      (continuousCoefficientDirectImageMap f T)
  unfold Scheme.proEtaleRingModuleDirectImage at b
  rw [hd] at b
  exact ⟨(b.leftAdjointUniq a).app M⟩

attribute [local irreducible] continuous_restriction_adjunction

private theorem exists_small_coefficient (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] :
    ∃ (K : Type) (_ : Field K) (_ : Algebra ℚ_[l] K)
      (_ : FiniteDimensional ℚ_[l] K), Nonempty (E ≃ₐ[ℚ_[l]] K) := by
  have : Small.{0} E := Module.Finite.small ℚ_[l] E
  let K := Shrink.{0} E
  let : Algebra ℚ_[l] K := (equivShrink E).symm.algebra ℚ_[l]
  let e : K ≃ₐ[ℚ_[l]] E := (equivShrink E).symm.algEquiv ℚ_[l]
  let : FiniteDimensional ℚ_[l] K := e.symm.toLinearEquiv.finiteDimensional
  exact ⟨K, inferInstance, inferInstance, inferInstance, ⟨e.symm⟩⟩

private theorem finite_cover_on_open (X : Scheme.{u}) [IsNoetherian X]
    [Nonempty X] [IsReduced X] {Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] (p : Y ⟶ X) [Etale p] [Surjective p] :
    ∃ U : X.Opens, Nonempty U ∧
      IsFinite (pullback.snd p U.ι) := by
  classical
  obtain ⟨S, _, hS⟩ := Scheme.exists_etale_stratified_finite p
  obtain ⟨x, hx⟩ := S.toStratification.dense_iUnion_interior_stratum.nonempty
  obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
  let U : X.Opens := ⟨interior (S.stratum a), isOpen_interior⟩
  let i := S.immersion a
  let q := pullback.snd i U.ι
  have hq : Surjective q := by
    constructor
    intro u
    have hu : U.ι u ∈ Set.range i := by
      rw [S.range_immersion]
      exact interior_subset u.property
    obtain ⟨z, hz⟩ := hu
    obtain ⟨v, _, hv⟩ := Scheme.Pullback.exists_preimage_pullback z u hz
    exact ⟨v, hv⟩
  have : IsClosedImmersion q := IsClosedImmersion.of_isPreimmersion q (by
    rw [Set.range_eq_univ.mpr q.surjective]
    exact isClosed_univ)
  have : IsIso q := isIso_of_isClosedImmersion_of_surjective q
  let f : U.toScheme ⟶ S.domain a := inv q ≫ pullback.fst i U.ι
  have hf : f ≫ i = U.ι := by
    dsimp only [f]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    simp [q]
  have := (hS a).1
  have := (hS a).2
  have : IsFinite (pullback.snd (pullback.snd p i) f) := inferInstance
  have : Etale (pullback.snd (pullback.snd p i) f) := inferInstance
  have h := (Scheme.finite_etale_pullback_comp p i f).1
  rw [hf] at h
  exact ⟨U, ⟨⟨x, ha⟩⟩, h⟩

open scoped CategoryTheory.Obj CategoryTheory.Functor
open CondensedRing in
private theorem scalar_square
    (A B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj A] [IsCommMonObj A] [MonObj B] [IsCommMonObj B]
    (φ : A ⟶ B) [IsMonHom φ]
    {X Y V W : Scheme.{u}} (p : Y ⟶ X) (j : W ⟶ X)
    (r : V ⟶ Y) (q : V ⟶ W) (h : r ≫ p = q ≫ j)
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj B X))
    (M : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1}) (condensedRingObj A Y))
    (e : (Mod.extendScalars (coefficientMap φ Y)).obj M ≅
      (CondensedRing.upperStar B p).obj P) :
    Nonempty ((Mod.extendScalars (coefficientMap φ V)).obj
      ((CondensedRing.upperStar A r).obj M) ≅
      (CondensedRing.upperStar B q).obj ((CondensedRing.upperStar B j).obj P)) := by
  exact ⟨(pullIso φ r).app M ≪≫ (CondensedRing.upperStar B r).mapIso e ≪≫
    ((CondensedRing.upperStarComp B r p).app P).symm ≪≫
    eqToIso (congrArg (fun f ↦ (CondensedRing.upperStar B f).obj P) h) ≪≫
    (CondensedRing.upperStarComp B q j).app P⟩

open CondensedRing in
private theorem internal_open_lattice (l : ℕ) [Fact l.Prime] (K : Type)
    [NormedField K] [NormedAlgebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (X : Scheme.{u}) [IsNoetherian X] [Nonempty X] [IsReduced X]
    (P : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj K) X))
    (hP : CondensedRing.LocallyFree _ P) :
    ∃ U : X.Opens, Nonempty U ∧
      ∃ M : Mod (Sheaf (Scheme.ProEt.topology U.toScheme) Ab.{u + 1})
          (condensedRingObj (integralCoeff l K) U.toScheme),
        CondensedRing.LocallyFree _ M ∧
        Nonempty ((Mod.extendScalars
          (coefficientMap (integralScalarMap l K) U.toScheme)).obj M ≅
            (CondensedRing.upperStar (Profinite.continuousMapRingObj K) U.ι).obj P) := by
  classical
  obtain ⟨Y, p, hp, hs, hc, hqs, M, hM, ⟨e⟩⟩ :=
    continuousLisse_etale_lattice l K X P hP
  have : Etale p := hp
  have : Surjective p := hs
  have : CompactSpace Y := hc
  have : QuasiSeparatedSpace Y := hqs
  obtain ⟨U, hU, hf⟩ := finite_cover_on_open X p
  let r := pullback.fst p U.ι
  let q := pullback.snd p U.ι
  have : IsFinite q := hf
  let M' := (CondensedRing.upperStar (integralCoeff l K) r).obj M
  let P' := (CondensedRing.upperStar (Profinite.continuousMapRingObj K) U.ι).obj P
  have hM' : CondensedRing.LocallyFree _ M' := locallyFree_upperStar _ r hM
  have hP' : CondensedRing.LocallyFree _ P' := locallyFree_upperStar _ U.ι hP
  obtain ⟨e'⟩ := scalar_square _ _ (integralScalarMap l K) p U.ι r q
    (pullback.condition (f := p) (g := U.ι)) P M e
  have : TopologicalSpace.NoetherianSpace U.toScheme :=
    U.ι.isOpenEmbedding.isInducing.noetherianSpace
  obtain ⟨N, hN, eN⟩ := continuousLisse_finiteEtale_lattice l K U.toScheme P' hP' q M' hM' ⟨e'⟩
  exact ⟨U, hU, N, hN, eN⟩

open CondensedRing in
private theorem field_inverse_locallyFree (l : ℕ) [Fact l.Prime] (K : Type)
    [NormedField K] [NormedAlgebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (X : Scheme.{u})
    (M : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l K X)))
    [M.IsFiniteLocallyFree] :
    CondensedRing.LocallyFree _ ((continuousFieldModuleEquivalence l K X).inverse.obj M) := by
  let : IsUltrametricDist K := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let : TotallyDisconnectedSpace K := inferInstance
  let F := continuousRingModuleEquivalence X K
  let e := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
      (eqToIso (lisseFieldSheaf_eq l K X))
  let H := ringModuleEquivalenceOfIso X e
  let : (H.inverse.obj M).IsFiniteLocallyFree :=
    finiteLocallyFree_restrict (Scheme.ProEt.topology X) _ _ e.symm M
  let e' : H.inverse.obj M ≅ F.functor.obj (F.inverse.obj (H.inverse.obj M)) :=
    (F.counitIso.app _).symm
  let : (F.functor.obj (F.inverse.obj (H.inverse.obj M))).IsFiniteLocallyFree :=
    SheafOfModules.IsFiniteLocallyFree.of_iso.{u + 1, u, u + 1} e'
  exact (continuousRing_locallyFree_iff X K
    (F.inverse.obj (H.inverse.obj M))).mpr inferInstance

open CondensedRing in
private theorem integer_forward_locallyFree (l : ℕ) [Fact l.Prime] (K : Type)
    [NormedField K] [NormedAlgebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (integralCoeff l K) X))
    (hM : CondensedRing.LocallyFree _ M) :
    ((continuousIntegerModuleEquivalence l K X).functor.obj M).IsFiniteLocallyFree := by
  let : IsUltrametricDist K := IsUltrametricDist.of_normedAlgebra ℚ_[l]
  let : TotallyDisconnectedSpace K := inferInstance
  let : ((continuousRingModuleEquivalence X (continuousIntegers l K)).functor.obj
      M).IsFiniteLocallyFree :=
    (continuousRing_locallyFree_iff X (continuousIntegers l K) M).mp hM
  exact finiteLocallyFree_restrict (Scheme.ProEt.topology X) _ _
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso
        (eqToIso (lisseIntegerSheaf_eq l K X))) _

section CoefficientTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (K : Type) [Field K] [Algebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
  (e : E ≃ₐ[ℚ_[l]] K)

private theorem coefficient_absolute (x : E) :
    Padic.coefficientExtensionAbsoluteValue l E x =
      Padic.coefficientExtensionAbsoluteValue l K (e x) := by
  change spectralNorm ℚ_[l] E x = spectralNorm ℚ_[l] K (e x)
  unfold spectralNorm
  rw [← minpoly.algEquiv_eq e x]

private def nativeFieldRingEquiv :
    WithAbs (Padic.coefficientExtensionAbsoluteValue l E) ≃+* K :=
  (WithAbs.equiv _).trans e.toRingEquiv

private theorem nativeField_isometry :
    letI := spectralNorm.normedField ℚ_[l] K
    Isometry (nativeFieldRingEquiv l E K e) := by
  let := spectralNorm.normedField ℚ_[l] K
  apply AddMonoidHomClass.isometry_of_norm
  intro x
  exact (coefficient_absolute l E K e x.ofAbs).symm

private def nativeIntegerRingEquiv :
    latticeCoefficientIntegers l E ≃+* Padic.coefficientExtensionIntegers l K :=
  (nativeFieldRingEquiv l E K e).restrict _ _ (by
    intro x
    change x.ofAbs ∈ Padic.coefficientExtensionIntegers l E ↔ _
    rw [coefficientIntegers_mem, coefficientIntegers_mem, coefficient_absolute l E K e]
    rfl)

private def nativeFieldIso (X : Scheme.{u}) :
    latticeCoefficientSheaf X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) ≅
      lisseFieldSheaf l K X := by
  letI := spectralNorm.normedField ℚ_[l] K
  let h : WithAbs (Padic.coefficientExtensionAbsoluteValue l E) ≃ᵢ K :=
    { (nativeFieldRingEquiv l E K e).toEquiv with
      isometry_toFun := nativeField_isometry l E K e }
  apply ObjectProperty.isoMk _
  refine NatIso.ofComponents (fun V ↦
    (ULift.ringEquiv.trans ((continuousMapRingEquiv (nativeFieldRingEquiv l E K e)
      h.continuous h.symm.continuous V.unop.left).trans ULift.ringEquiv.symm)).toCommRingCatIso) ?_
  intro V W f
  rfl

private def nativeIntegerIso (X : Scheme.{u}) :
    latticeCoefficientSheaf X (latticeCoefficientIntegers l E) ≅
      lisseIntegerSheaf l K X := by
  letI := spectralNorm.normedField ℚ_[l] K
  have hi : Isometry (nativeIntegerRingEquiv l E K e) := by
    intro x y
    exact nativeField_isometry l E K e x.val y.val
  let h : latticeCoefficientIntegers l E ≃ᵢ Padic.coefficientExtensionIntegers l K :=
    { (nativeIntegerRingEquiv l E K e).toEquiv with isometry_toFun := hi }
  apply ObjectProperty.isoMk _
  refine NatIso.ofComponents (fun V ↦
    (ULift.ringEquiv.trans ((continuousMapRingEquiv (nativeIntegerRingEquiv l E K e)
      h.continuous h.symm.continuous V.unop.left).trans ULift.ringEquiv.symm)).toCommRingCatIso) ?_
  intro V W f
  rfl

private theorem native_coefficient_square (X : Scheme.{u}) :
    integralLatticeCoefficientMap X l E ≫ (nativeFieldIso l E K e X).hom =
      (nativeIntegerIso l E K e X).hom ≫ lisseIntegerToField l K X := by
  apply Sheaf.hom_ext
  ext V s
  rfl

end CoefficientTransport

attribute [local irreducible] CondensedRing.continuousFieldModuleEquivalence
  CondensedRing.ringModuleEquivalenceOfIso CondensedRing.upperStar

private theorem encoded_pullback_iso
    (l : ℕ) [Fact l.Prime] (K : Type) [NormedField K]
    [NormedAlgebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (T : Type u) [TopologicalSpace T] [CommRing T] [IsTopologicalRing T]
    [TotallyDisconnectedSpace T] (X : Scheme.{u}) {Y : Scheme.{u}}
    (f : Y ⟶ X) [Etale f]
    (eX : latticeModuleRing X T ≅ (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l K X))
    (eY : latticeModuleRing Y T ≅ (sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseFieldSheaf l K Y))
    (hsquare : eY.hom.hom ≫ lisseEtaleCoefficientIdentification l K f =
      ({ app := fun _ ↦ 𝟙 _
         naturality := fun _ _ _ ↦ rfl } : (latticeModuleRing Y T).obj ⟶
          (lisseEtaleSiteInclusion f).op ⋙ (latticeModuleRing X T).obj) ≫
        (lisseEtaleSiteInclusion f).op.whiskerLeft eX.hom.hom)
    (L : SheafOfModules.{u + 1}
      (latticeModuleRing X T)) :
    let FE := CondensedRing.continuousFieldModuleEquivalence l K
    let GX := CondensedRing.ringModuleEquivalenceOfIso X eX
    let GY := CondensedRing.ringModuleEquivalenceOfIso Y eY
    Nonempty (GY.functor.obj ((FE Y).functor.obj
      ((CondensedRing.upperStar (Profinite.continuousMapRingObj K) f).obj
        ((FE X).inverse.obj (GX.inverse.obj L)))) ≅
      continuousModulePullback f T L) := by
  let FE := CondensedRing.continuousFieldModuleEquivalence l K
  let GX := CondensedRing.ringModuleEquivalenceOfIso X eX
  let GY := CondensedRing.ringModuleEquivalenceOfIso Y eY
  let P := (FE X).inverse.obj (GX.inverse.obj L)
  obtain ⟨er⟩ := CondensedRing.continuousField_module_restriction l K X Y f P
  let F := lisseEtaleSiteInclusion f
  let : F.IsContinuous (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X) :=
    Scheme.ProEt.isContinuous_overMap (inferInstance : WeaklyEtale f)
  let j := lisseEtaleCoefficientIdentification l K f
  let j' : (latticeModuleRing Y
      T).obj ⟶
      F.op ⋙ (latticeModuleRing X
        T).obj :=
    { app := fun _ ↦ 𝟙 _
      naturality := fun _ _ _ ↦ rfl }
  let er' := er ≪≫ (PresheafOfModules.pushforward j).mapIso
    ((SheafOfModules.forget _).mapIso ((FE X).counitIso.app (GX.inverse.obj L)))
  obtain ⟨en⟩ := CondensedRing.ringModule_restrictionOfIso X Y F eX eY j j'
    hsquare (GX.inverse.obj L) _ er'
  let a : latticeModuleRing Y T ⟶
      (F.sheafPushforwardContinuous RingCat.{u + 1}
        (Scheme.ProEt.topology Y) (Scheme.ProEt.topology X)).obj
          (latticeModuleRing X T) := ⟨j'⟩
  let ec := GX.counitIso.app L
  let en' := en ≪≫ (PresheafOfModules.pushforward j').mapIso
    ((SheafOfModules.forget _).mapIso ec)
  obtain ⟨ei⟩ := continuous_restriction_iso f
    T L
  let e0 := (SheafOfModules.fullyFaithfulForget _).preimageIso
    (Y := (SheafOfModules.pushforward a).obj L) en'
  exact ⟨e0 ≪≫ ei.symm⟩


section CoefficientTransport
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (K : Type) [NormedField K] [NormedAlgebra ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
  (e : E ≃ₐ[ℚ_[l]] K)

private theorem native_restriction_square (X : Scheme.{u}) {Y : Scheme.{u}}
    (f : Y ⟶ X) [Etale f] :
    let eX := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeFieldIso l E K e X)
    let eY := (sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeFieldIso l E K e Y)
    eY.hom.hom ≫ lisseEtaleCoefficientIdentification l K f =
      ({ app := fun _ ↦ 𝟙 _
         naturality := fun _ _ _ ↦ rfl } : (latticeModuleRing Y
          (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj ⟶
        (lisseEtaleSiteInclusion f).op ⋙ (latticeModuleRing X
          (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))).obj) ≫
        (lisseEtaleSiteInclusion f).op.whiskerLeft eX.hom.hom := by
  ext V s
  rfl

attribute [local irreducible] nativeFieldIso nativeIntegerIso

private theorem native_pullback_iso (X : Scheme.{u}) {Y : Scheme.{u}}
    (f : Y ⟶ X) [Etale f]
    (L : SheafOfModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)))) :
    let FE := CondensedRing.continuousFieldModuleEquivalence l K
    let GX := CondensedRing.ringModuleEquivalenceOfIso X
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeFieldIso l E K e X))
    let GY := CondensedRing.ringModuleEquivalenceOfIso Y
      ((sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeFieldIso l E K e Y))
    Nonempty (GY.functor.obj ((FE Y).functor.obj
      ((CondensedRing.upperStar (Profinite.continuousMapRingObj K) f).obj
        ((FE X).inverse.obj (GX.inverse.obj L)))) ≅
      continuousModulePullback f (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) L) := by
  let T := WithAbs (Padic.coefficientExtensionAbsoluteValue l E)
  let : IsUltrametricDist T :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm (by
      intro x y
      exact isNonarchimedean_spectralNorm (K := ℚ_[l]) (L := E) x.ofAbs y.ofAbs)
  let : TotallyDisconnectedSpace T := inferInstance
  exact encoded_pullback_iso l K T X f
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeFieldIso l E K e X))
    ((sheafCompose (Scheme.ProEt.topology Y)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeFieldIso l E K e Y))
    (native_restriction_square l E K e X f) L

attribute [local semireducible] CondensedRing.ringModuleEquivalenceOfIso

attribute [local semireducible] CondensedRing.upperStar

private theorem native_scalar_iso (X : Scheme.{u})
    (M : ringedSiteModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (lisseIntegerSheaf l K X))) :
    let GI := CondensedRing.ringModuleEquivalenceOfIso X
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeIntegerIso l E K e X))
    let GE := CondensedRing.ringModuleEquivalenceOfIso X
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeFieldIso l E K e X))
    Nonempty (SheafOfModules.changeOfRings.{u, u + 1, u + 1} (integralLatticeCoefficientMap X l E)
        (GI.functor.obj M) ≅
      GE.functor.obj (SheafOfModules.changeOfRings.{u, u + 1, u + 1}
        (lisseIntegerToField l K X) M)) := by
  let J := Scheme.ProEt.topology X
  let R := latticeCoefficientSheaf X (latticeCoefficientIntegers l E)
  let S := latticeCoefficientSheaf X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))
  let R' := lisseIntegerSheaf l K X
  let S' := lisseFieldSheaf l K X
  let er := (nativeIntegerIso l E K e X).symm
  let es := (nativeFieldIso l E K e X).symm
  let a := integralLatticeCoefficientMap X l E
  let a' := lisseIntegerToField l K X
  have hs : a' ≫ es.hom = er.hom ≫ a := by
    dsimp only [a, a', er, es]
    apply (cancel_mono (nativeFieldIso l E K e X).hom).mp
    simp only [Category.assoc, Iso.symm_hom, Iso.inv_hom_id, Category.comp_id]
    rw [native_coefficient_square l E K e X]
    simp
  let t := coefficientTensorPresheafIso.{u} J a a' er es hs M
  let forgetRing := sheafCompose J (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  exact ⟨(PresheafOfModules.sheafification.{u + 1, u, u + 1, u + 1}
    (R := forgetRing.obj S) (𝟙 _)).mapIso t ≪≫
    pushforwardSheafificationIso.{u} J J (𝟭 X.ProEt)
      (forgetRing.obj S') (forgetRing.obj S) (forgetRing.map es.inv)
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} a' M)⟩

end CoefficientTransport

attribute [local semireducible] CondensedRing.ringModuleEquivalenceOfIso
  CondensedRing.continuousFieldModuleEquivalence CondensedRing.upperStar

/-- A lisse rational coefficient module has a lisse integral lattice on a nonempty
quasi-compact open of a nonempty reduced noetherian finite-dimensional scheme.
The coefficient type `WithAbs` equips the field with its canonical extended p-adic
absolute value; `latticeCoefficientIntegers` is its ring of integers. The ringed
pullback along the open immersion is `j⁻¹ L`, with its coefficient action identified
by the canonical continuous-function comparison. No constant or positive rank is required.

Source: Bhatt--Scholze, Lemma 6.8.13, first paragraph; Stacks Tags 03S0 and 0356.
(blueprint: lem-weil-pbc-lisse-lattice-reduced-open)

Proof:
1. Finite dimensionality gives an algebra-isomorphic small coefficient field. The
   equivalence preserves minimal polynomials and the spectral absolute value, hence
   identifies both continuous coefficient sheaves and their integral scalar maps.
2. The continuous etale-local lattice theorem gives a qcqs etale surjection Y to X
   and a locally finite free integral lattice on Y.
3. Apply finite-etale stratification to Y to X. The interiors of the finitely many
   locally closed strata have dense union, so one interior U is nonempty.
4. The pullback of the chosen stratum to U is a surjective immersion, hence a closed
   immersion. As U is reduced, this morphism is an isomorphism. Its inverse gives
   an actual map from U to the stratum; pullback pasting makes Y_U to U finite etale.
5. Pull back the lattice to Y_U and compose scalar and inverse-image comparison
   isomorphisms. Finite-etale lattice descent gives a locally finite free lattice on U.
6. Transport its continuous-module encoding to the original coefficients. The tensor
   comparison identifies rationalization. Composition of site objects is left adjoint
   to base change, and their coefficient maps satisfy the adjunction equations
   pointwise. Uniqueness of left adjoints identifies restriction with the canonical
   ringed pullback in the conclusion.
7. The noetherian space U makes its open immersion quasi-compact. The construction
   allows varying ranks and rank zero. -/
theorem exists_lisse_lattice_reduced_open
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    (X : Scheme.{u}) [IsNoetherian X] [Nonempty X] [IsReduced X]
    (_hdim : ∃ n : ℕ, topologicalKrullDim X ≤ n)
    (_hl : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (L : ringedSiteModules.{u + 1}
      (latticeModuleRing X (WithAbs (Padic.coefficientExtensionAbsoluteValue l E))))
    (_hL : L.IsFiniteLocallyFree) :
    ∃ U : X.Opens, Nonempty U ∧ QuasiCompact U.ι ∧
      ∃ M : ringedSiteModules.{u + 1}
          (latticeModuleRing U.toScheme (latticeCoefficientIntegers l E)),
        M.IsFiniteLocallyFree ∧
        Nonempty (SheafOfModules.changeOfRings.{u, u + 1, u + 1}
          (integralLatticeCoefficientMap U.toScheme l E) M ≅
          continuousModulePullback U.ι
            (WithAbs (Padic.coefficientExtensionAbsoluteValue l E)) L) := by
  classical
  have := _hL
  obtain ⟨K, hK, hAK, hFK, ⟨e⟩⟩ := exists_small_coefficient l E
  let := hK
  let := hAK
  let := hFK
  let := spectralNorm.normedField ℚ_[l] K
  let := spectralNorm.normedAlgebra ℚ_[l] K
  let FE := CondensedRing.continuousFieldModuleEquivalence l K
  let FI := CondensedRing.continuousIntegerModuleEquivalence l K
  let er X := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeFieldIso l E K e X)
  let ea X := (sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso (nativeIntegerIso l E K e X)
  let GX := CondensedRing.ringModuleEquivalenceOfIso X (er X)
  let L' := GX.inverse.obj L
  have : L'.IsFiniteLocallyFree :=
    finiteLocallyFree_restrict (Scheme.ProEt.topology X) _ _ (er X).symm L
  let P := (FE X).inverse.obj L'
  have hP : CondensedRing.LocallyFree _ P := field_inverse_locallyFree l K X L'
  obtain ⟨U, hU, N, hN, ⟨eN⟩⟩ := internal_open_lattice l K X P hP
  let M := (FI U.toScheme).functor.obj N
  have : M.IsFiniteLocallyFree := integer_forward_locallyFree l K U.toScheme N hN
  let GI := CondensedRing.ringModuleEquivalenceOfIso U.toScheme (ea U.toScheme)
  let GE := CondensedRing.ringModuleEquivalenceOfIso U.toScheme (er U.toScheme)
  have hM : (GI.functor.obj M).IsFiniteLocallyFree :=
    finiteLocallyFree_restrict (Scheme.ProEt.topology U.toScheme) _ _ (ea U.toScheme) M
  obtain ⟨eS⟩ := CondensedRing.continuousModuleEncoding_scalar_extension l K U.toScheme M
  let eS' := (FE U.toScheme).functor.mapIso
    ((Mod.extendScalars (coefficientMap
      (CondensedRing.integralScalarMap l K) U.toScheme)).mapIso
        ((FI U.toScheme).unitIso.app N)) ≪≫ eS
  have hqc : QuasiCompact U.ι := inferInstance
  obtain ⟨es⟩ := native_scalar_iso l E K e U.toScheme M
  obtain ⟨ep⟩ := native_pullback_iso l E K e X U.ι L
  refine ⟨U, hU, hqc, GI.functor.obj M, hM, ⟨?_⟩⟩
  exact es ≪≫
    GE.functor.mapIso (eS'.symm ≪≫ (FE U.toScheme).functor.mapIso eN) ≪≫
      ep

end AlgebraicGeometry.ProEtale

#print axioms AlgebraicGeometry.ProEtale.exists_lisse_lattice_reduced_open
