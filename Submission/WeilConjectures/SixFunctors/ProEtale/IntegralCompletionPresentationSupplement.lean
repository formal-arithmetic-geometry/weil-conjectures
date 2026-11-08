/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.SixFunctors.ProEtale.Encoding.IntegralPresentationEncodingSupplement
public import Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEncodingSupplement
public import Submission.WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
public import Submission.WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
import Submission.WeilConjectures.CategoryTheory.InverseMateEquivalence
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientData
import Mathlib.CategoryTheory.Sites.ConstantSheaf
import Mathlib.Topology.Category.Profinite.AsLimit
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Submission.WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
import Submission.WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
import Submission.WeilConjectures.CategoryTheory.SheafTensor
import Submission.WeilConjectures.CategoryTheory.SheafTensorStructure
import Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Monoidal.Preadditive
import Submission.WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import Submission.WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Sites.Localization
import Mathlib.CategoryTheory.Sites.Sheafification
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Submission.WeilConjectures.Topology.ContinuousMapCondensedRing
import Submission.WeilConjectures.NumberTheory.Padics.IntegersProfiniteTower
import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import Submission.WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
import Mathlib.RingTheory.Ideal.Quotient.Index
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Algebra.Ring.Pi
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Compactness.Compact
import Submission.WeilConjectures.NumberTheory.Padics.IntegersCosetBasis
import Mathlib.Topology.Bases
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.NumberTheory.Padics.ProperSpace
import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrCore
import Mathlib.Analysis.Normed.Algebra.Ultra
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorization
import Submission.WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvrFactorizationUnique
import Submission.WeilConjectures.Mathlib.RingTheory.OrderOfVanishing.Noetherian
import Submission.WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import Submission.WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import Submission.WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Category.Profinite.CofilteredLimit
import Submission.WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Submission.WeilConjectures.AlgebraicGeometry.ProfiniteLocallyConstantAdjunction
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteConstantRepresentable
import Submission.WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.FintypeCat
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Submission.WeilConjectures.AlgebraicGeometry.CoproductCopiesMorphismsClopen
import Mathlib.AlgebraicGeometry.OpenImmersion
import Submission.WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Presheaf
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralRingComparison
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleIntegralPointRingMap
import Submission.WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import Submission.WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.CategoryTheory.Monoidal.Mon
import Submission.WeilConjectures.AlgebraicGeometry.Finite.FiniteDiscreteSchemeRingSupplement
import Submission.WeilConjectures.AlgebraicGeometry.FiniteDiscreteCoefficientTerminal
import Submission.WeilConjectures.AlgebraicGeometry.DerivedNakayamaResolution
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientUniverse
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Submission.WeilConjectures.CategoryTheory.RingObjects.ContinuousMap
import Mathlib.Condensed.TopComparison
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import Mathlib.Topology.Algebra.Ring.Ideal
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import Submission.WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import Submission.WeilConjectures.SixFunctors.ProEtale.Adic.PadicIntSheafLinear
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.TensorMappingCone
import Submission.WeilConjectures.CategoryTheory.Monoidal.Closed.UnitEnd
import Mathlib.CategoryTheory.Center.Linear
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Kernels
import Submission.WeilConjectures.NumberTheory.Padics.ContinuousUniformizerDivision
import Mathlib.Topology.Algebra.Order.Field
import Submission.WeilConjectures.Mathlib.CategoryTheory.Functor.Flat
import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import Submission.WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Submission.WeilConjectures.SixFunctors.ProEtale.GaloisEvaluation
import Mathlib.Topology.Category.Profinite.Limits
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleFiniteReductionPullback
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientRealizations
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Submission.WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
import Mathlib.Topology.Algebra.Valued.NormedValued
import Mathlib.Topology.ContinuousMap.Compact
import Submission.WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.CategoryTheory.Abelian.ShortExact
import Submission.WeilConjectures.AlgebraicGeometry.CondensedFieldContinuousRealization
import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructiblePullback
import Submission.WeilConjectures.CategoryTheory.Monoidal.Conjugate
import Submission.WeilConjectures.ConstructibleSheaf.Pullback
import Submission.WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Mathlib.Topology.NoetherianSpace
import Submission.WeilConjectures.AlgebraicGeometry.ProEtalePointComponentsMaps
import Submission.WeilConjectures.Topology.SpectralSpace.ConnectedComponent
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleSheafificationWcontractibleSections
import Submission.WeilConjectures.AlgebraicGeometry.PointLanAffineEvaluation
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Category.Ring.Basic
import Submission.WeilConjectures.AlgebraicGeometry.PointLanFiniteProducts
import Submission.WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductEvaluation
import Submission.WeilConjectures.AlgebraicGeometry.FiniteCoproductLfpQcqs
import Submission.WeilConjectures.AlgebraicGeometry.Sites.ProEtaleFiniteCoproductSections
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineContractibleExtension
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleAffineWeaklyContractibleCover
import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
import Submission.WeilConjectures.AlgebraicGeometry.IntegralScalarContractive
import Submission.WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import Submission.WeilConjectures.CategoryTheory.RingObjects.Ab
import Submission.WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import Submission.WeilConjectures.CategoryTheory.RingedSiteModules
import Submission.WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Submission.WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.CategoryTheory.Sites.Equivalence
import Submission.WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import Mathlib.CategoryTheory.Monoidal.Ring
import Submission.WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Submission.WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Submission.WeilConjectures.AlgebraicGeometry.LisseLatticeCoefficients
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousChartSchemeNaturality
import Submission.WeilConjectures.AlgebraicGeometry.IntegralMatrixAnalyticData
import Mathlib.Data.Matrix.Basic
import Submission.WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncoding
import Mathlib.Order.CompletePartialOrder
import Submission.WeilConjectures.SixFunctors.ProEtale.IntegralReductionTransitionComparison
import Submission.WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
public import Submission.WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import Submission.WeilConjectures.SixFunctors.ProEtale.IntegralCompletionPresentation

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Canonical completeness in the completed integral presentation

Source: blueprint main-20261015, integral-criterion-reductions, final sentence;
Stacks Project, Tags 06YY, 0941, 08TC and 0145
(blueprint: lem-pe-integral-completion-presentation).

The coefficient identification is normalized by every finite restriction square.
Finite comparisons retain their finite coefficient action.
Their restriction squares are normalized on underlying abelian sheaves, and their
units fix the derived comparisons uniquely. The index n denotes exponent n+1.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u d

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open WeilConjectures

namespace AlgebraicGeometry.ProEtale.IntegralPresentation

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u}) (A : Encoding l E X)

/-- A comparison in D(R_n), retaining the finite coefficient action.
Source: Stacks 06YY, derived tensor under an isomorphism of coefficients
(blueprint: lem-pe-integral-completion-presentation). -/
abbrev FiniteComparison (n : ℕ) (e : FiniteEncoding l E X n) :=
  letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  A.derived.functor ⋙
      scalarReductionDerivedExtension.{u, u} l E X n ≅
    AdicCompletion.derivedReduction l E X n ⋙ e.ordinaryDerived.functor

end AlgebraicGeometry.ProEtale.IntegralPresentation
