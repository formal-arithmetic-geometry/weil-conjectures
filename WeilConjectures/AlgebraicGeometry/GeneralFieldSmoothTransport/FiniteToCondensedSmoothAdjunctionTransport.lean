/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarLines
public import WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived.ExactMonoidalEquivalenceDerived
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartTensor
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
public import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekIndependence
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsComp
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionGeneralBase
public import WeilConjectures.AlgebraicGeometry.CoefficientHomComparison.ConstructibleCoefficientHomComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.GeneralFieldLocalizingTools
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityNormalizedTowers
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothAdjunctionData
import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
import WeilConjectures.Compactification.RefinementCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdjunctionShift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DerivedDirectImageOpenCoherenceData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedPullbackTensorComparison
import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProjectionMapShift
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.AlgebraicGeometry.TowerOpenCover.TowerOpenCoverTriangleData
import WeilConjectures.Algebra.Homology.OpenCoverMateComplexShortExact
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenComparison
import WeilConjectures.Algebra.Homology.Scalar.ScalarExtensionRingIsoSupplement
import WeilConjectures.Algebra.Homology.SubterminalLocal.SubterminalModuleLocalCalculus
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.AlgebraicGeometry.RingedRestrictionExchange.ProEtaleRingedOpenCoverReflectsIso
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalCompDerived
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformationOplax
import WeilConjectures.CategoryTheory.Exact.ExactFunctorCoproducts
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportDerivedLocalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionIhom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.DerivedOpenRestrictionSuccessive
import WeilConjectures.CategoryTheory.SmoothPurity.CompactSupportIdentityCalculus
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.CompactificationIndependence
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedContinuityDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedContinuitySections
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstruction

/-! # Finite-to-condensed smooth adjunction transport over perfect fields

Source: current blueprint, sk-thm-purity-transport, Steps 1--4, and
thm-a1-curve-perverse-heart, Step 2.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.GeneralFieldSmoothTransport
open PurityTransport

attribute [instance] Base.field Base.perfect

attribute [instance] Index.xSmooth Index.ySmooth Index.xFinite Index.yFinite
  Index.xCompact Index.yCompact Index.xSeparated Index.ySeparated Index.isOver
  Index.smooth Index.separated Index.finiteType Index.quasiCompact
  Index.noetherianX Index.noetherianY

variable (ell : ℕ) [Fact ell.Prime]

/-- Derive the exact finite encoding with its K-flat tensorator.
Source: finite tensor realization.
(blueprint: lem-per-finite-to-condensed-smooth-adjunction-transport). -/
@[instance_reducible] def finiteDerivedMonoidal
    (A : Type) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [DiscreteTopology A] [Finite A] (X : Scheme.{u})
    (m : (finiteEncoding A X).inverse.Monoidal) :
    (finiteEncodingDerived A X).inverse.Monoidal := by
  let F := (finiteEncoding A X).inverse
  letI : F.Monoidal := m
  letI : F.PreservesFlat := Functor.preservesFlat_of_isEquivalence F
  letI : F.leftDerivedFunctor.Monoidal := F.leftDerivedFunctorMonoidal
  exact Functor.Monoidal.transport F.leftDerivedFunctorIsoMapDerivedCategory

end AlgebraicGeometry.ProEtale.GeneralFieldSmoothTransport
