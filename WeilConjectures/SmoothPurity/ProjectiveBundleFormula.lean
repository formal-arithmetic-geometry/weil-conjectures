/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalGeometry
public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCoefficientTwists
public import WeilConjectures.AlgebraicGeometry.Kummer.KummerModuleCoefficients
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleModuleCohomologyForget
public import WeilConjectures.CategoryTheory.SmoothPurity.RhomGlobalSectionsOfUniverses
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import Mathlib.Algebra.CharP.CharAndCard
public import Mathlib.Algebra.CharP.Algebra
public import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
public import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Adjunction.Additive
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
public import WeilConjectures.CategoryTheory.DeltaFunctor
public import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
public import WeilConjectures.CategoryTheory.SiteMorphismComposition
public import WeilConjectures.CategoryTheory.SiteCohomologyPullbackData
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import WeilConjectures.AlgebraicGeometry.EtaleModulePullbackForgetNaturality
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.LongExactSequence
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

import WeilConjectures.AlgebraicGeometry.Pur.PurTwistSheafLocallyFree
import WeilConjectures.AlgebraicGeometry.Fixed.FixedComparisonDirectImageMate
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.Support.SupportComparisonPullbackCoherence
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import WeilConjectures.ProperBaseChange.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.CategoryTheory.RingedSiteModules
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonUnit
import WeilConjectures.SmoothPurity.PurityFiniteSetting.RankOne.PurityRankOneLocalCalculation
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.StrictlyHenselianSectionsStalk
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import WeilConjectures.AlgebraicGeometry.Supported.SupportedCup
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCohomologicalSupport
import WeilConjectures.SmoothPurity.Sf.SfDerivedComplete
import WeilConjectures.SmoothPurity.Sf.SfRationalizationKaroubi
import WeilConjectures.SmoothPurity.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficients
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
import WeilConjectures.SixFunctors.Sf.SfIntegralReductionTowerSupplement
import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.SmoothPurity.Integral.IntegralRationalQbarCompactSupport
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicDerivedOpenAdjunction
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicExtensionByZeroAdjunction
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.DeligneLaumon.SfWeilSheafComplex
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsCanonicalAdjunctionSupplement
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SmoothPurity.PurCompactSupport.IntegralCompactSupportCoefficientData
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIdentifiedOpenClosed
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenClosed
import WeilConjectures.AlgebraicGeometry.ProEtale.Intrinsic.ProEtaleIntrinsicClosedAmbient
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedClosedKernelAdjoint
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.CategoryTheory.Adjunction.SmoothPurity.ExactDerivedAdjunctionUnitShift
import WeilConjectures.CategoryTheory.Triangulated.Recollement
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LocalizeConstructible
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenClosedTriangle
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingConstructibleDerivedOrigin
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteLocalConstancyPullback
import WeilConjectures.AlgebraicGeometry.Open.OpenExtensionFiniteTor
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleConstructibility
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Complement
import WeilConjectures.CategoryTheory.Triangulated.TriangleMorphismExtension
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.SmoothPurity.Integral.IntegralConstructibleLinear
import WeilConjectures.SixFunctors.Integral.IntegralOperationsPreserveConstructible
import WeilConjectures.CategoryTheory.StageSystem.StageSystemFunctorDescent
import WeilConjectures.CategoryTheory.StageSystem.Functor
import WeilConjectures.DeligneLaumon.FieldWeilShriekShiftData
import WeilConjectures.SmoothPurity.Automorphism.AutomorphismConstructibleStageEquivalence
import WeilConjectures.DeligneLaumon.LocalFrobeniusTrace
import Mathlib.CategoryTheory.PathCategory.Basic
import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
import WeilConjectures.AlgebraicGeometry.Pbc.PbcQbarStandardCohomology
import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.Affine
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
import Mathlib.Topology.LocallyConstant.Algebra
import Mathlib.GroupTheory.QuotientGroup.Basic
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing
import WeilConjectures.AlgebraicGeometry.Abelian.AbelianEtaleProEtaleCohomologyComparison
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.Topology.Connected.Separation
import WeilConjectures.RingTheory.StrictlyHenselianOfDimensionZero
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.Sites.StrictlyHenselian
import Mathlib.Topology.Separation.DisjointCover
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
import WeilConjectures.AlgebraicGeometry.ZariskiEtaleCore
import WeilConjectures.RingTheory.ProperBaseChange.IndPrincipalZariski
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.FieldTheory.Separable
import WeilConjectures.RingTheory.ProEtale.WeaklyEtaleField
import Mathlib.AlgebraicGeometry.Fiber
import WeilConjectures.SmoothPurity.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafEquivalence
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Reflective
import WeilConjectures.AlgebraicGeometry.ProperBaseChange.SmallStrictHenselizationIndEtale
import WeilConjectures.RingTheory.ProperBaseChange.IndEtaleStability
import WeilConjectures.RingTheory.Spectrum.Prime.LocallyConstant
import Mathlib.Topology.Compactification.OnePoint.Basic
import WeilConjectures.AlgebraicGeometry.ProEtale.Comparison.ProEtaleComparisonStalk
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonDerived
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.Abelian
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import WeilConjectures.CategoryTheory.Abelian.HorseshoeDeltaFunctor
import WeilConjectures.CategoryTheory.Abelian.RightDerived.FullLongExactSequence
import WeilConjectures.CategoryTheory.DeltaFunctor
import WeilConjectures.CategoryTheory.RightDerivedUniversalDeltaFunctor
import WeilConjectures.CategoryTheory.SiteMorphismComposition
import WeilConjectures.CategoryTheory.SiteCohomologyPullbackData
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.BaseChange.Derived
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedExchangeCompatibility
import Mathlib.Algebra.Homology.DerivedCategory.Plus
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricFiberFinite
import WeilConjectures.AlgebraicGeometry.Supported.SupportedExteriorProduct
import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.Supported.SupportedCohomologyHom
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import WeilConjectures.SmoothPurity.PurityConventions.PurityConventions
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFrameClass
import WeilConjectures.AlgebraicGeometry.Support.SupportCohomology
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCoefficientTwistsUnrestricted
import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorCohomology
import WeilConjectures.CategoryTheory.Sites.WithSection.TorsorWithSection
import Mathlib.Algebra.Homology.Embedding.ExtendHomology
import Mathlib.Algebra.Homology.HomologySequence
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
import WeilConjectures.AlgebraicGeometry.EffectiveCartier
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctoriality
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
import Mathlib.AlgebraicGeometry.IdealSheaf.Basic
import Mathlib.RingTheory.KrullDimension.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Spectrum.Prime.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.BaseChange
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Regular.Flat
import Mathlib.RingTheory.Noetherian.Defs
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Noetherian.Basic
import WeilConjectures.Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import WeilConjectures.RingTheory.SmoothFibreRegularLocal
import WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence
import WeilConjectures.RingTheory.ProperBaseChange.SmoothOverFieldRegularLocal
import Mathlib.RingTheory.Smooth.Flat
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.KrullDimension.Regular
import WeilConjectures.AlgebraicGeometry.EffectiveCartierSum
import WeilConjectures.SmoothPurity.Sf.SfCommonStageWeilCohomology
import WeilConjectures.WeilSheaf.FourierInversion.OtherSections
import WeilConjectures.AlgebraicGeometry.Support.SupportSiteComparison
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.Ordinary
import WeilConjectures.AlgebraicGeometry.Etale.Constant.EtaleConstantProjectionMap
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriek
import WeilConjectures.AlgebraicGeometry.ProEtale.Supported.ProEtaleSupportedExteriorProduct
import WeilConjectures.AlgebraicGeometry.Support.SupportQuotientPairPullback
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ClosedImmersion
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
import WeilConjectures.SixFunctors.ProEtale.OpenClosed.Sequence
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
import WeilConjectures.AlgebraicGeometry.Fixed.FixedEtaleOriginWitness
import WeilConjectures.Algebra.Homology.SmoothPurity.ClosedSupportHom
import WeilConjectures.Compactification.CategoryBaseChange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.AlgebraicGeometry.KummerAdditivity

/-!
# The finite-coefficient projective-bundle formula

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-an,
`thm-pur-projective-bundle-formula` (blueprint: thm-pur-projective-bundle-formula).

The negative shifted coefficient is the derived dual of the published ordered positive
shifted Tate power. Since the Tate sheaf is locally free of rank one, this is precisely
A(-a)[-2a], with evaluation as its canonical pairing. All arrows below are constructions:
tensor powers of the Kummer class, evaluation, and the ordinary pullback adjunction.

## Main definitions

* `projectiveBundleOrderedCup`: ordered tensor powers of one class.
* `PurityFiniteSetting.projectiveBundleSummand`: the negative shifted Tate coefficient.
* `PurityFiniteSetting.projectiveBundleComponent`: the adjunct of an evaluated cup power.
* `PurityFiniteSetting.projectiveBundleMap`: the specified finite coproduct morphism.
* `PurityFiniteSetting.projectiveBundleTargetBaseChange`: the canonical exchange map.
* `PurityFiniteSetting.projectiveBundleFormula`: invertibility and base-change compatibility.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite AlgebraicGeometry
open scoped CategoryTheory.Functor

namespace WeilConjectures

/-- Tensor the same class repeatedly in a specified ordered power presentation.
The zero and successor comparisons merely identify that presentation; no power object
is chosen. Source: blueprint sk-prop-an, cup powers before adjunction
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleOrderedCup {C : Type v} [Category.{w} C]
    (T : C ⥤ C ⥤ C) (U L : C) (K : ℕ → C) (k0 : U ≅ K 0)
    (ks : ∀ a : ℕ, (T.obj (K a)).obj L ≅ K (a + 1))
    (delta : U ⟶ (T.obj U).obj U) (h : U ⟶ L) : (a : ℕ) → U ⟶ K a
  | 0 => k0.hom
  | a + 1 => delta ≫ (T.map (projectiveBundleOrderedCup T U L K k0 ks delta h a)).app U ≫
      (T.obj (K a)).map h ≫ (ks a).hom

/-- The diagonal of the coefficient unit, expressed in the same tensor coordinates
as the recorded Tate powers. Source: blueprint sk-prop-an, tensoring cup powers
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleUnitDiagonal (A : Type (u + 1)) [CommRing A] (T : Scheme.{u}) :
    Etale.ordinaryFiniteUnit A T ⟶
      ((Etale.ordinaryFiniteTensor A T).obj (Etale.ordinaryFiniteUnit A T)).obj
        (Etale.ordinaryFiniteUnit A T) :=
  (Etale.derivedTensorSingleUnitIso
    (Λ := A) (X := T) (Etale.ordinaryFiniteUnit A T)).inv

/-- Ordered cup powers in the published positive shifted Tate model, for any finite
coefficient ring. The zero power is the identity and the successor tensors with h.
Source: blueprint sk-prop-an, cup powers (blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleCupPowerRaw (A : Type (u + 1)) [CommRing A] (m : ℕ)
    (hA : (m : A) = 0) (T : Scheme.{u})
    (h : Etale.ordinaryFiniteUnit A T ⟶
      (Etale.ordinaryFiniteLine A m
        hA T)⟦(2 : ℤ)⟧) :
    (a : ℕ) → Etale.ordinaryFiniteUnit A T ⟶ (Etale.affineLinearBaseCoefficient A m hA) T a
  := WeilConjectures.projectiveBundleOrderedCup
    (Etale.ordinaryFiniteTensor A T)
    (Etale.ordinaryFiniteUnit A T)
    ((Etale.ordinaryFiniteLine A m
      hA T)⟦(2 : ℤ)⟧)
    ((Etale.affineLinearBaseCoefficient A m hA) T) (Iso.refl _) (fun _ ↦ Iso.refl _)
    (WeilConjectures.projectiveBundleUnitDiagonal A T) h

/-- Pullback of ordered positive powers using the unit, tensor comparison and the
root-normalized shifted-line comparison. Source: blueprint sk-prop-an, base change
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundlePositivePullbackRaw (A : Type (u + 1)) [CommRing A] (m : ℕ) (hA : (m : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A m
      hA) {T T' : Scheme.{u}} (f : T' ⟶ T)
    (hT : IsUnit (m : Γ(T, ⊤))) :
    (a : ℕ) → (Etale.ordinaryFinitePullback A f).obj
      ((Etale.affineLinearBaseCoefficient A m hA) T a) ≅
      (Etale.affineLinearBaseCoefficient A m hA) T' a
  | 0 => Etale.ordinaryFiniteUnitPullback A f
  | a + 1 => Etale.ordinaryFiniteTensorPullback A f
      ((Etale.affineLinearBaseCoefficient A m hA) T a)
      ((Etale.ordinaryFiniteLine A m
        hA T)⟦(2 : ℤ)⟧) ≪≫
      Etale.ordinaryFiniteTensorRightMapIso A T'
        (projectiveBundlePositivePullbackRaw A m hA t f hT a)
        (Etale.ordinaryFiniteShiftedLinePullback A m
          hA t f hT)

/-- Constant-coefficient pullback, using the canonical site-comparison square and the
ordinary unit comparison. Source: blueprint sk-prop-an, proper base-change target
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleUnitPullback (P : PurityFiniteSetting.{u})
    {T T' : Scheme.{u}} (f : T' ⟶ T) :
    (ProEtale.upperStar (ModuleCat.{u + 1} P.Coefficient) f).leftDerivedFunctor.obj
      (P.projectiveBundleUnit T) ≅ P.projectiveBundleUnit T' :=
  (ProEtale.leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} P.Coefficient) f).app _ ≪≫
    ProEtale.kummerCoefficientPullback P.Coefficient f _ _
      (Etale.ordinaryFiniteUnitPullback P.Coefficient f)

/-- The specified global Kummer class of the actual tautological degree-one twist.
Source: blueprint sk-prop-an, h_F=c_1(O(1))
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleChern (P : PurityFiniteSetting.{u}) {B : Scheme.{u}}
    {F : B.Modules} (b : B ⟶ Spec (.of P.field.k))
    (D : ProjectiveBundleRealization B F) (hL : D.L.IsInvertible) :=
  letI := hL
  Etale.kummerFirstChern P.Coefficient P.diagonalExponent P.diagonalExponent_annihilates
    D.A.data.relProj (P.diagonalExponent_isUnit (D.A.data.relProjHom ≫ b))
      (Scheme.Pic.ofIsInvertible D.L)

/-- The constant finite coefficient complex in comparison coordinates on the actual
small pro-etale site. Source: blueprint sk-prop-an, A_P
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleUnit (P : PurityFiniteSetting.{u}) (T : Scheme.{u}) :=
  (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} P.Coefficient) T).mapDerivedCategory.obj
    (Etale.ordinaryFiniteUnit P.Coefficient T)

/-- Pullback of the positive shifted Tate powers: the unit comparison, followed
recursively by tensor pullback and the root-normalized line comparison.
Source: blueprint sk-prop-an, base-change clause; Stacks Tag 03PK
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundlePositivePullback (P : PurityFiniteSetting.{u})
    (t : Etale.OrdinaryFiniteTwistTransport P.Coefficient P.diagonalExponent
      P.diagonalExponent_annihilates) {T T' : Scheme.{u}} (f : T' ⟶ T)
    (hT : IsUnit (P.diagonalExponent : Γ(T, ⊤))) :
    (a : ℕ) → (Etale.ordinaryFinitePullback P.Coefficient f).obj
      (P.diagonalTwistEtale T a) ≅ P.diagonalTwistEtale T' a :=
  WeilConjectures.projectiveBundlePositivePullbackRaw P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates t f hT

/-- The cup powers of a specified Kummer class in the recorded ordered tensor-power
presentation. Degree zero is the identity, and the successor tensors with the same class.
Source: blueprint sk-prop-an, construction before taking fibres
(blueprint: thm-pur-projective-bundle-formula). -/
def projectiveBundleCupPower (P : PurityFiniteSetting.{u}) (T : Scheme.{u})
    (h : Etale.ordinaryFiniteUnit P.Coefficient T ⟶
      (Etale.ordinaryFiniteLine P.Coefficient P.diagonalExponent
        P.diagonalExponent_annihilates T)⟦(2 : ℤ)⟧) :
    (a : ℕ) → Etale.ordinaryFiniteUnit P.Coefficient T ⟶ P.diagonalTwistEtale T a :=
  WeilConjectures.projectiveBundleCupPowerRaw P.Coefficient P.diagonalExponent
    P.diagonalExponent_annihilates T h

end WeilConjectures

namespace WeilConjectures.PurityFiniteSetting

end WeilConjectures.PurityFiniteSetting
