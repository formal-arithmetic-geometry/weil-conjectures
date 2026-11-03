/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedDncFamily
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SectionInvariant
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnitConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.ZetaWeil.PodCtfAdjunctionData.PodCtfAdjunctions
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.Algebra.Homology.Strict.StrictPerfectCoefficientPackageOfUniverses
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Conservative
public import Mathlib.Data.Finset.Max
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AdmissibleBoundedConstructibleTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedPointModuleComparison
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenFiltrationSuccessor
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import WeilConjectures.ConstructibleSheaf.Devissage
public import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
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
public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.NativeInternalHomExact
public import Mathlib.CategoryTheory.Triangulated.Opposite.Subcategory
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.SixFunctors.ShriekCoefficientIsomorphism
public import WeilConjectures.CategoryTheory.Brown.BrownHypothesesStructural
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingExceptionalPreservation
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralCompactSupport.IntegralExceptionalRestriction
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Rational.RationalRestrictionGlue
public import WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived.ExactMonoidalEquivalenceDerived
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteLocalizingSmoothLocalFormula
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCoefficientUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Shift
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
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
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantModelLocalResolution
public import WeilConjectures.ProperBaseChange.IntegralLfpLocallyFreeResolution
public import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
public import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import Mathlib.Topology.Defs.Filter
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import Mathlib.CategoryTheory.ObjectProperty.Shift
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
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
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
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.CategoryTheory.SixFunctors.LocalizingClosure
public import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
public import WeilConjectures.CategoryTheory.Brown.BrownHypotheses
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingCompactificationCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ReductionNakayama
public import WeilConjectures.NumberTheory.Padics.Extension
public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
import WeilConjectures.AlgebraicGeometry.DeformationSpace.SmoothProj

/-! # DNC invariance for all four condensed coefficients

Source: latest blueprint,
sec-smooth-purity/sk-thm-dnc/thm-pur-dnc-invariance.md
and its proof (blueprint: thm-pur-dnc-invariance).
The normal and Rees pairs are the actual schemes. Their fibre maps are the native
exceptional counit mates with canonical pullback compositors. Normalization compares the
one and zero restrictions of every constant presentation of the family after arbitrary
finite-type base change; thus no auxiliary orientation or arbitrary endpoint map is chosen.
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

variable (D : WeilConjectures.FiniteFieldDatum.{u})

local instance datumPrime : Fact D.p.Prime := ⟨D.prime⟩
local instance datumChar : CharP D.k₀ D.p := by
  let _ : Fintype D.k₀ := Fintype.ofFinite D.k₀
  exact charP_of_card_eq_prime_pow
    ((Nat.card_eq_fintype_card (α := D.k₀)).symm.trans
      (D.card_base.trans D.cardinality_eq))
local instance closureChar : CharP D.k D.p := charP_of_injective_algebraMap' D.k₀ D.p
local instance closurePrime : Fact (ringChar D.k).Prime :=
  ⟨(ringChar.eq D.k D.p).symm ▸ D.prime⟩
local instance closureClosed : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀

variable (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (hcoeff :
    (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
    Finite A ∧ (∃ N : ℕ, ∀ a : A, (ell ^ N) • a = 0) ∧
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))

set_option maxHeartbeats 2000000 in
-- Checking the large normalized coherence witness exceeds the default kernel heartbeat budget.
private theorem sectionBaseChangeMap_isIso {X Y X' Y' : Over (Spec (.of D.k))}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
    [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
    (g : X ⟶ Y) (g' : X' ⟶ Y') (v : X'.left ⟶ X.left) (b : Y'.left ⟶ Y.left)
    (sq : IsPullback v g'.left g.left b)
    (s : Y.left ⟶ X.left) (s' : Y'.left ⟶ X'.left)
    (hsection : s' ≫ v = b ≫ s)
    [IsIso (dualizingBaseChangeMap D ell hell E n hn Λ hcoeff g g' v b sq)] :
    IsIso (sectionBaseChangeMap D ell hell E n hn Λ hcoeff g g' v b sq s s' hsection) := by
  let Ω := (dualizing D ell hell E n hn Λ hcoeff g).obj
  let c₁ := (leftDerivedUpperStarComp Λ b s).app Ω
  let c₂ := (leftDerivedUpperStarComp Λ s' v).app Ω
  let e := congrArg (fun f ↦ (moduleObjectDerivedPullback Λ f).obj Ω) hsection.symm
  let β := dualizingBaseChangeMap D ell hell E n hn Λ hcoeff g g' v b sq
  have hβ : IsIso ((moduleObjectDerivedPullback Λ s').map β) := inferInstance
  exact @IsIso.comp_isIso _ _ _ _ _ c₁.inv _ (inferInstance) (
    @IsIso.comp_isIso _ _ _ _ _ (eqToHom e) _ (inferInstance) (
      @IsIso.comp_isIso _ _ _ _ _ c₂.hom _ (inferInstance) hβ))

end AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

namespace AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

attribute [instance] Pair.base_ft Pair.base_qc Pair.base_sep Pair.source_ft Pair.source_qc
  Pair.source_sep Pair.smooth Pair.separated Pair.finite_type Pair.qc Pair.closed

variable {D : WeilConjectures.FiniteFieldDatum.{u}}

end AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

namespace AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

variable {D : WeilConjectures.FiniteFieldDatum.{u}}
  (ell : ℕ) [Fact ell.Prime] (hell : ell ≠ D.p)
  (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (hn : 1 ≤ n)
  (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  (hcoeff :
    (∃ (A : Type) (_ : CommRing A) (_ : TopologicalSpace A)
      (_ : DiscreteTopology A) (_ : IsTopologicalRing A),
    Finite A ∧ (∃ N : ℕ, ∀ a : A, (ell ^ N) • a = 0) ∧
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj A))) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
    Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))

private theorem atOne_isIso_of_dualizing (Q : Pair D)
    [IsIso (dualizingBaseChangeMap D ell hell E n hn Λ hcoeff Q.rees.g Q.g
      (Scheme.Hom.deformationSpaceOneFibre Q.g.left Q.s.left)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) Q.B.left)
      (Scheme.Hom.isPullback_deformationSpaceOneFibre Q.g.left Q.s.left))] :
    IsIso (atOne ell hell E n hn Λ hcoeff Q) := by
  apply sectionBaseChangeMap_isIso

private theorem atZero_isIso_of_dualizing (Q : Pair D)
    [IsIso (dualizingBaseChangeMap D ell hell E n hn Λ hcoeff Q.rees.g Q.normal.g
      Q.s.left.ker.normalConeToDeformationSpace
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Q.B.left)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace Q.g.left Q.s.left))] :
    IsIso (atZero ell hell E n hn Λ hcoeff Q) := by
  apply sectionBaseChangeMap_isIso

/-- Both specified native fibre maps are invertible.
Source: sk-lem-geometry (1), proof Step 5 (blueprint: thm-pur-dnc-invariance).
Proof: the Rees one and zero squares identify the pairs with (g,s) and its normal
bundle zero section. Apply smooth exceptional base change to the coefficient unit;
pull its specified counit mate to the sections and compose the canonical pullback
compositors. This proves invertibility of exactly atOne and atZero for all four
coefficient presentations, with no orientation assumed. -/
theorem fibreMaps_isIso (Q : Pair D) (d : ℕ)
    [SmoothOfRelativeDimension d Q.g.left] :
    IsIso (atOne ell hell E n hn Λ hcoeff Q) ∧
      IsIso (atZero ell hell E n hn Λ hcoeff Q) := by
  let hs : Q.s.left ≫ Q.g.left = 𝟙 Q.B.left :=
    congrArg (fun f ↦ f.left) Q.section_eq
  letI : SmoothOfRelativeDimension d Q.rees.g.left :=
    Scheme.Hom.smoothOfRelativeDimension_deformationSpaceProj d Q.g.left Q.s.left hs
  letI : IsIso (dualizingBaseChangeMap D ell hell E n hn Λ hcoeff Q.rees.g Q.g
      (Scheme.Hom.deformationSpaceOneFibre Q.g.left Q.s.left)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) Q.B.left)
      (Scheme.Hom.isPullback_deformationSpaceOneFibre Q.g.left Q.s.left)) :=
    native_dualizingBaseChangeMap_isIso_of_smooth (D := D) ell hell E n hn Λ hcoeff
      Q.rees.g Q.g (Scheme.Hom.deformationSpaceOneFibre Q.g.left Q.s.left)
      (AffineSpace.oneSection (ULift.{u} (Fin 1)) Q.B.left)
      (Scheme.Hom.isPullback_deformationSpaceOneFibre Q.g.left Q.s.left) d
  have hone : IsIso (atOne ell hell E n hn Λ hcoeff Q) :=
    atOne_isIso_of_dualizing ell hell E n hn Λ hcoeff Q
  letI : SmoothOfRelativeDimension d Q.normal.g.left :=
    (Scheme.Hom.normalConeData d hs).smoothOfRelativeDimension_proj
  letI : IsIso (dualizingBaseChangeMap D ell hell E n hn Λ hcoeff Q.rees.g Q.normal.g
      Q.s.left.ker.normalConeToDeformationSpace
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Q.B.left)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace Q.g.left Q.s.left)) :=
    native_dualizingBaseChangeMap_isIso_of_smooth (D := D) ell hell E n hn Λ hcoeff
      Q.rees.g Q.normal.g Q.s.left.ker.normalConeToDeformationSpace
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) Q.B.left)
      (Scheme.Hom.isPullback_normalConeToDeformationSpace Q.g.left Q.s.left) d
  exact ⟨hone, atZero_isIso_of_dualizing ell hell E n hn Λ hcoeff Q⟩

/-- Native-coefficient constancy of the section DNC family, normalized at one.
Source: `prop-pur-dnc-family-constancy`, clauses (2), (3), (4)
(blueprint: prop-pur-native-dnc-family-constancy).
Proof: smooth purity makes the family a shifted lisse line. Centred etale coordinates
identify it with the pullback of the standard section line. Normalize these comparisons
by the specified one-fibre mate. Their transition automorphisms are locally constant
units, determined at the one-section; hence the normalized comparisons glue uniquely.
The same construction after any base change gives the pullback of this comparison.
For an arbitrary constant presentation e, read its normalization at one as chi. The
two resulting family comparisons agree at one, so uniqueness makes e the pullback
comparison followed by the pullback of chi. This argument uses no zero-fibre map.
Finite coefficients follow from lisse descent; integral coefficients follow from
compatible finite reductions, and rational and algebraically closed coefficients
from the specified scalar comparisons. -/
theorem native_family_constancy (Q : Pair D) (d : ℕ)
    [SmoothOfRelativeDimension d Q.g.left] :
    ∃ κ : Q.F ell hell E n hn Λ hcoeff ≅
        (moduleObjectDerivedPullback Λ
          (AffineSpace (ULift.{u} (Fin 1)) Q.B.left ↘ Q.B.left)).obj
            (Q.C ell hell E n hn Λ hcoeff),
      (moduleObjectDerivedPullback Λ
          (AffineSpace.oneSection (ULift.{u} (Fin 1)) Q.B.left)).mapIso κ ≪≫
        (NativeSectionPullback.sectionIso Λ _ _
          (AffineSpace.oneSection_comp_over _ Q.B.left)).app _ =
            fibreOne ell hell E n hn Λ hcoeff Q d ∧
      ∀ (B' : Over (Spec (.of D.k)))
        [LocallyOfFiniteType B'.hom] [QuasiCompact B'.hom] [IsSeparated B'.hom]
        (b : B' ⟶ Q.B)
        (C₀ : DerivedCategory
          (Mod (Sheaf (Scheme.ProEt.topology B'.left) Ab.{u + 1})
            (condensedRingObj Λ B'.left)))
        (e : (moduleObjectDerivedPullback Λ
            (AffineSpace.map (ULift.{u} (Fin 1)) b.left)).obj
              (Q.F ell hell E n hn Λ hcoeff) ≅
          (moduleObjectDerivedPullback Λ
            (AffineSpace (ULift.{u} (Fin 1)) B'.left ↘ B'.left)).obj C₀),
        ∃ χ : (moduleObjectDerivedPullback Λ b.left).obj
            (Q.C ell hell E n hn Λ hcoeff) ≅ C₀,
          e = (moduleObjectDerivedPullback Λ
              (AffineSpace.map (ULift.{u} (Fin 1)) b.left)).mapIso κ ≪≫
            ((NativeSectionPullback.compAlong Λ
              (AffineSpace.map (ULift.{u} (Fin 1)) b.left)
              (AffineSpace (ULift.{u} (Fin 1)) Q.B.left ↘ Q.B.left) _ rfl).app _).symm ≪≫
            (NativeSectionPullback.compAlong Λ
              (AffineSpace (ULift.{u} (Fin 1)) B'.left ↘ B'.left) b.left _
              (AffineSpace.map_over b.left).symm).app _ ≪≫
            (moduleObjectDerivedPullback Λ
              (AffineSpace (ULift.{u} (Fin 1)) B'.left ↘ B'.left)).mapIso χ := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

namespace AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

private theorem sectionRestrictionIso_eq_readingIso {B B' A A' : Scheme.{u}}
    (b : B' ⟶ B) (i : B ⟶ A) (i' : B' ⟶ A') (a' : A' ⟶ B') (f : A' ⟶ A)
    (hbi : b ≫ i = i' ≫ f) (hia : i' ≫ a' = 𝟙 B')
    (F : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology A) Ab.{u + 1})
      (condensedRingObj Λ A)))
    (C : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B) Ab.{u + 1})
      (condensedRingObj Λ B)))
    (C₀ : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology B') Ab.{u + 1})
      (condensedRingObj Λ B')))
    (θ : (moduleObjectDerivedPullback Λ i).obj F ≅ C)
    (e : (moduleObjectDerivedPullback Λ f).obj F ≅
      (moduleObjectDerivedPullback Λ a').obj C₀) :
    sectionRestrictionIso Λ b i i' a' f hbi hia F C C₀ θ e =
      NativeSectionPullback.readingIso Λ b f hbi.symm hia θ e := by
  have hc : (NativeSectionPullback.compAlong Λ i' f (i' ≫ f) rfl).hom.app F =
      (leftDerivedUpperStarComp Λ i' f).hom.app F := by
    simp only [NativeSectionPullback.compAlong]
  apply Iso.ext
  simp only [sectionRestrictionIso, moduleObjectDerivedPullback,
    NativeSectionPullback.readingIso, NativeSectionPullback.sectionIso,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Iso.app_hom, Iso.app_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, NatTrans.comp_app, eqToIso.hom]
  rw [NativeSectionPullback.compAlong_inv_app, hc,
    NativeSectionPullback.compAlong_inv_app]
  simp only [Category.assoc]

private theorem mapIso_injective_of_iso_id {C : Type*} [Category C]
    (F : C ⥤ C) (e : F ≅ 𝟭 C) {X Y : C} {α β : X ≅ Y}
    (h : F.mapIso α = F.mapIso β) : α = β := by
  have : F.Faithful := Functor.Faithful.of_iso e.symm
  exact F.mapIso_injective h

set_option maxHeartbeats 1000000 in
-- The native derived-category assembly uses the budget of its coherence theorems.
end AlgebraicGeometry.ProEtale.CondensedRing.DncInvariance
