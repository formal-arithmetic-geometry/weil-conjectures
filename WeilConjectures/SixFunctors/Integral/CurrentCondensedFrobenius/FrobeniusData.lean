/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.StrictWeilCondensed.StrictWeilCondensed
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ModelSemilinearComparison.CondensedModelFrobeniusOperatorsBase
public import WeilConjectures.SixFunctors.SfIdentificationData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Current.CurrentDerivedPoincarePairing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Current.SfIdentificationStatementData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Current.CurrentGlobalVerdierDuality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.ScalarOpenCompositorCoherence
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestrictionMaps
import WeilConjectures.Compactification.BaseChange
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingEtaleCompactGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTowerCoefficients
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTrace
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1Triangle
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement
import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedCtfSixFunctorStabilityCurrent
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixHomTensorShiftCancellation
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Current.SfIdentificationStatementData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Current.SfIdentificationStatementData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Current.IdentificationPointCupShift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Current.IdentificationProjectionCupShift
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.IsoId
import WeilConjectures.AlgebraicGeometry.PurityTransport.SmoothDualizingAllCoefficients
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.Monoidal.Closed.InvertibleDualizing
import Mathlib.CategoryTheory.Shift.Adjunction
import Mathlib.Algebra.Group.Int.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeTateLineInvertible2
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.NativeSitePerfectDual
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import Mathlib.Algebra.Ring.Shrink
import WeilConjectures.Compactification.BoundaryPreparation
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LocalizingCompactificationCoherence
import WeilConjectures.AlgebraicGeometry.SmoothPurity.DimensionExtension
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import Mathlib.Algebra.Ring.Shrink
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteConstructibleEncoding
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedDirectImageBoundedBelow
import WeilConjectures.SixFunctors.Etale.Derived.DirectImageAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.AlgebraicGeometry.Open.OpenExtensionConstantModelConstructible
import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
import WeilConjectures.AlgebraicGeometry.ProEtale.SepClosedPointLift
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapGlobalSections
import WeilConjectures.WeilObject.Sheaf.Stalk
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.SepClosedPoint
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ConstructibleNakayama
import WeilConjectures.AlgebraicGeometry.Integral.IntegralPositiveReductionConstructible
import WeilConjectures.AlgebraicGeometry.Constructible.ConstructibleFiniteHeart
import WeilConjectures.AlgebraicGeometry.Integral.Residue.IntegralResidueCriterion
import WeilConjectures.AlgebraicGeometry.Integral.IntegralDirectImageLimits
import WeilConjectures.AlgebraicGeometry.Integral.IntegralDirectImageReductionCone
import WeilConjectures.CategoryTheory.DerivedCategory.CoproductsOfHomologyProperty
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficientData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
import WeilConjectures.AlgebraicGeometry.ProEtaleModuleConstructibleExtensionByZero
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
import WeilConjectures.AlgebraicGeometry.ContinuousIntegralCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorCategory.Complete
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.CategoryTheory.ModuleObjects.Monoidal
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import WeilConjectures.ConstructibleSheaf.FreeLifting
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralStratum
import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralGluing
import WeilConjectures.AlgebraicGeometry.CondensedFinitePresentationDescent
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointIntegralCoefficientIso
import WeilConjectures.AlgebraicGeometry.Integral.IntegralContinuousEncodingConstructible
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.SixFunctors.Integral.ScalarCompositionPairing
import WeilConjectures.SixFunctors.Coefficient.CoefficientDuality
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.NoetherianPseudoCoherentCohomologyCriterion
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.PerfectCohomologyAssembly
import WeilConjectures.RingTheory.DiscreteValuationRing.QuotientDuality
import WeilConjectures.CategoryTheory.DerivedCategory.Perfect.Dualizable
import WeilConjectures.CategoryTheory.ObjectProperty.Duality
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.SimpleModule.InjectiveProjective
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedScalarRealization
import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
import Mathlib.Algebra.Module.Shrink
import Mathlib.Topology.Category.Profinite.EffectiveEpi
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.AlgebraicGeometry.Native.NativeHomSourceShiftData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportCompact
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.Algebra.Polynomial.Roots
public import WeilConjectures.SixFunctors.Etale.Derived.OrientationDatum
public import WeilConjectures.AlgebraicGeometry.FiniteRingProperEtaleAdjoint
public import WeilConjectures.Compactification.BoundaryRefinement
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportComparisonUnit
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExactOfUniverses
import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
import WeilConjectures.CategoryTheory.Ringed.Site.RingedSiteKInjectiveResolutionsMixedUniverses
import WeilConjectures.CategoryTheory.SmoothPurity.QuasiIsoHomComplexMapMixedUniverses
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.SmoothPurity.CondensedOrdinaryCompactSections
import WeilConjectures.ProEtaleCoefficients.DerivedNakayamaResolution
import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
import WeilConjectures.PoincareDuality.Abstract
import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import Mathlib.Topology.KrullDimension
import Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.ConstructibleDirectImage
import WeilConjectures.SmoothPurity.Point.PointSectionsScalarExtension

import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointScalarRealization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointScalarRings
import Mathlib.Algebra.Field.ULift
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedOrdinaryCompactCohomology
import WeilConjectures.CategoryTheory.DerivedCategory.Bounded.BoundedHeartAmplitude
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Algebra.Module.Projective
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructibleStratum
import WeilConjectures.PoincareDuality.VerdierBiduality
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FinitePointSectionsExact

/-! # Canonical data for condensed Frobenius duality

Source: latest blueprint, sec-poincare-duality/sk-thm-frobenius/_section.md (statement)
and sk-thm-frobenius.proof.md (both proof paragraphs)
(blueprint: def-pod-current-frobenius-coordinates).

All returns below are the pullback-square mates followed by the given strict
Weil isomorphism. In particular the dual return uses `StrictWeilCondensed.dualDatum`,
not an independently supplied endomorphism. The pairing is the current recorded
`Current.derivedPoincarePairing`, in arbitrary admissible coefficient coordinates.
The untwisted pairing is written in every Tate frame pulled back from the
geometric point. These scalar formulas express the line-valued formula in
Lambda(-d), independently of a choice of frame.

## Main declarations

* `ordinaryReturn`, `compactScalarReturn`: the specified semilinear cohomology returns.
* `coefficientTateDatum`, `pulledFrame`: canonical Tate structures in coefficient coordinates.
* `onDegree`: the induced scalar cohomology operator.
* `FieldConsequences`: the pairing-normalized adjoint, spectrum and determinant clauses.

-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory MonoidalClosed
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.CondensedRing
open AlgebraicGeometry.ProEtale.PurityTransport
open scoped CategoryTheory.Obj

namespace WeilConjectures.SixFunctors.CurrentCondensedFrobenius

open ModelSemilinearComparison
open WeilConjectures

/-- Residue-field invertibility follows from ell different from the finite-field
characteristic. Source: standing setting (blueprint: def-pod-current-frobenius-coordinates). -/
abbrev primeInvertible (ell : ℕ) [Fact ell.Prime]
    (D : FiniteFieldDatum.{u}) (hEll : ell ≠ D.p)
    (X : Over (Spec (.of D.k))) (x : X.left) :
    Invertible (ell : X.left.residueField x) :=
  (by simpa only [map_natCast] using
    (PurityTransport.primeUnit D ell hEll).map (X.hom.residueFieldAlgebraMap x) :
    IsUnit (ell : X.left.residueField x)).invertible

/-- Ordinary scalar sections of the canonical semilinear return. The first map
is point reparametrization, the second the pullback-square mate, and the last
is the direct image of the supplied Weil structure.
Source: cohomology F (blueprint: def-pod-current-frobenius-coordinates). -/
def ordinaryReturn
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (D : FiniteFieldDatum.{u})
    {X : Scheme.{u}} (a : X ⟶ Spec (.of D.k))
    (g : X ≅ X) (w : g.hom ≫ a = a ≫ (StrictWeilCondensed.pointFrobenius D).hom)
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (phi : (StrictWeilCondensed.action Λ g).obj K ⟶ K) :=
  letI : IsAlgClosed D.k := IsAlgClosure.isAlgClosed D.k₀
  (CohomologyTransport.sections Λ (Spec (.of D.k))).mapDerivedCategory.map
    ((pointReparametrization Λ (StrictWeilCondensed.pointFrobenius D).hom).inv.app _ ≫
      (properExchange Λ a g.hom (StrictWeilCondensed.pointFrobenius D).hom w).app K ≫
      (lowerStar Λ a).rightDerivedFunctor.map phi)

/-- Compact scalar sections of the canonical proper/open return in a model
compactification. Source: cohomology F (blueprint: def-pod-current-frobenius-coordinates). -/
def compactScalarReturn
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ] (D : FiniteFieldDatum.{u})
    {X : Scheme.{u}} {a : X ⟶ Spec (.of D.k)} (cf : Compactification a)
    (g : X ≅ X) (gz : cf.Z ≅ cf.Z)
    (wj : g.hom ≫ cf.i = cf.i ≫ gz.hom)
    (wp : gz.hom ≫ cf.g = cf.g ≫ (StrictWeilCondensed.pointFrobenius D).hom)
    {K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))}
    (phi : (StrictWeilCondensed.action Λ g).obj K ⟶ K) :=
  (CohomologyTransport.sections Λ (Spec (.of D.k))).mapDerivedCategory.map
    (compactReturn Λ cf.i cf.g g.hom gz.hom
      (StrictWeilCondensed.pointFrobenius D).hom wj wp phi)

/-- Pull a point frame to X through the specified Cartesian Tate comparison,
then transport it along the coefficient isomorphism. This expresses the
Lambda(-d)-valued pairing in any constant Tate frame, without changing it.
Source: removing the twist (blueprint: def-pod-current-frobenius-coordinates). -/
def pulledFrame (ell : ℕ) [Fact ell.Prime] (D : FiniteFieldDatum.{u})
    (hEll : ell ≠ D.p) (Λ : ScalarSixRing.{u}) (c : Coefficient ell)
    (ec : c.bundled.{u} ell ≅ Λ) (X : Over (Spec (.of D.k)))
    (d : ℕ) (e : c.line ell (Spec (.of D.k)) d ≅ 𝟙_ _) :
    smoothTraceCoefficientLine ell Λ c ec X.left d ≅
      𝟙_ (DerivedCategory (Mod (Sheaf (ProEt.topology X.left) Ab.{u + 1})
        (condensedRingObj Λ.X X.left))) :=
  letI := scalarSixChangeMonoidal ec.hom X.left
  letI := primeInvertible ell D hEll X
  letI := primeInvertible ell D hEll (Over.mk (𝟙 (Spec (.of D.k))))
  let p := Classical.choice (linePullCoordinates_nonempty ell c X.hom)
  (scalarSixChange ec.hom X.left).mapIso
    ((DerivedCategory.singleFunctor _ 0).mapIso
      ((p.power d).symm ≪≫ (upperStar (c.obj ell) X.hom).mapIso e ≪≫
        (Functor.Monoidal.εIso (upperStar (c.obj ell) X.hom)).symm) ≪≫
          DerivedCategory.singleFunctorObjUnitIso _) ≪≫
    (Functor.Monoidal.εIso (scalarSixChange ec.hom X.left)).symm

/-- Cohomology as Hom from the regular unit to a shift of the scalar complex.
Source: induced cohomology Frobenius (blueprint: def-pod-current-frobenius-coordinates). -/
def onDegree {R : Type (u + 1)} [CommRing R]
    {P : DerivedCategory (ModuleCat.{u + 1} R)} (F : End P) (i : ℤ) :
    (𝟙_ _ ⟶ P⟦i⟧) →ₗ[R] (𝟙_ _ ⟶ P⟦i⟧) :=
  Linear.rightComp R _ ((shiftFunctor _ i).map F)

set_option maxHeartbeats 1600000 in
-- Elaborating the original scalar/cohomology coordinates needs the full instance context.
/-- The complete field clause for the specified untwisted pairing. The adjoint
is fixed by the degreewise value of that pairing; its conjugacy equation is the
inverse-transpose assertion. Root multiset equality retains algebraic multiplicities
in every algebraically closed extension. Finiteness, invertibility, equal dimensions
and the determinant identity are conclusions, including dimension zero.
Source: entire final paragraph (blueprint: def-pod-current-frobenius-coordinates). -/
def FieldConsequences {R : Type (u + 1)} [CommRing R]
    {P Q : DerivedCategory (ModuleCat.{u + 1} R)} (b : P ⊗ Q ⟶ 𝟙_ _)
    (A : End P) (B : End Q) (q d : ℕ) : Prop :=
  ∀ hR : IsField R,
    letI : Field R := hR.toField
    ∀ i : ℤ,
      ∃ hP : Module.Finite R (𝟙_ _ ⟶ P⟦i⟧),
      ∃ hQ : Module.Finite R (𝟙_ _ ⟶ Q⟦-i⟧),
        letI := hP
        letI := hQ
        (∃ a : (𝟙_ _ ⟶ P⟦i⟧) ≃ₗ[R] (𝟙_ _ ⟶ P⟦i⟧),
          a.toLinearMap = onDegree A i ∧
          ∃ adj : (𝟙_ _ ⟶ Q⟦-i⟧) ≃ₗ[R] Module.Dual R (𝟙_ _ ⟶ P⟦i⟧),
            (∀ x y, adj y x = identificationScalarValue
              (identificationDegreeValue b i x y)) ∧
            ∀ y, adj (onDegree B (-i) y) =
              (q : R) ^ d • a.symm.toLinearMap.dualMap (adj y)) ∧
        Module.finrank R (𝟙_ _ ⟶ P⟦i⟧) = Module.finrank R (𝟙_ _ ⟶ Q⟦-i⟧) ∧
        (LinearMap.det (onDegree A i) * LinearMap.det (onDegree B (-i)) =
          (q : R) ^ (d * Module.finrank R (𝟙_ _ ⟶ P⟦i⟧))) ∧
        ∀ (Ω : Type (max (u + 1) v)) [Field Ω] [IsAlgClosed Ω] (j : R →+* Ω),
          ((onDegree B (-i)).charpoly.map j).roots =
            (((onDegree A i).charpoly.map j).roots.map (fun α ↦ (q : Ω) ^ d / α))

end WeilConjectures.SixFunctors.CurrentCondensedFrobenius
