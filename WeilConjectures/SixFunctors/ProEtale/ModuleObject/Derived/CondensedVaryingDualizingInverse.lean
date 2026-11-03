/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.IntegralModelsEmbedded.IntegralModelsEmbedded
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
import WeilConjectures.Compactification.Defs
import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.KrullDimension
import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.NumberTheory.Padics.ExtensionIntegersDvr
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.NumberTheory.Padics.PadicNumbers
import WeilConjectures.AlgebraicGeometry.ProEtale.Clopen.ProEtaleClopenRingedModuleGluing
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.AlgebraicGeometry.FiniteClopenTensor.ProEtaleFiniteClopenTensorCalculus
import WeilConjectures.AlgebraicGeometry.Finite.Constant.FiniteConstantLocalModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Mate.MateOpenRestriction
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeTensorComparison
import WeilConjectures.AlgebraicGeometry.Integral.Models.IntegralModelsStacksBlueprint
import WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import WeilConjectures.AlgebraicGeometry.ProEtaleIntegralCoefficientLimit
import WeilConjectures.SixFunctors.Supporting.RoosIntrinsicCompletenessEquivalence
import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.SmoothPurity.IntegralOnSlice.DerivedCompleteOnSlices
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.SmoothPurity.Finite.FiniteTorAmplitudeSites
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
import WeilConjectures.SmoothPurity.IntegralOnSlice.IntegralDerivedOperationsOnSlices
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.SixFunctors.Supporting.ConstantCompletionEquivalence
import WeilConjectures.AlgebraicGeometry.AdicResidueLissePerfectLift
import WeilConjectures.SixFunctors.AdicPerfectModelCompleteReduction
import WeilConjectures.RingTheory.PseudoCoherentBoundedFiniteFreeModel
import WeilConjectures.RingTheory.MinimalFreeModel
import WeilConjectures.AlgebraicGeometry.SiteRestrictionExact
import WeilConjectures.Algebra.Homology.LineEvaluation.LineEvaluationInversePair
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorClosed
import WeilConjectures.CategoryTheory.SixFunctors.OrdinaryModuleDerivedInternalHom
import WeilConjectures.Algebra.Homology.LineUnbounded.LineUnboundedDerivedTensor
import WeilConjectures.AlgebraicGeometry.ProEtaleLisseOrigin
import WeilConjectures.SixFunctors.Integral.IntegralLineTensorComparisonDefinitions
import WeilConjectures.SixFunctors.Integral.IntegralLineTensorComparisonIso
import WeilConjectures.SixFunctors.Integral.IntegralLineTensorComparisonRepresentative
import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
import WeilConjectures.SixFunctors.Constructible.ConstructibleTensorCompletion
import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonPresentationSupplement
import WeilConjectures.AlgebraicGeometry.Finite.Comparison.FiniteComparisonLocalizing
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.Etale.Derived.Stability.OpenImmersion
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleOrigin
import WeilConjectures.AlgebraicGeometry.Flat.FlatModelGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleLisseModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixFiniteEtaleExtensionIso
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartLocallyClosedExtension
import Mathlib.CategoryTheory.Triangulated.Generators
import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel
import WeilConjectures.ConstructibleSheaf.OpenClosed
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartStratificationDefs
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeartSheafConeWitness
import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantModelLocalResolution
import WeilConjectures.ProperBaseChange.IntegralLfpLocallyFreeResolution
import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement

import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
import Mathlib.Topology.Defs.Filter
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
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
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
import Mathlib.CategoryTheory.Triangulated.Subcategory
import Mathlib.CategoryTheory.ObjectProperty.Shift
import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
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
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import WeilConjectures.CategoryTheory.CompactGeneratorsBuildObjects
import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.AlgebraicGeometry.Finite.Ring.FiniteRingEtaleCompactGenerators
import Mathlib.Algebra.CharP.CharAndCard
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Formal.FormalClosedSupportDerived
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.DiagonalTowerCoefficients
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimit
import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerTrace
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1Triangle
import WeilConjectures.AlgebraicGeometry.RationalP1.RationalP1UnitCounit
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafClosedLocalization
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafBaseChangeMates
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars

/-! # Tensor inverse of the native smooth dualizing object

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-geometry/
def-pur-section-invariant.md, final invertibility assertion, and
sk-thm-dnc/thm-pur-cohomological-smoothness.md, invertibility clause
(blueprint: lem-pur-condensed-varying-dualizing-inverse).

All objects are ordinary derived internal modules over the pulled-back condensed ring.
The coefficient presentation allows exactly the fixed positive quotient, its integer ring,
its finite coefficient field, and the finite-subextension-valued algebraic closure.
The base-field typing facts and coefficient-unit membership are asserted, rather than assumed.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry Scheme AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- The native exceptional image of the coefficient unit has a two-sided Dctf inverse,
without a section, pure global dimension or Tate orientation.

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-geometry/
def-pur-section-invariant.md, final invertibility assertion; thm-pur-cohomological-smoothness,
invertibility clause (blueprint: lem-pur-condensed-varying-dualizing-inverse).

Proof, following the ten steps of the DAG:
1. By sbc-lem-smooth-relative-dimension-locally-constant, the fibre-dimension loci are
clopen and disjoint. Quasi-compactness gives finitely many nonempty loci, possibly none.
2. Each restricted map is smooth of pure dimension and stays separated and finite type,
by open restriction, the closed-immersion and finite-type permanence lemmas. Apply
lem-pur-finite-setting-comparison-hypotheses on these components.
3. Apply lem-pur-clopen-ringed-module-gluing and
lem-pur-finite-product-derived-tensor-calculus to the actual coefficient ring sheaf.
The internal/section tensor comparison identifies their tensors and K-flat tests.
The equivalence detects constructibility and all cohomological and Tor bounds; take
finite minima and maxima to obtain common bounds.
4. The coefficient unit has the constant rank-one local model and Tor interval [0,0].
The base field has ell-cohomological dimension zero. The right adjoint from
sk-thm-existence preserves Dctf, and det-sf-mate-open-restriction identifies its component
values with the component exceptional images of the coefficient unit.
5. At each finite quotient, thm-asd-smooth-tensor gives an etale rank-one line shifted
by twice the dimension. The counit-compatible lem-pur-finite-native-tensor-comparison
identifies this with the actual native exceptional value, including at the residue field.
6. At integral coefficients, lem-sfb-internal-integral-criterion-forward gives completeness.
Transport along the internal/section equivalence and the coefficient-ring limit isomorphism
of det-prop-sfb-qlbar-colimit-x-integral-limit. The Roos completeness equivalence identifies
this with the intrinsic completeness required by the residue-line theorem.
7. det-prop-scalar-six-exceptional identifies the residue of this same exceptional unit
with its residue-field exceptional value. Apply lem-pur-complete-residue-line-inverse:
the native integral object is a shifted pro-etale rank-one line.
8. The same scalar-six theorem for the integer-to-field and field-to-closure maps gives
the ordinary derived scalar extensions. A line is flat and K-flat in degree zero by
lem-pur-line-unbounded-derived-tensor, so these are shifted native lines as well.
9. In each case the dual line with the opposite shift gives the two evaluations, by
lem-pur-line-unbounded-derived-tensor and the internal/section tensor comparison.
Its constant rank-one local model and the opposite Tor interval give native Dctf membership.
10. Reassemble the component inverses with the finite-product equivalence. Full faithfulness
lifts both evaluation maps and their inverses, and faithfulness checks the identities.
When the source is empty this is the empty product: its unique object is both zero and
the coefficient unit, and its unique maps are the required isomorphisms. -/
theorem condensed_varying_dualizing_inverse
    (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D.p)
    (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ) (_hn : 1 ≤ n)
    (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj Λ] [IsCommMonObj Λ]
    (_hcoeff :
      Nonempty (Mon.mk Λ ≅ Mon.mk (IntegralModelsEmbedded.discreteObj
        (Padic.coefficientExtensionRing ell E n))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E)) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell)))
    (B V : Over (Spec (.of D.k)))
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType V.hom] [QuasiCompact V.hom] [IsSeparated V.hom]
    (g : V ⟶ B) [Smooth g.left] [IsSeparated g.left]
    [LocallyOfFiniteType g.left] [QuasiCompact g.left] :
    ∃ (hp : Fact (ringChar D.k).Prime) (hd : Fact (ringChar D.k ≠ ell))
      (hcd : BaseFieldFiniteCD ell D.k) (ha : IsLocalizingAdmissibleCoefficient ell Λ)
      (U : ConstantModelConstructibleFiniteTor Λ B.left),
      U.obj = 𝟙_ _ ∧
      ∃ P : ConstantModelConstructibleFiniteTor Λ V.left,
        Nonempty
          (((derivedTensor Λ V.left).obj
            ((@ctfExceptionalInverseImage Λ _ _ ell _ D.k _ hp hd hcd
              V B _ _ _ _ _ _ g ha).obj U).obj).obj P.obj ≅ 𝟙_ _) ∧
        Nonempty
          (((derivedTensor Λ V.left).obj P.obj).obj
            ((@ctfExceptionalInverseImage Λ _ _ ell _ D.k _ hp hd hcd
              V B _ _ _ _ _ _ g ha).obj U).obj ≅ 𝟙_ _) := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
