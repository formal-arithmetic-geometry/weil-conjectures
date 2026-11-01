/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComposition
public import WeilConjectures.AlgebraicGeometry.SepFinType
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SmoothPurity.AdmissibleCondensedCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence
public import WeilConjectures.Compactification.Triangle
public import WeilConjectures.CategoryTheory.Adjunction.ExchangeMate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperLowerShriek
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
public import WeilConjectures.Compactification.NagataCompactification
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.AlgebraicGeometry.Open.OpenImmersionLocalizing
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteDirectImageComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.Compactification.CommonDenseRefinement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperImageLocalizingProper
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteProperBaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperBaseChange
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchangeTriangulated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ProperBaseChange.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedCoefficientIsoExchange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeAdmissibleGenerators
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientProperFormulaTools
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Monoidal.Mon
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.Algebra.Homology.ScalarPullback.KFlatScalarComparisonNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarRestrictionMateNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficientsMate
public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientExchangeComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushIntegralDerivedIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.AmbientQcqsExchangeCanonicalShifts
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.LocalizingIsoLocus
public import WeilConjectures.Compactification.BaseChange
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compact.CompactSupportRefinementBaseChange
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.CategoryTheory.RingedDerivedComparisons.RingedDerivedMonoidalComparisons
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedSupportProjectionFormula
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedClosedSupportAdjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralDerivedCoefficientData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralConstantModelLocalResolution
public import WeilConjectures.ProperBaseChange.IntegralLfpLocallyFreeResolution
public import WeilConjectures.ProperBaseChange.CondensedConstructibleSerre
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocallyClosedGeneratorTensorIntersection
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison
public import WeilConjectures.AlgebraicGeometry.CondensedLocallyClosedExtensionTower
public import WeilConjectures.AlgebraicGeometry.CondensedOpenClosedRecollement

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import Mathlib.Topology.Defs.Filter
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicConstantLocalModelTor
public import WeilConjectures.AlgebraicGeometry.InternalModuleAbEquivalence
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteDiscreteCondensedRing
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.AlgebraicGeometry.Sites.QuasiCompact
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitudeMapDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntegralLisseDerivedAux
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalLeftDerived
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientProjectionSquare
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientsFiniteFree
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.QlbarDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.IntegralFiniteScalar.FiniteFreeScalarDerivedComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteScalarProjectionCase
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarMateProjection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralFinitePointResolution
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionData.LocallyClosedExtensionCoherence
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.AlgebraicGeometry.ProEtale.Tate.ProEtaleTateTwists
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.DetSfCompBaseChangeDefs
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import WeilConjectures.Algebra.Homology.ScalarPullback.KFlatScalarComparisonNormalization
import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionData.LocallyClosedExtensionCoherence
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixNormalizedImmersion
import WeilConjectures.CategoryTheory.SixFunctors.MateIsoAlongEquivalences
import WeilConjectures.AlgebraicGeometry.PurityTransport.SmoothDatum.TransportGeometricOperations
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportCompact
import WeilConjectures.Compactification.BoundaryRefinement
import WeilConjectures.Mathlib.CategoryTheory.Functor.SquareTransport
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportScalarCompatibility
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportGeometry
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceTower
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
import WeilConjectures.AlgebraicGeometry.PurityTransport.Coefficient.TransportCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteCoefficientEncodingDataSupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteDiscreteRestrictionEncodingSupplement
import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportRoot
import WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionDataSupplement
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportUnits
import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonConstantGenerator
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
import WeilConjectures.AlgebraicGeometry.Affine.Trace.AffineTraceConstruction
import Mathlib.CategoryTheory.Sites.LocalProperties

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportComparisonDefinitions

/-! # Compact-support, exceptional and coefficient comparisons on native condensed categories

Source: blueprint latest, sk-thm-sbc-coefficients/fix-lem-exchanges, clauses 1, 2, 4;
sk-prop-scalar-six; sk-prop-sp-composition; sk-prop-sp-purity-bc
(blueprint: lem-pur-condensed-operation-comparisons).

The full subcategories are the published bounded constructible finite-Tor categories of
ordinary derived internal modules over the coefficient ring pulled from the condensed point.
The selected composition and exchange maps are fixed by the dependency's refinement and
proper/open normalization equations. Selecting them does not choose arbitrary isomorphisms.
Right adjoints are quantified together with their adjunctions; their conjugates and exceptional
exchange maps below are actual adjunction constructions.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing
namespace OperationComparisons

/-- Exactly the four coefficient stages in the statement, invariant under coefficient
isomorphism. The finite quotient uses the recorded uniformizer and the discrete topology.
Source: opening coefficient convention (blueprint: lem-pur-condensed-operation-comparisons). -/
def IsCoefficient (ell : ℕ) [Fact ell.Prime] (Λ : ScalarSixRing.{u}) : Prop :=
  (∃ (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ), 1 ≤ n ∧
    Nonempty (Mon.mk Λ.X ≅ Mon.mk
      (cartesianFinitePointRing (ULift.{u} (Padic.coefficientExtensionRing ell E.1 n))))) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ell,
    Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicIntegersRingObj ell E.1))) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ell,
    Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.continuousMapRingObj E.1))) ∨
  Nonempty (Mon.mk Λ.X ≅ Mon.mk (Profinite.padicAlgClRingObj ell))

variable {k : Type u} [Field k] {Λ : ScalarSixRing.{u}}

/-- The fully faithful inclusion of the existing Dctf category in its ambient derived category.
Source: full-subcategory convention (blueprint: lem-pur-condensed-operation-comparisons). -/
abbrev inclusion (Γ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    ConstantModelConstructibleFiniteTor Γ.X X ⥤
      DerivedCategory (ModuleRingedComparison.internalModules Γ.X X) :=
  ObjectProperty.ι _

/-- The canonical inclusion of Dctf in its localizing closure, with unchanged objects and maps.
Source: composition theorem, restriction to C
(blueprint: lem-pur-condensed-operation-comparisons). -/
def toLocalizing (Γ : ScalarSixRing.{u}) (X : Scheme.{u}) :
    ConstantModelConstructibleFiniteTor Γ.X X ⥤
      (localizingClosureProEtale Γ.X X).FullSubcategory :=
  ObjectProperty.ιOfLE (fun K hK _P _hP hS ↦ hS K hK)

/-- Geometric comparison data with its five mate and purity laws.

The construction first applies the normalized compact-support existence result to each
coefficient stage, using its coherent composition data and right-adjoint witnesses.  The
mate-counit identity is `CategoryTheory.mateEquiv_counit`; applying it to the selected
composition and identity comparisons gives `composition_counit` and `exchange_identity`.
Applying the same identity twice and using the pasted-square equation in the coherent data
gives `exchange_pasting`.  The condensed purity-base-change proposition supplies the
invertibility of the exceptional mate for smooth maps, and its counit equation is exactly
`exceptional_counit`.  Restricting all maps along the fully faithful inclusions preserves
these equalities and produces the five fields.  Source: clauses 1--6 of the
operation-comparison argument (blueprint: lem-pur-condensed-operation-comparisons). -/
theorem geometricWitness_exists (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hne : ell ≠ D.p) :
    ∃ S : Data D ell, GeometricWitness S := by
  sorry

/-- The native condensed compact-support comparisons, their conjugate and exceptional counit
identities, smooth exceptional invertibility, and the scalar/exchange rectangle with its
composition and pasting coherences. The base datum retains q = p^a, a >= 1 and the specified
algebraic closure. Every coefficient stage retains the finite-subextension-valued convention.
All base arrows in the equations are arbitrary underlying scheme maps; in particular the
same maps and equations apply to compatible semilinear isomorphisms.

Source: latest blueprint fix-lem-exchanges, clauses 1, 2, 4, with sk-prop-scalar-six,
sk-prop-sp-composition and sk-prop-sp-purity-bc
(blueprint: lem-pur-condensed-operation-comparisons).

Proof plan, the ten steps of the node:
1. Use sk-thm-existence on Dctf, then restrict sk-thm-sf-comp-composition. Its normalization
   fixes alpha and B, and supplies independence, naturality, associativity, units and the
   stacked-square composition/exchange law even for base maps not over k.
2. Compose the adjunctions for f and g. Conjugate alpha using the gf adjunction and the
   composite adjunction (def-weil-pbc-composite-adjunction, def-weil-pbc-adjunction-conjugate).
   The mate-counit identity gives composition_counit; conjugation and mate pasting give its
   units and associativity (lem-amb-mate-unit-counit, lem-weil-pbc-mate-pasting).
3. On a compactification, B is proper exchange followed by proper image of the inverse
   open mate (def-sfb-compact-support-base-change-maps). Proper and open mate pasting, with
   prop-sfb-module-left-derived-upper-star-comp and internal-module transport, gives their
   identity and successive-base-change equations without flatness assumptions.
4. Substitute these two formulas in B. Naturality moves the middle open map through proper
   exchange, giving exchange_pasting. Independence identifies arbitrary models. The same
   expansion respects alpha. Identity models give exchange_identity.
5. Transpose inverse B using the specified adjunctions. The mate-counit identity followed
   by cancellation of B inverse with B is exceptional_counit; no assertion that an arbitrary
   mate preserves isomorphisms is used.
6. For smooth f of pure relative dimension use prop-pur-condensed-purity-base-change.
   For varying relative dimension use its open loci, provided by
   sbc-lem-smooth-relative-dimension-locally-constant. They remain finite type since the
   standing schemes are Noetherian (lem-weil-pbc-finite-type-over-noetherian). Composition
   conjugation and exchange pasting identify the restricted exceptional maps. The pure
   case and dimension-zero purity make these restrictions invertible. Apply
   lem-sfb-sheaf-cover-local-isomorphism to every cohomology of the cone, obtaining zero
   cone and smooth_exceptional, including the empty scheme.
7. The scalar open comparison is normalized by inverse theta
   (lem-sfb-scalar-six-normalized-immersion). Restrict the mixed scalar/open rectangle to
   the open: both paths are the same scalar/pullback comparison by
   lem-sfb-scalar-pullback-square-coherence. Faithfulness of locally closed extension and
   internal-module transport proves the rectangle before restriction.
8. For the proper factor apply lem-sfb-scalar-geometric-exchange-rectangle to the specified
   unit/pullback/counit scalar mate. Identify its lambda with inverse theta using
   lem-sfb-scalar-six-derived-pullback-normalization and
   lem-sfb-kflat-scalar-comparison-normalization. Paste with step 7 and apply proper image.
   The specified resulting maps are scalarCompactSupportMap and B, giving scalar_exchange.
   The coefficient hypotheses ensure scalar preservation and scalar_isIso; finite
   cohomological dimension of D.k follows from its being an algebraic closure.
9. Paste two copies of scalar_exchange and cancel their shared edges. Pullback-compositor
   and theta coherence gives scalar_exchange_pasting and the outer-square equation.
   Scalar compact-support composition and the composition/exchange law for B identify the
   stacked-square pasting with alpha; scalar_composition records this same b coherence.
10. For compatible semilinear isomorphisms use their actual pro-etale pullbacks and the
   coefficient identifications from the point (sk-prop-sfb-cartesian-coefficients). They
   are inverse equivalences. Apply lem-weil-mate-iso-along-equivalences to inverse B to get
   the same invertibility assertion; steps 2--5 and 7--9 apply to these scheme maps. -/
theorem condensedOperationComparisons (D : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hne : ell ≠ D.p) :
    ∃ S : Data D ell, Laws S := by
  obtain ⟨S, hg1, hg2, hg3, hg4, hg5⟩ := geometricWitness_exists D ell _hne
  obtain ⟨hs1, hs2, hs3, hs4⟩ := scalarWitness_of_geometric D ell _hne S
    ⟨hg1, hg2, hg3, hg4, hg5⟩
  exact ⟨S, Laws.mk hg1 hg2 hg3 hg4 hg5 hs1 hs2 hs3 hs4⟩

variable {D : WeilConjectures.FiniteFieldDatum.{u}} {ell : ℕ} [Fact ell.Prime]

end OperationComparisons
end AlgebraicGeometry.ProEtale.CondensedRing
