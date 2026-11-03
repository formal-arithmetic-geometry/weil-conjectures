/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
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

public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralCoefficientExtComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDefinitions
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficientTwistsSupplement
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixDerivedPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixImmersionComparison
public import WeilConjectures.AlgebraicGeometry.BaseFieldFiniteCD.FiniteCohomologicalDimensionHypothesis
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedCoefficientMaps
public import WeilConjectures.AlgebraicGeometry.RootCoordinateFace.RootTowerCoordinateFace
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.FieldTensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
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
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
public import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
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
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafClosedLocalization
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafBaseChangeMates
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Adjunction
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorHom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedSixOperations
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCondensedCoefficients
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportCoefficientChange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenClosedSequenceRingSheaf
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.Extension
public import WeilConjectures.NumberTheory.Padics.IntegersShrinkModPow
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteSupportReduction.CondensedCompactSupportReductionCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.FiniteSupportReduction.CondensedCompactSupportReductionIdentity
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixCtf
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison

/-! # Finite condensed compact-support reduction transitions

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-tower/
lem-coef-integral-compact-support.md and its proof, final paragraph.
(blueprint: lem-coef-compact-support-normalized-realization).

All categories are ordinary uncompleted condensed module derived categories. The finite
extension is presented as a finite subfield of the fixed algebraic closure. Coordinate n
means exponent n+1, so every positive quotient occurs. The existing positive-quotient
construction is reused; its name `completedResidue` denotes a plain ring quotient.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.FiniteSupportReduction

variable (ell : ℕ) [Fact ell.Prime] (E : PadicAlgCl.FiniteIntermediateField ell)
  (π : PadicAlgCl.integers ell E)

/-- Bundle the existing positive quotient as a commutative condensed ring.
Source: blueprint finite coefficients; def-pod-positive-quotient-coefficients.
(blueprint: lem-coef-compact-support-normalized-realization). -/
abbrev ring (n : ℕ) : ScalarSixRing.{u} :=
  ⟨Profinite.continuousMapRingObj (completedResidue ell E π n)⟩

/-- Bundle the existing integral reduction of continuous functions.
Source: blueprint finite coefficients; def-pod-positive-quotient-coefficients.
(blueprint: lem-coef-compact-support-normalized-realization). -/
def reduction (n : ℕ) : latticeIntegralRing.{u} ell E ⟶ ring.{u} ell E π n :=
  ⟨⟨(sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (completedReduction ell E π n)⟩⟩

/-- The actual quotient A_(m+1) to A_(n+1), applied to continuous functions.
Source: blueprint finite quotient maps; Ideal.Quotient.factorPow.
(blueprint: lem-coef-compact-support-normalized-realization). -/
def quotient {m n : ℕ} (h : n ≤ m) : ring.{u} ell E π m ⟶ ring.{u} ell E π n :=
  ⟨⟨(sheafCompose (coherentTopology Profinite.{u})
    (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
      (Profinite.continuousMapRingSheafMap
        (Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.add_le_add_right h 1))
        ((QuotientRing.isOpenQuotientMap_mk ((Ideal.span {π}) ^ (m + 1))).isQuotientMap
          |>.continuous_iff.mpr continuous_quot_mk))⟩⟩

/-- The canonical quotient identities needed for typed scalar transports.
Source: blueprint quotient maps and their associativity, proof step 1.
(blueprint: lem-coef-compact-support-normalized-realization).

Proof: Evaluate on a profinite set and on a continuous function. Quotient induction
reduces each equation to the identity on the integers of E. For the first equation use
Ideal.Quotient.factor_eq, for the second use factor_comp, and for the third use
factor_comp_mk. Postcomposition and passage to the underlying ring objects preserve
these equations. These are equations of the specified maps, not chosen comparisons. -/
theorem coefficientLaws :
    (∀ n : ℕ, quotient.{u} ell E π (le_refl n) = 𝟙 (ring.{u} ell E π n)) ∧
    (∀ (r m n : ℕ) (hrm : m ≤ r) (hmn : n ≤ m),
      quotient.{u} ell E π hrm ≫ quotient.{u} ell E π hmn = quotient.{u} ell E π (hmn.trans hrm)) ∧
    (∀ (m n : ℕ) (h : n ≤ m),
      reduction.{u} ell E π m ≫ quotient.{u} ell E π h = reduction.{u} ell E π n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    apply CommMon.hom_ext
    change (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map _ = 𝟙 _
    simp only [Ideal.Quotient.factorPow, Ideal.Quotient.factor_eq,
      Profinite.continuousMapRingSheafMap_id]
    exact (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map_id _
  · intro r m n hrm hmn
    apply CommMon.hom_ext
    change (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map _ ≫
      (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map _ = _
    rw [← Functor.map_comp, ← Profinite.continuousMapRingSheafMap_comp]
    congr 2
    exact Ideal.Quotient.factor_comp _ _
  · intro m n h
    apply CommMon.hom_ext
    change (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map _ ≫
      (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map _ =
      (sheafCompose (coherentTopology Profinite.{u})
        (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (completedReduction ell E π n)
    unfold completedReduction
    rw [← Functor.map_comp, ← Profinite.continuousMapRingSheafMap_comp]
    congr 2

end AlgebraicGeometry.ProEtale.CondensedRing.FiniteSupportReduction

namespace AlgebraicGeometry.ProEtale.CondensedRing.FiniteSupportReduction

/-- Finite quotient maps are listed scalar changes. -/
private theorem quotientListed (D : WeilConjectures.FiniteFieldDatum.{u})
    (_hell : ell ≠ D.p)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E))
    {m n : ℕ} (h : n ≤ m) :
    IsListedScalarCoefficientMap ell (quotient.{u} ell E π h) := by
  letI := PadicAlgCl.normedFieldOfAlgebra ell E.1
  let : ProperSpace E.1 := FiniteDimensional.proper (Padic ell) E.1
  let : CompactSpace (PadicAlgCl.integers ell E.1) := by
    rw [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ,
      Subtype.range_coe_subtype]
    let he : (PadicAlgCl.integers ell E.1 : Set E.1) = Metric.closedBall 0 1 := by
      ext x
      change x ∈ PadicAlgCl.integers ell E.1 ↔ _
      rw [PadicAlgCl.mem_integers_iff, Metric.mem_closedBall, dist_zero_right]
      rfl
    change IsCompact (PadicAlgCl.integers ell E.1 : Set E.1)
    rw [he]
    exact isCompact_closedBall (0 : E.1) 1
  letI : Finite (completedResidue ell E π m) := by
    unfold completedResidue
    rw [hπ]
    letI : Finite (IsLocalRing.ResidueField (PadicAlgCl.integers ell E.1)) :=
      PadicAlgCl.finite_residueField_integers ell E.1
    exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) (m + 1)
  letI : Finite (completedResidue ell E π n) := by
    unfold completedResidue
    rw [hπ]
    letI : Finite (IsLocalRing.ResidueField (PadicAlgCl.integers ell E.1)) :=
      PadicAlgCl.finite_residueField_integers ell E.1
    exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) (n + 1)
  letI : DiscreteTopology (completedResidue ell E π m) :=
    QuotientAddGroup.discreteTopology (by
      apply (IsLocalRing.isOpen_iff_finite_quotient (I :=
        (Ideal.span {π}) ^ (m + 1))).mpr
      infer_instance)
  letI : DiscreteTopology (completedResidue ell E π n) :=
    QuotientAddGroup.discreteTopology (by
      apply (IsLocalRing.isOpen_iff_finite_quotient (I :=
        (Ideal.span {π}) ^ (n + 1))).mpr
      infer_instance)
  have hm : (ell : completedResidue ell E π m) ^ (m + 1) = 0 := by
    have hl : (ell : PadicAlgCl.integers ell E) ∈ Ideal.span {π} := by
      rw [hπ]
      exact PadicAlgCl.natCast_mem_maximalIdeal_integers ell E.1
    have hq := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hl (m + 1))
    simpa only [map_pow, map_natCast] using hq

  have hn : (ell : completedResidue ell E π n) ^ (n + 1) = 0 := by
    have hl : (ell : PadicAlgCl.integers ell E) ∈ Ideal.span {π} := by
      rw [hπ]
      exact PadicAlgCl.natCast_mem_maximalIdeal_integers ell E.1
    have hq := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hl (n + 1))
    simpa only [map_pow, map_natCast] using hq
  change IsListedScalarCoefficientMap ell (scalarSixContinuousMap
    (Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.add_le_add_right h 1))
      continuous_of_discreteTopology)
  exact IsListedScalarCoefficientMap.finite (m + 1) (n + 1) hm hn
      (Ideal.Quotient.factorPow (Ideal.span {π}) (Nat.add_le_add_right h 1))
        continuous_of_discreteTopology

/-- Integral quotient maps are listed scalar changes. -/
private theorem reductionListed (D : WeilConjectures.FiniteFieldDatum.{u})
    (_hell : ell ≠ D.p)
    (hπ : Ideal.span {π} = IsLocalRing.maximalIdeal (PadicAlgCl.integers ell E))
    (n : ℕ) : IsListedScalarCoefficientMap ell (reduction.{u} ell E π n) := by
  letI := PadicAlgCl.normedFieldOfAlgebra ell E.1
  let : ProperSpace E.1 := FiniteDimensional.proper (Padic ell) E.1
  let : CompactSpace (PadicAlgCl.integers ell E.1) := by
    rw [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ,
      Subtype.range_coe_subtype]
    have he : (PadicAlgCl.integers ell E.1 : Set E.1) = Metric.closedBall 0 1 := by
      ext x
      change x ∈ PadicAlgCl.integers ell E.1 ↔ _
      rw [PadicAlgCl.mem_integers_iff, Metric.mem_closedBall, dist_zero_right]
      rfl
    change IsCompact (PadicAlgCl.integers ell E.1 : Set E.1)
    rw [he]
    exact isCompact_closedBall (0 : E.1) 1
  letI : Finite (completedResidue ell E π n) := by
    unfold completedResidue
    rw [hπ]
    letI : Finite (IsLocalRing.ResidueField (PadicAlgCl.integers ell E.1)) :=
      PadicAlgCl.finite_residueField_integers ell E.1
    exact Ideal.finite_quotient_pow (IsNoetherian.noetherian _) (n + 1)
  letI : DiscreteTopology (completedResidue ell E π n) :=
    QuotientAddGroup.discreteTopology (by
      apply (IsLocalRing.isOpen_iff_finite_quotient (I :=
        (Ideal.span {π}) ^ (n + 1))).mpr
      infer_instance)
  have hn : (ell : completedResidue ell E π n) ^ (n + 1) = 0 := by
    have hl : (ell : PadicAlgCl.integers ell E) ∈ Ideal.span {π} := by
      rw [hπ]
      exact PadicAlgCl.natCast_mem_maximalIdeal_integers ell E.1
    have hq := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hl (n + 1))
    simpa only [map_pow, map_natCast] using hq
  simpa [reduction, scalarSixContinuousMap, completedReduction,
    latticeIntegralRing, ring] using
    (IsListedScalarCoefficientMap.integralFinite E (n + 1) hn
      (Ideal.Quotient.mk _) continuous_quot_mk)

end AlgebraicGeometry.ProEtale.CondensedRing.FiniteSupportReduction
