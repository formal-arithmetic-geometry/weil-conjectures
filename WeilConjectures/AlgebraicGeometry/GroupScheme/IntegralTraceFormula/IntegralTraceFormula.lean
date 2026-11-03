/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AbelianVariety.TraceCoefficientMorphismFormula.TraceCoefficientMorphismFormula
public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.FreeParameterEvaluation.FreeParameterScalarMaps
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.GeometricPointFiniteness.GeometricPointCohomologyFiniteness
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.IntTensorProjection
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.AdmissibleTensorConstructibility
import WeilConjectures.AlgebraicGeometry.Condensed.CondensedCoefficientIsoConstructible
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralOpenImageProperFormulas
import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.LocalizingClosureCtfEqualsBc
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperLocalizingAdmissibleCoefficients
import WeilConjectures.AlgebraicGeometry.Rational.RationalOpenDirectImageConstructible
import WeilConjectures.CategoryTheory.RingObjects.Condensed.BaseCoefficientCondensedIdentification
import WeilConjectures.AlgebraicGeometry.Compactification.CompactificationOverField
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteOpenDirectImageCtf
import WeilConjectures.Compactification.Over
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
import Mathlib.CategoryTheory.Triangulated.Adjunction
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixFiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixNonfiniteGeneration
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixAdmissibleThickness
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixPerfectExtension
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Scalar.ScalarSixCtfGenerators
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
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
import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import WeilConjectures.SixFunctors.Etale.Derived.EtaleTorAmplitude
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import Mathlib.CategoryTheory.Triangulated.Subcategory
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
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CurrentCtfSixFunctorStability

/-! # Integral trace formula and its finite reductions

Source: literature/blueprint/latest/blueprint/part-duality-trace-formula/sec-trace-formula/
sec-tf-coefficient-transport/sk-prop-tf-transport-integral/_section.md
(blueprint: sk-prop-tf-transport-integral).

The coefficient objects, quotient maps and derived reductions are those of
`AdicCompletion`. Traces and operators are exactly the constructions used in the finite
coefficient formula. In particular the Frobenius coefficient morphism need not be invertible.
The reduction assertion identifies each individual local trace, as well as the global trace.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open WeilConjectures.TraceWeilComplex WeilConjectures.TraceCoefficientMorphismFormula

namespace WeilConjectures.IntegralTraceFormula

variable (D : FiniteFieldDatum.{u})
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

attribute [local instance] coefficientDerivedCategory

/-- Compactly supported scalar complex, using exactly the point realization of the finite
formula. Source: integral trace formula, left side (blueprint: sk-prop-tf-transport-integral). -/
abbrev compactComplex (O : TraceOperations.Given Λ (Spec (.of D.k)))
    (X₀ : Over (Spec (.of D.k₀))) [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [HasCompactification (D.geometricFiber X₀).hom]
    (K : TraceOperations.D Λ (D.geometricFiber X₀).left) :=
  (pointFibre D Λ).obj
    ((TraceOperations.Comparisons.compactlySupported O (D.geometricFiber X₀)).obj K)

/-- Scalar geometric stalk at the point indexed by `X₀(F_{q^m})`.
Source: integral trace formula, right side (blueprint: sk-prop-tf-transport-integral). -/
abbrev stalkComplex (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (K : TraceOperations.D Λ (D.geometricFiber X₀).left)
    (m : ℕ) (hm : 1 ≤ m) (x : D.extensionPoints X₀ m hm) :=
  (pointFibre D Λ).obj
    ((TraceOperations.star Λ (fixedGeometricPoint D X₀ m hm x).left).obj K)

/-- The categorical trace of the prescribed global Frobenius operator.
Source: formula (1), left side (blueprint: sk-prop-tf-transport-integral). -/
def globalTrace (O : TraceOperations.Given Λ (Spec (.of D.k)))
    (P : TraceOperations.GeometricOperations O) (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [HasCompactification (D.geometricFiber X₀).hom]
    (K : ConstantModelConstructibleFiniteTor Λ (D.geometricFiber X₀).left)
    (θ : FrobeniusCorrespondence D Λ X₀ K) (m : ℕ)
    (hc : _root_.DerivedCategory.IsPerfectRingComplex (compactComplex D Λ O X₀ K.obj)) :
    MonObj.Γ Λ :=
  _root_.DerivedCategory.perfectCategoricalTrace _ hc
    ((pointFibre D Λ).map (FrobeniusCorrespondence.operator D O P θ m))

/-- The categorical trace of the prescribed fixed-point stalk operator.
Source: formula (1), each summand (blueprint: sk-prop-tf-transport-integral). -/
def localTrace (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    (K : ConstantModelConstructibleFiniteTor Λ (D.geometricFiber X₀).left)
    (θ : FrobeniusCorrespondence D Λ X₀ K) (m : ℕ) (hm : 1 ≤ m)
    (x : D.extensionPoints X₀ m hm)
    (hx : _root_.DerivedCategory.IsPerfectRingComplex (stalkComplex D Λ X₀ K.obj m hm x)) :
    MonObj.Γ Λ :=
  _root_.DerivedCategory.perfectCategoricalTrace _ hx
    ((pointFibre D Λ).map
      ((FrobeniusCorrespondence.toWeilComplex D θ).stalkEndomorphism m
        (fixedGeometricPoint D X₀ m hm x) (fixedGeometricPoint_fixed D X₀ m hm x)))

/-- Extend a coefficient morphism across the canonical scalar/pullback isomorphism.
This coefficient-general helper keeps the derived adjunctions folded before specialization.
Source: proof paragraph 1, scalar comparison (blueprint: sk-prop-tf-transport-integral). -/
def scalarCoefficient
    (R S : Profinite.CondensedRing.{u}) [IsCommMonObj R.X] [IsCommMonObj S.X]
    (a : R.X ⟶ S.X) [IsMonHom a] {X : Scheme.{u}} (f : X ⟶ X)
    (K : TraceOperations.D R.X X) (θ : (TraceOperations.star R.X f).obj K ⟶ K) :
    (TraceOperations.star S.X f).obj
        ((Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K) ⟶
      (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.obj K :=
  letI := FreeParameterEvaluation.scalarPullComparison_isIso R S a f K
  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory S.X f).hom.app _ ≫
    inv (FreeParameterEvaluation.scalarPullComparison R S a f K) ≫
    (Mod.extendScalars (coefficientMap a X)).leftDerivedFunctor.map
      ((CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory R.X f).inv.app K ≫ θ)

variable (ℓ : ℕ) [Fact ℓ.Prime] (E : Type u) [Field E]
  [Algebra (Padic ℓ) E] [FiniteDimensional (Padic ℓ) E]

/-- Reduction of a Frobenius coefficient morphism: inverse of the canonical non-flat
scalar/pullback comparison followed by derived reduction of the original morphism.
The two outer comparisons identify exact termwise pullback with its total left derived
functor. Source: proof paragraph 1, definition of bar-theta_n
(blueprint: sk-prop-tf-transport-integral). -/
def reducedCoefficient (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    (K : TraceOperations.D (DerivedNakayama.integerRing ℓ E) (D.geometricFiber X₀).left)
    (θ : (TraceOperations.star (DerivedNakayama.integerRing ℓ E)
      (modelFrobenius D X₀).left).obj K ⟶ K) (n : ℕ) :
    (TraceOperations.star (DerivedNakayama.quotientRing ℓ E (n + 1))
      (modelFrobenius D X₀).left).obj
        ((AdicCompletion.derivedReduction ℓ E (D.geometricFiber X₀).left n).obj K) ⟶
      (AdicCompletion.derivedReduction ℓ E (D.geometricFiber X₀).left n).obj K :=
  scalarCoefficient (Mon.mk (DerivedNakayama.integerRing ℓ E))
    (Mon.mk (DerivedNakayama.quotientRing ℓ E (n + 1)))
    (DerivedNakayama.reductionRing ℓ E (n + 1)) (modelFrobenius D X₀).left K θ

/-- **Integral trace formula, including compatibility of its individual traces with every
positive uniformizer reduction.** The input is bounded constructible, with no extra Tor,
completeness, invertibility or lattice hypothesis. `n : ℕ` denotes exponent `n + 1`, the
indexing convention of the recorded normalized tower.

Source: latest blueprint sk-prop-tf-transport-integral, formula (1) and final sentence
(blueprint: sk-prop-tf-transport-integral).

Proof: integral_ctf_equals_bc gives finite Tor amplitude. Stability of the six operations
and sk-lem-finite give perfectness of compact cohomology and geometric stalks. Scalar-six
identifies their derived reductions with compact cohomology and stalks of the normalized
reductions, respecting the adjunction units, pullback compositors and composition defining
all Frobenius iterates and operators. Hence each reduced operator is the operator of
reducedCoefficient. Represent each perfect point complex by a bounded finite-projective
complex and its operator by a chain map. sk-p-trace identifies its categorical trace with
the alternating sum of the termwise traces. Reduction commutes with this finite sum and
with finite-projective trace, giving the asserted global and individual local reduction
identities. Apply sk-thm-tf-coefficient-morphism-formula at each positive level. The point
set is finite, so the integral global trace minus the sum of local traces vanishes modulo
every uniformizer power. Separatedness of the complete valuation ring makes it zero. -/
theorem integral_traceFormula (hℓ : ℓ ≠ D.p)
    (O : TraceOperations.Given (DerivedNakayama.integerRing ℓ E) (Spec (.of D.k)))
    (P : TraceOperations.GeometricOperations O)
    (On : ∀ n : ℕ, TraceOperations.Given (DerivedNakayama.quotientRing ℓ E (n + 1))
      (Spec (.of D.k)))
    (Pn : ∀ n : ℕ, TraceOperations.GeometricOperations (On n))
    (X₀ : Over (Spec (.of D.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [HasCompactification (D.geometricFiber X₀).hom]
    (K : TraceOperations.D (DerivedNakayama.integerRing ℓ E) (D.geometricFiber X₀).left)
    (hK : constantModelBoundedConstructible (DerivedNakayama.integerRing ℓ E)
      (D.geometricFiber X₀).left K)
    (θ : (TraceOperations.star (DerivedNakayama.integerRing ℓ E)
      (modelFrobenius D X₀).left).obj K ⟶ K) (m : ℕ) (hm : 1 ≤ m) :
    ∃ htor : _root_.DerivedCategory.finiteTorAmplitude _ K,
    ∃ hc : _root_.DerivedCategory.IsPerfectRingComplex
        (compactComplex D (DerivedNakayama.integerRing ℓ E) O X₀ K),
    ∃ hx : ∀ x : D.extensionPoints X₀ m hm, _root_.DerivedCategory.IsPerfectRingComplex
        (stalkComplex D (DerivedNakayama.integerRing ℓ E) X₀ K m hm x),
      globalTrace D (DerivedNakayama.integerRing ℓ E) O P X₀ ⟨K, hK, htor⟩ θ m hc =
        ∑ᶠ x : D.extensionPoints X₀ m hm,
          localTrace D (DerivedNakayama.integerRing ℓ E) X₀ ⟨K, hK, htor⟩ θ m hm x (hx x) ∧
      ∀ n : ℕ,
        ∃ hn : (constantModelBoundedConstructible (DerivedNakayama.quotientRing ℓ E (n + 1))
          (D.geometricFiber X₀).left ⊓ _root_.DerivedCategory.finiteTorAmplitude _)
          ((AdicCompletion.derivedReduction ℓ E (D.geometricFiber X₀).left n).obj K),
        ∃ hcn : _root_.DerivedCategory.IsPerfectRingComplex
          (compactComplex D (DerivedNakayama.quotientRing ℓ E (n + 1)) (On n) X₀
            ((AdicCompletion.derivedReduction ℓ E (D.geometricFiber X₀).left n).obj K)),
        ∃ hxn : ∀ x : D.extensionPoints X₀ m hm, _root_.DerivedCategory.IsPerfectRingComplex
          (stalkComplex D (DerivedNakayama.quotientRing ℓ E (n + 1)) X₀
            ((AdicCompletion.derivedReduction ℓ E (D.geometricFiber X₀).left n).obj K) m hm x),
          CoefficientMorphismTraceFormula D (DerivedNakayama.quotientRing ℓ E (n + 1))
            (On n) (Pn n) X₀
            ⟨(AdicCompletion.derivedReduction ℓ E (D.geometricFiber X₀).left n).obj K, hn⟩
            (reducedCoefficient D ℓ E X₀ K θ n) m hm ∧
          MonObj.Γ.map (DerivedNakayama.reductionRing ℓ E (n + 1))
            (globalTrace D (DerivedNakayama.integerRing ℓ E) O P X₀ ⟨K, hK, htor⟩ θ m hc) =
            globalTrace D (DerivedNakayama.quotientRing ℓ E (n + 1)) (On n) (Pn n) X₀
              ⟨(AdicCompletion.derivedReduction ℓ E (D.geometricFiber X₀).left n).obj K, hn⟩
              (reducedCoefficient D ℓ E X₀ K θ n) m hcn ∧
          ∀ x : D.extensionPoints X₀ m hm,
            MonObj.Γ.map (DerivedNakayama.reductionRing ℓ E (n + 1))
              (localTrace D (DerivedNakayama.integerRing ℓ E) X₀
                ⟨K, hK, htor⟩ θ m hm x (hx x)) =
              localTrace D (DerivedNakayama.quotientRing ℓ E (n + 1)) X₀
                ⟨(AdicCompletion.derivedReduction ℓ E (D.geometricFiber X₀).left n).obj K, hn⟩
                (reducedCoefficient D ℓ E X₀ K θ n) m hm x (hxn x) := by
  sorry

end WeilConjectures.IntegralTraceFormula
