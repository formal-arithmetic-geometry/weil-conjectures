/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactSupportComposition.CondensedCompactSupportCompositionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ScalarSixTensorComparison
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
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.AlgebraicGeometry.Condensed.CondensedConstantConstructibilitySupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import WeilConjectures.CategoryTheory.ProEtaleCoefficients.LocalizingAdmissibleCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingExceptionalAdjoint
public import WeilConjectures.AlgebraicGeometry.ConstantModelTorAmplitude
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenImmersionTensorProjection
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.ClosedImmersionTensorProjection
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedLocalizingPullback
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationLocalizing
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerStarComp
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
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyPerfectScalarModel
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
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
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ListedScalarCoefficientMaps
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.CategoryTheory.ObjectProperty.Shift
public import WeilConjectures.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
public import WeilConjectures.AlgebraicGeometry.Coefficient.CoefficientHeart
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationCoherenceCocycle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProEtaleProperOpenInterchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleOperationsSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import Mathlib.CategoryTheory.Adjunction.CompositionIso
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionLowerShriek
public import WeilConjectures.AlgebraicGeometry.LocallyClosedExtensionData.LocallyClosedExtensionCoherence
public import WeilConjectures.CategoryTheory.AdjunctionSquareComposition
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarGeometricExchangeRectangle
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Compactification.CompactificationRefinementLocalizing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Open.OpenExtensionConstructibleFiniteTor
public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenCoefficientRefinement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Finite.FiniteCoefficientSmallCarrierComparison
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.LocalizingLowerShriekCompositionModel
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalization
public import WeilConjectures.PoincareDuality.ProjectionFormula
public import Mathlib.Tactic.DefEqTransformations
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalScalarPullbackNormalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ModuleObjectProjectionMap
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorLeftFlatComputation
public import WeilConjectures.AlgebraicGeometry.QuotientTensorFlatModel.QuotientTensorRightFlatComputation
public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientScalarTensorCanonical
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PullIsoMonoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.AlgebraicGeometry.QuotientChange.ScalarPullbackSquareCoherence
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalPullNormalizationExistence
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
public import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import WeilConjectures.Algebra.Homology.SixFunctors.OrdinaryDerivedChangeOfRings
public import WeilConjectures.AlgebraicGeometry.QuotientChange.InternalDerivedScalarComparisons
public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Scalar.DiagonalScalarPullbackComparison
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactificationReindexing.CondensedCompactificationReindexing
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedFiniteTorConstructible
public import WeilConjectures.SmoothPurity.CondensedWeilTensor.CondensedWeilTensorProduct
public import WeilConjectures.SmoothPurity.WeilSheafComplex
public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactProjectionFormula
public import WeilConjectures.SmoothPurity.ProjectionFormulaCoherence
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ConstructibleIntrinsic
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.Compactification.Defs
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CondensedProperOpenInterchange

public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleOrigin
import WeilConjectures.SmoothPurity.Supporting.ProjectionFiniteReduction
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalOriginCompactSupportComposition

/-! # Compact-support projection formula at every coefficient stage

Source: latest blueprint
part-duality-trace-formula/sec-poincare-duality/
sec-perfect-complexes-on-the-point-and-two-exchange-formulas/sk-thm-sf-tensor-hom/
sk-rem-sf-pf-done/
fix-prop-projection-formula.md and its six-step proof
(blueprint: fix-prop-projection-formula).

The finite clause retains the constant-coefficient etale and pro-etale realization.
The higher clauses use ordinary modules over pulled-back condensed rings. The comparison
system carries its proper/open and refinement normalizations, so the equations refer to
specified maps. The assertion predicates below only collect clauses of this node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing.AllCoefficientProjection

open CompactSupportComposition CompactificationReindexing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Canonical proper compact-support/direct-image identification, using the identity
open immersion. Source: latest blueprint, proper coincidence clause
(blueprint: fix-prop-projection-formula). -/
def properSupportComparison {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f] :
    F Λ (Compactification.ofIsProper f) ≅ R Λ f :=
  Functor.isoWhiskerRight (derivedOpenImmersionLowerShriekId Λ X) (R Λ f) ≪≫
    Functor.leftUnitor (R Λ f)

/-- Exactly the isomorphism, naturality, compactification and composition clauses.
The first conjunct includes every bounded constructible K in the comparison domain;
there is no finite-Tor assumption on K. L alone is in Dctf. The comparison system's
laws include its normalized compositor, both units and the associativity pentagon.
Source: latest blueprint fix-prop-projection-formula, displayed formula and coherences
(blueprint: fix-prop-projection-formula). -/
def GeometricAssertions (k : Type u) [Field k] (H : CoherentData Λ k) : Prop :=
  (∀ (X : SepFinType k) (K : BoundedConstructible (condensedRingObj Λ X.obj.left)),
    localizingClosureProEtale Λ X.obj.left K.obj) ∧
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left)
      (K : BoundedConstructible (condensedRingObj Λ X.obj.left))
      (L : CondensedConstructibleFiniteTor Λ Y.obj.left),
    boundedConstructible (condensedRingObj Λ X.obj.left)
      (K.obj ⊗ (P Λ f.hom.left).obj L.obj) ∧
    boundedConstructible (condensedRingObj Λ Y.obj.left) ((F Λ c).obj K.obj ⊗ L.obj) ∧
    boundedConstructible (condensedRingObj Λ Y.obj.left)
      ((F Λ c).obj (K.obj ⊗ (P Λ f.hom.left).obj L.obj)) ∧
    IsIso (pf Λ c K.obj L.obj)) ∧
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left)
      (K K' : BoundedConstructible (condensedRingObj Λ X.obj.left))
      (L L' : CondensedConstructibleFiniteTor Λ Y.obj.left) (a : K ⟶ K') (b : L ⟶ L'),
    ((F Λ c).map a.hom ⊗ₘ b.hom) ≫ pf Λ c K'.obj L'.obj =
      pf Λ c K.obj L.obj ≫ (F Λ c).map (a.hom ⊗ₘ (P Λ f.hom.left).map b.hom)) ∧
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) (c d : Compactification f.hom.left)
      (K : BoundedConstructible (condensedRingObj Λ X.obj.left))
      (L : CondensedConstructibleFiniteTor Λ Y.obj.left)
      (hK : localizingClosureProEtale Λ X.obj.left K.obj)
      (hT : localizingClosureProEtale Λ X.obj.left
        (K.obj ⊗ (P Λ f.hom.left).obj L.obj)),
    ((H.comparison f c d).hom.app ⟨K.obj, hK⟩ ▷ L.obj) ≫ pf Λ d K.obj L.obj =
      pf Λ c K.obj L.obj ≫
        (H.comparison f c d).hom.app ⟨K.obj ⊗ (P Λ f.hom.left).obj L.obj, hT⟩) ∧
  (∀ {X Y Z : SepFinType k} (f : X ⟶ Y) (g : Y ⟶ Z)
      (c : Compactification f.hom.left) (d : Compactification g.hom.left)
      (e : Compactification (f.hom.left ≫ g.hom.left))
      (K : BoundedConstructible (condensedRingObj Λ X.obj.left))
      (L : CondensedConstructibleFiniteTor Λ Z.obj.left)
      (hK : localizingClosureProEtale Λ X.obj.left K.obj)
      (hT : localizingClosureProEtale Λ X.obj.left
        (K.obj ⊗ (P Λ f.hom.left).obj ((P Λ g.hom.left).obj L.obj))),
    ((H.comp f g c d e).hom.app ⟨K.obj, hK⟩ ▷ L.obj) ≫ pf Λ e K.obj L.obj =
      pf Λ d ((F Λ c).obj K.obj) L.obj ≫
        (F Λ d).map (pf Λ c K.obj ((P Λ g.hom.left).obj L.obj)) ≫
        (H.comp f g c d e).hom.app
          ⟨K.obj ⊗ (P Λ f.hom.left).obj ((P Λ g.hom.left).obj L.obj), hT⟩ ≫
        (F Λ e).map
          (K.obj ◁ (leftDerivedUpperStarComp Λ f.hom.left g.hom.left).inv.app L.obj)) ∧
  (∀ {X Y : SepFinType k} (f : X ⟶ Y) [IsProper f.hom.left]
      (K : BoundedConstructible (condensedRingObj Λ X.obj.left))
      (L : CondensedConstructibleFiniteTor Λ Y.obj.left),
    pf Λ (Compactification.ofIsProper f.hom.left) K.obj L.obj ≫
      (properSupportComparison Λ f.hom.left).hom.app
        (K.obj ⊗ (P Λ f.hom.left).obj L.obj) =
      ((properSupportComparison Λ f.hom.left).hom.app K.obj ▷ L.obj) ≫
        properProjectionMorphism Λ f.hom.left K.obj L.obj)

/-- All higher coefficients satisfy the specified geometric projection assertions.
Source: latest blueprint fix-prop-projection-formula, higher coefficient clauses
(blueprint: fix-prop-projection-formula).

Proof: (1) choose etale-origin representatives at finite level using
lem-sf-proetale-constructible-origin and sk-cor-pe-finite-tor-comparison, and apply
lem-weil-finite-compact-projection-formula, with finite Tor only on L.
(2) prop-sf-pf-reduction identifies the reductions of the specified maps.
(3) thm-sf-pf-adic reconstructs the integral map, and thm-sf-pf-field transports it
by localization and scalar extension. (4) thm-sf-pf-proetale identifies the maps
on the pro-etale site. (5) prop-sf-pf-coherence, sk-prop-sf-pf-coherence and the
composition theorem give the normalized comparisons, naturality, composition,
pentagon and proper coincidence; lem-integral-ctf-equals-bc puts all higher
bounded constructible inputs in their comparison domains. (6) lem-fix-weil-operations
and def-wf-tensor-product give the additional Weil clause stated below.
-/
theorem higher (D₀ : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D₀.p)
    (_hcoeff : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicIntegersRingObj ell E))) ∨
      (∃ E : PadicAlgCl.FiniteIntermediateField ell,
        Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) :
    ∃ H : CoherentData Λ D₀.k, GeometricAssertions Λ D₀.k H := by
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing.AllCoefficientProjection

namespace AlgebraicGeometry.ProEtale.CondensedRing.AllCoefficientProjection

open CompactSupportComposition CompactificationReindexing

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- Compact-support Frobenius is the normalized exchange followed by the image
of the input Frobenius. The exact/derived identifications only change presentation.
Source: latest blueprint fix-prop-projection-formula, Weil-compatibility clause
(blueprint: fix-prop-projection-formula). -/
def imagePair {k : Type u} [Field k] (H : CoherentData Λ k)
    {X Y : SepFinType k} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (a : Aut X.obj.left) (b : Aut Y.obj.left)
    (sq : IsPullback a.hom f.hom.left f.hom.left b.hom)
    (K : CategoryTheory.Endofunctor.IsoAlgebra (upperStar Λ a.hom).mapDerivedCategory)
    (hK : localizingClosureProEtale Λ X.obj.left K.carrier) :
    CategoryTheory.Endofunctor.IsoAlgebra (upperStar Λ b.hom).mapDerivedCategory :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk ((F Λ c).obj K.carrier)
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ b.hom).symm.app _ ≪≫
      (H.exchange sq c c).app ⟨K.carrier, hK⟩ ≪≫
        (F Λ c).mapIso ((leftDerivedUpperStarIsoMapDerivedCategory Λ a.hom).app _ ≪≫ K.str))

/-- Pullback Frobenius is the inverse canonical square comparison followed by
pullback of the input Frobenius, transported to the exact-functor convention.
Source: latest blueprint fix-prop-projection-formula, Weil-compatibility clause
(blueprint: fix-prop-projection-formula). -/
def pullPair {X Y : Scheme.{u}} (f : X ⟶ Y) (a : Aut X) (b : Aut Y)
    (sq : IsPullback a.hom f f b.hom)
    (L : CategoryTheory.Endofunctor.IsoAlgebra (upperStar Λ b.hom).mapDerivedCategory) :
    CategoryTheory.Endofunctor.IsoAlgebra (upperStar Λ a.hom).mapDerivedCategory :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk ((P Λ f).obj L.carrier)
    ((leftDerivedUpperStarIsoMapDerivedCategory Λ a.hom).symm.app _ ≪≫
      (pullbackSquareComparison Λ sq.toCommSq).symm.app L.carrier ≪≫
        (P Λ f).mapIso ((leftDerivedUpperStarIsoMapDerivedCategory Λ b.hom).app _ ≪≫ L.str))

/-- The recorded tensor Frobenius bundled with its actual ambient tensor carrier.
Source: latest blueprint fix-prop-projection-formula, prescribed tensor Frobenius
(blueprint: fix-prop-projection-formula). -/
def tensorPair {X : Scheme.{u}} (g : X ⟶ X)
    (K L : CategoryTheory.Endofunctor.IsoAlgebra (upperStar Λ g).mapDerivedCategory) :
    CategoryTheory.Endofunctor.IsoAlgebra (upperStar Λ g).mapDerivedCategory :=
  CategoryTheory.Endofunctor.IsoAlgebra.mk (K.carrier ⊗ L.carrier)
    (WeilConjectures.CondensedWeilTensor.frobenius Λ g K L)

/-- The existing geometric fibre bundled as a separated finite-type object.
Its three structure properties are the existing Mathlib base-change instances for
its second projection; no additional hypothesis on the fibre is imposed.
Source: latest blueprint fix-prop-projection-formula, finite-field scheme setting
(blueprint: fix-prop-projection-formula). -/
def geometricObject (D₀ : WeilConjectures.FiniteFieldDatum.{u})
    (X₀ : Over (Spec (.of D₀.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom] :
    SepFinType D₀.k :=
  ⟨D₀.geometricFiber X₀,
    inferInstanceAs (LocallyOfFiniteType (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k))))),
    inferInstanceAs (QuasiCompact (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k))))),
    inferInstanceAs (IsSeparated (pullback.snd X₀.hom
      (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k)))))⟩

/-- The base change of a finite-field morphism, bundled in the existing category
of separated finite-type schemes. Source: latest blueprint, Weil clause
(blueprint: fix-prop-projection-formula). -/
abbrev geometricMap (D₀ : WeilConjectures.FiniteFieldDatum.{u})
    {X₀ Y₀ : Over (Spec (.of D₀.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) :
    geometricObject D₀ X₀ ⟶ geometricObject D₀ Y₀ :=
  ObjectProperty.homMk
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D₀.k₀ D₀.k)))).map f₀)

/-- Equivariance for geometric Frobenius, expressed as the morphism equation
between the two specified Weil pairs. Actual derived Weil complexes are included
through condensedWeilRealization; strict pairs are also allowed by the definition.
Membership of every constructible carrier in the comparison domain is part of
GeometricAssertions, so the two domain witnesses exclude no input.
Source: latest blueprint fix-prop-projection-formula, Weil clause
(blueprint: fix-prop-projection-formula). -/
def WeilAssertions (D₀ : WeilConjectures.FiniteFieldDatum.{u})
    (H : CoherentData Λ D₀.k) : Prop :=
  ∀ (X₀ Y₀ : Over (Spec (.of D₀.k₀)))
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom] [IsSeparated X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom] [IsSeparated Y₀.hom]
    (f₀ : X₀ ⟶ Y₀),
    ∀ (sq : IsPullback (D₀.geometricFrobenius X₀).hom (geometricMap D₀ f₀).hom.left (geometricMap
        D₀ f₀).hom.left (D₀.geometricFrobenius Y₀).hom)
      (c : Compactification (geometricMap D₀ f₀).hom.left)
      (K : WeilConjectures.condensedStrictWeilComplex Λ (D₀.geometricFrobenius X₀).hom)
      (L : WeilConjectures.condensedStrictWeilComplex Λ (D₀.geometricFrobenius Y₀).hom)
      (_hL : _root_.DerivedCategory.finiteTorAmplitude _ L.obj.carrier)
      (hK : localizingClosureProEtale Λ (geometricObject D₀ X₀).obj.left
        K.obj.carrier)
      (hT : localizingClosureProEtale Λ (geometricObject D₀ X₀).obj.left
        (K.obj.carrier ⊗ (P Λ (geometricMap D₀ f₀).hom.left).obj L.obj.carrier)),
      (upperStar Λ (D₀.geometricFrobenius Y₀).hom).mapDerivedCategory.map (pf Λ c K.obj.carrier
        L.obj.carrier) ≫
          (imagePair Λ H (geometricMap D₀ f₀) c (D₀.geometricFrobenius X₀) (D₀.geometricFrobenius
        Y₀) sq
            (tensorPair Λ (D₀.geometricFrobenius X₀).hom K.obj (pullPair Λ (geometricMap D₀
        f₀).hom.left (D₀.geometricFrobenius X₀) (D₀.geometricFrobenius Y₀) sq L.obj)) hT).str.hom =
        (tensorPair Λ (D₀.geometricFrobenius Y₀).hom (imagePair Λ H (geometricMap D₀ f₀) c
        (D₀.geometricFrobenius X₀) (D₀.geometricFrobenius Y₀) sq K.obj hK) L.obj).str.hom ≫
          pf Λ c K.obj.carrier L.obj.carrier

/-- The geometric assertion and its Weil clause hold for both field coefficients.
Source: latest blueprint fix-prop-projection-formula, last two sentences
(blueprint: fix-prop-projection-formula).

Proof: steps 1--5 are the finite, reduction, adic, field, site-comparison and
coherence argument recorded in higher. Step 6 applies lem-fix-weil-operations
to the same proper-counit/open projection. Its Frobenius exchange is normalized
by the proper/open mates and common refinements; def-wf-tensor-product supplies
the tensor Frobenius on both endpoints. Thus the projection satisfies exactly
the displayed Weil morphism equation. No purity or biduality is used.
-/
theorem fieldsWithWeil (D₀ : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D₀.p)
    (_hcoeff : (∃ E : PadicAlgCl.FiniteIntermediateField ell,
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
      Nonempty (Mon.mk Λ ≅ Mon.mk (Profinite.padicAlgClRingObj ell))) :
    ∃ H : CoherentData Λ D₀.k, GeometricAssertions Λ D₀.k H ∧ WeilAssertions Λ D₀ H := by
  sorry

/-- The four coefficient stages in this node, allowing a ring-object presentation
isomorphism. The finite stage is a positive-power quotient, not an arbitrary finite ring.
Source: latest blueprint, coefficient list
(blueprint: fix-prop-projection-formula). -/
def IsCoefficientStage (ell : ℕ) [Fact ell.Prime] (A : ScalarSixRing.{u}) : Prop :=
  (∃ (E : PadicAlgCl.FiniteIntermediateField ell) (n : ℕ), 1 ≤ n ∧
    Nonempty (Mon.mk A.X ≅ Mon.mk
      (cartesianFinitePointRing (ULift.{u} (Padic.coefficientExtensionRing ell E n))))) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ell,
    Nonempty (Mon.mk A.X ≅ Mon.mk (Profinite.padicIntegersRingObj ell E))) ∨
  (∃ E : PadicAlgCl.FiniteIntermediateField ell,
    Nonempty (Mon.mk A.X ≅ Mon.mk (Profinite.continuousMapRingObj E))) ∨
  Nonempty (Mon.mk A.X ≅ Mon.mk (Profinite.padicAlgClRingObj ell))

end AlgebraicGeometry.ProEtale.CondensedRing.AllCoefficientProjection

namespace AlgebraicGeometry.Etale.AllCoefficientProjection

variable (D₀ : WeilConjectures.FiniteFieldDatum.{u}) (ell : ℕ) [Fact ell.Prime]
    (hell : ell ≠ D₀.p) (E : Type (u + 1)) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) [Fact (1 ≤ n)]

/-- Finite-coefficient isomorphism on every etale-origin pro-etale realization,
with naturality, compactification comparison, finite-Tor reduction and proper
coincidence for its specified constant-coefficient map. K has no Tor hypothesis.
The native finite composition and pentagon equations are stated separately below.
Source: latest blueprint fix-prop-projection-formula, finite and reduction clauses
(blueprint: fix-prop-projection-formula).

Proof: step 1 chooses etale-origin representatives using
lem-sf-proetale-constructible-origin and sk-cor-pe-finite-tor-comparison and applies
lem-weil-finite-compact-projection-formula. Step 2 is prop-sf-pf-reduction, at the
ideal pi^m A_E,n in particular. Step 5 is prop-sf-pf-coherence transported by the
specified site realization. Its naturality, refinement and proper equations are
exactly those of the canonical etale projection used by step 1.
-/
theorem finite
    {X Y : Scheme.{u}}
    [X.Over (Spec (.of D₀.k))] [Y.Over (Spec (.of D₀.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D₀.k))] [QuasiCompact (X ↘ Spec (.of D₀.k))]
    [LocallyOfFiniteType (Y ↘ Spec (.of D₀.k))] [QuasiCompact (Y ↘ Spec (.of D₀.k))]
    (f : X ⟶ Y) [f.IsOver (Spec (.of D₀.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (c : Compactification f)
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing ell E n) X) (L :
        DerivedCategoryModule (Padic.coefficientExtensionRing ell E n) Y)
    (hK : DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing ell E n) X K)
    (hL : DerivedCategory.isBoundedConstructible (Padic.coefficientExtensionRing ell E n) Y L)
    (hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn (Padic.coefficientExtensionRing ell E n)
        Y a b L) :
    (type_of% (isIso_finiteCompactProjection D₀ ell hell E n f c K L hK hL hTor)) ∧
    (∀ (K' : DerivedCategoryModule (Padic.coefficientExtensionRing ell E n) X) (L' :
        DerivedCategoryModule (Padic.coefficientExtensionRing ell E n) Y)
      (a : K ⟶ K') (b : L ⟶ L'),
      type_of% (WeilConjectures.sixFunctorProjection_naturality (Padic.coefficientExtensionRing
        ell E n) c a b)) ∧
    (∀ d : Compactification f,
      type_of% (WeilConjectures.sixFunctorProjection_compactification
        (Padic.coefficientExtensionRing ell E n) c d K L)) ∧
    (∀ (_hKTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn
      (Padic.coefficientExtensionRing ell E n) X a b K)
      (J : Ideal (Padic.coefficientExtensionRing ell E n))
      (_hJ : ∃ m : ℕ, 1 ≤ m ∧ m ≤ n ∧ Nonempty
        ((Padic.coefficientExtensionRing ell E n ⧸ J) ≃+*
          Padic.coefficientExtensionRing ell E m)),
      type_of% (WeilConjectures.sixFunctorProjection_reduction_finite
        (Padic.coefficientExtensionRing ell E n) c J K L)) ∧
    (∀ [IsProper f],
      type_of% (WeilConjectures.sixFunctorProjection_proper (Padic.coefficientExtensionRing ell E
        n) f K L)) := by
  sorry

/-- The finite canonical pentagon in the finite-type geometric setting.
The local instances below are the existing Mathlib consequences of the structure maps,
not extra assumptions on the inputs. Source: latest blueprint, composition pentagon
(blueprint: fix-prop-projection-formula). -/
def finitePentagonAssertions (A : Type (u + 1)) [CommRing A] [Finite A]
    {k : Type u} [Field k] {X Y Z T : SepFinType k}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T) : Prop :=
  letI : IsLocallyNoetherian X.obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian X.obj.hom
  letI : CompactSpace X.obj.left :=
    QuasiCompact.compactSpace_of_compactSpace X.obj.hom
  letI : IsNoetherian X.obj.left :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  letI : QuasiSeparatedSpace X.obj.left :=
    quasiSeparatedSpace_of_quasiSeparated X.obj.hom
  letI : IsLocallyNoetherian Y.obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian Y.obj.hom
  letI : CompactSpace Y.obj.left :=
    QuasiCompact.compactSpace_of_compactSpace Y.obj.hom
  letI : IsNoetherian Y.obj.left :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  letI : QuasiSeparatedSpace Y.obj.left :=
    quasiSeparatedSpace_of_quasiSeparated Y.obj.hom
  letI : IsLocallyNoetherian Z.obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian Z.obj.hom
  letI : CompactSpace Z.obj.left :=
    QuasiCompact.compactSpace_of_compactSpace Z.obj.hom
  letI : IsNoetherian Z.obj.left :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  letI : QuasiSeparatedSpace Z.obj.left :=
    quasiSeparatedSpace_of_quasiSeparated Z.obj.hom
  letI : IsLocallyNoetherian T.obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian T.obj.hom
  letI : CompactSpace T.obj.left :=
    QuasiCompact.compactSpace_of_compactSpace T.obj.hom
  letI : IsNoetherian T.obj.left :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  letI : QuasiSeparatedSpace T.obj.left :=
    quasiSeparatedSpace_of_quasiSeparated T.obj.hom
  letI : IsSeparated (f.hom.left ≫ Y.obj.hom) :=
    (Over.w f.hom).symm ▸ (inferInstance : IsSeparated X.obj.hom)
  letI : LocallyOfFiniteType (f.hom.left ≫ Y.obj.hom) :=
    (Over.w f.hom).symm ▸ (inferInstance : LocallyOfFiniteType X.obj.hom)
  letI : QuasiCompact (f.hom.left ≫ Y.obj.hom) :=
    (Over.w f.hom).symm ▸ (inferInstance : QuasiCompact X.obj.hom)
  letI : IsSeparated f.hom.left := IsSeparated.of_comp f.hom.left Y.obj.hom
  letI : LocallyOfFiniteType f.hom.left :=
    locallyOfFiniteType_of_comp f.hom.left Y.obj.hom
  letI : QuasiCompact f.hom.left := QuasiCompact.of_comp f.hom.left Y.obj.hom
  letI : IsSeparated (g.hom.left ≫ Z.obj.hom) :=
    (Over.w g.hom).symm ▸ (inferInstance : IsSeparated Y.obj.hom)
  letI : LocallyOfFiniteType (g.hom.left ≫ Z.obj.hom) :=
    (Over.w g.hom).symm ▸ (inferInstance : LocallyOfFiniteType Y.obj.hom)
  letI : QuasiCompact (g.hom.left ≫ Z.obj.hom) :=
    (Over.w g.hom).symm ▸ (inferInstance : QuasiCompact Y.obj.hom)
  letI : IsSeparated g.hom.left := IsSeparated.of_comp g.hom.left Z.obj.hom
  letI : LocallyOfFiniteType g.hom.left :=
    locallyOfFiniteType_of_comp g.hom.left Z.obj.hom
  letI : QuasiCompact g.hom.left := QuasiCompact.of_comp g.hom.left Z.obj.hom
  letI : IsSeparated (h.hom.left ≫ T.obj.hom) :=
    (Over.w h.hom).symm ▸ (inferInstance : IsSeparated Z.obj.hom)
  letI : LocallyOfFiniteType (h.hom.left ≫ T.obj.hom) :=
    (Over.w h.hom).symm ▸ (inferInstance : LocallyOfFiniteType Z.obj.hom)
  letI : QuasiCompact (h.hom.left ≫ T.obj.hom) :=
    (Over.w h.hom).symm ▸ (inferInstance : QuasiCompact Z.obj.hom)
  letI : IsSeparated h.hom.left := IsSeparated.of_comp h.hom.left T.obj.hom
  letI : LocallyOfFiniteType h.hom.left :=
    locallyOfFiniteType_of_comp h.hom.left T.obj.hom
  letI : QuasiCompact h.hom.left := QuasiCompact.of_comp h.hom.left T.obj.hom
  type_of% (WeilConjectures.sixFunctorProjection_pentagon
    A f.hom.left g.hom.left h.hom.left)

/-- Finite projection composition and its canonical associativity pentagon.
All schemes and arrows are separated of finite type over the given geometric field.
Source: latest blueprint fix-prop-projection-formula, composition clause
(blueprint: fix-prop-projection-formula).

Proof: step 5 applies prop-sf-pf-coherence to the canonical etale projection
and thm-sf-comp-composition to its compactification compositors. Their associativity
is exactly the canonical pentagon; refinement independence transports a compatible
tower to any chosen compactifications.
-/
theorem finiteComposition (_hell : ell ≠ D₀.p) {X Y Z T : SepFinType D₀.k}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)
    (d : Compactification g.hom.left)
    (e : Compactification (f.hom.left ≫ d.i))
    (K : DerivedCategoryModule (Padic.coefficientExtensionRing ell E n) X.obj.left)
    (L : DerivedCategoryModule (Padic.coefficientExtensionRing ell E n) Z.obj.left)
    (_hK : DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing ell E n) X.obj.left K)
    (_hL : DerivedCategory.isBoundedConstructible
      (Padic.coefficientExtensionRing ell E n) Z.obj.left L)
    (_hTor : ∃ a b : ℤ, DerivedCategory.hasTorAmplitudeIn
      (Padic.coefficientExtensionRing ell E n) Z.obj.left a b L) :
    (type_of% (WeilConjectures.sixFunctorProjection_composition
      (Padic.coefficientExtensionRing ell E n) f.hom.left g.hom.left d e K L)) ∧
    finitePentagonAssertions (Padic.coefficientExtensionRing ell E n) f g h := by
  sorry

end AlgebraicGeometry.Etale.AllCoefficientProjection

namespace AlgebraicGeometry.ProEtale.AllCoefficientProjection

/-- The finite pro-etale clause uses intrinsic constructibility of both inputs,
not an etale-origin hypothesis, and finite Tor only on L.
Source: latest blueprint fix-prop-projection-formula, finite coefficient clause
(blueprint: fix-prop-projection-formula).

Proof: step 1, lem-sf-proetale-constructible-origin, supplies etale representatives
of the intrinsically bounded constructible K and L. The finite Tor comparison
sk-cor-pe-finite-tor-comparison transfers the Tor bounds on L. Apply
lem-weil-finite-compact-projection-formula and transport its canonical map by
these representatives. That theorem identifies the proper counit and the open
projection, so its conclusion concerns the specified map, not an arbitrary iso.
-/
theorem finite (D₀ : WeilConjectures.FiniteFieldDatum.{u})
    (ell : ℕ) [Fact ell.Prime] (_hell : ell ≠ D₀.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic ell) E]
    [FiniteDimensional (Padic ell) E] (n : ℕ) [Fact (1 ≤ n)]
    {X Y : SepFinType D₀.k} (f : X ⟶ Y) (c : Compactification f.hom.left)
    (K : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X.obj.left)
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))))
    (L : _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology Y.obj.left)
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n))))
    (_hK : DerivedCategory.boundedConstructibleIntrinsic
      (Padic.coefficientExtensionRing ell E n) X.obj.left K)
    (_hL : DerivedCategory.boundedConstructibleIntrinsic
      (Padic.coefficientExtensionRing ell E n) Y.obj.left L)
    (_hTor : ∃ a b : ℤ, DerivedCategory.torAmplitudeIn
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n)) Y.obj.left a b L) :
    IsIso (((projectionMapOfCompactification
      (ModuleCat.{u + 1} (Padic.coefficientExtensionRing ell E n)) c).app K).app L) := by
  sorry

end AlgebraicGeometry.ProEtale.AllCoefficientProjection
