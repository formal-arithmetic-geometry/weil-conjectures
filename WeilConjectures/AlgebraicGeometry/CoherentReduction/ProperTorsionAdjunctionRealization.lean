/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoherentReduction.CoherentMappingSystems
public import WeilConjectures.AlgebraicGeometry.FiniteProperQuotient.FiniteExceptionalDerivedHom
public import WeilConjectures.AlgebraicGeometry.CoherentReduction.FiniteProperReductionTransport
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStar
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedBelowProEtaleComparison
public import WeilConjectures.AlgebraicGeometry.IntegralCtfEqualsBc
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import WeilConjectures.AlgebraicGeometry.ProEtale.Classical.ProEtaleClassicalDirectImagePreservation
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageMateCompatibility
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImageCanonicalMate
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDirectImage
public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import WeilConjectures.SixFunctors.ProEtale.Comparison
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusComp
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.CategoryTheory.Ringed.RingedDerivedClosedSymmetricMonoidal
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
public import WeilConjectures.CategoryTheory.RingedSiteGlobalRHom.RingedSiteGlobalRHomModel
public import WeilConjectures.CategoryTheory.DerivedInternalHomSectionsModel.DerivedInternalHomSectionsModel
public import WeilConjectures.CategoryTheory.SmoothPurity.HomComplexGlobalHomotopyOfUniverses
public import WeilConjectures.Algebra.Homology.KInjectiveHomComplexOfUniverses
public import WeilConjectures.AlgebraicGeometry.Picard.KFlatResolutionIndependentCoefficients
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HomModule
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.CategoryTheory.Limits.HasLimits
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.CategoryTheory.SmoothPurity.ComplexColimitHomotopyColimit
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
public import WeilConjectures.CategoryTheory.RingedSiteGlobalRHom.RingedSiteGlobalRHomDescent
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import WeilConjectures.Algebra.Homology.SiteTensorHom.SiteTensorHomEquiv
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import Mathlib.CategoryTheory.Limits.Yoneda
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralProperBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
public import WeilConjectures.CategoryTheory.ClosedScalarHom.ClosedScalarHomComparison
public import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.RingedTopoiCanonicalTensorPullbackOfUniverses
public import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientProjectionDataSupplement
public import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientPullbackComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.Picard.SuccessiveDerivedQuotientNormalization
public import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientPullbackShifts
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Functor.KanExtension.Preserves
public import WeilConjectures.Algebra.Homology.RingedCoefficientProjection.RingedCoefficientScalarUnits
public import WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.AdjunctionShift
public import WeilConjectures.Algebra.Homology.SheafRingDerivedCoefficientAdjunction
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
public import WeilConjectures.Algebra.Homology.System.SystemLevelLeftExtension
public import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension
public import WeilConjectures.AlgebraicGeometry.CondensedIntegralTower.IntegralTowerStatement
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.ProfiniteFiniteConstantLocalModel
public import WeilConjectures.CategoryTheory.ScalarLocalization.ScalarLocalization
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralModels
public import WeilConjectures.AlgebraicGeometry.CoefficientBoundedConstructibleProEtale
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalars
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousCoefficientModuleEncodingSupplement
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.Topology.MetricSpace.Ultra.TotallySeparated
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationMap
public import Mathlib.RingTheory.Localization.BaseChange
public import WeilConjectures.Mathlib.CategoryTheory.Linear.LinearFunctor
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Continuous.ContinuousIntegralPushComparisonSupplement
public import WeilConjectures.AlgebraicGeometry.ContinuousConstructibleIntegralModel
public import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Integral.IntegralModelsOperations
public import WeilConjectures.SixFunctors.Integral.IntegralModelsGenerators
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.PadicIntegersBoundedTriangulated
public import WeilConjectures.AlgebraicGeometry.Adic.AdicConstructibilityPredicateComparison
public import WeilConjectures.AlgebraicGeometry.Integral.IntegralLfpConstantModelComparison

import Mathlib.CategoryTheory.Adjunction.Basic
public import WeilConjectures.AlgebraicGeometry.VaryingRing.VaryingRingOperations
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.TorAmplitude

/-!
# Realization of the proper torsion adjunction

Source: `literature/blueprint/latest/blueprint/part-six-operations/
sec-coefficients-constructible/sec-n-brown/sk-thm-existence/
lem-sfb-dc-proper-pushforward-left-adjoint-qlbar.proof.md`, second sentence.
The statement retains the concrete coherent coefficient tower and its system-level
Hom comparison.  The integral right adjoint is a functor between the recorded
unbounded derived categories, with bounded-constructible preservation and the
canonical reduction comparison.  No equality is inferred by level evaluation.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.setOption false
set_option maxHeartbeats 2000000

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open WeilConjectures WeilConjectures.SemilinearSections
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CoherentReduction

attribute [local instance] proEtSmall sequenceSmall scalarSmallDerived

/-- The ambient integral module category, without a completeness condition.
Source: the ordinary-module convention of the node
(blueprint: lem-sfb-proper-torsion-adjunction-realization). -/
abbrev IntegralModules (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :=
  CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (internalRing T (Padic.coefficientExtensionIntegers l E))

/-- The ordinary unbounded derived category of integral modules.
Source: the ordinary-module convention of the node
(blueprint: lem-sfb-proper-torsion-adjunction-realization). -/
abbrev IntegralDerived (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :=
  DerivedCategory (IntegralModules l E T)

/-- The actual varying-coefficient module systems.
Source: Zheng, Construction 4.1
(blueprint: lem-sfb-proper-torsion-adjunction-realization). -/
abbrev TowerModules (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :=
  Systems.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
    (coefficients l E T) (transitions l E T)

/-- The ordinary derived category of the actual system category.
Source: Zheng, Construction 4.1
(blueprint: lem-sfb-proper-torsion-adjunction-realization). -/
abbrev TowerDerived (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) :=
  DS.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
    (coefficients l E T) (transitions l E T)

/-- Level restriction to the integral section ring.
Source: the inverse-limit construction, Stacks 0941
(blueprint: lem-sfb-proper-torsion-adjunction-realization). -/
def integralLevel (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) (n : ℕ) :=
  evaluation.{u + 1, u, u + 1} (Scheme.ProEt.topology T)
      (coefficients l E T) (transitions l E T) n ⋙
    res.{u + 1, u, u + 1} (coefficientMap l E T n)

/-- Total derived inverse limit, fixed by the ordinary limit universal property.
The projection maps retain the quotient transitions on every section; the universal
property is tested against every integral module. Thus the ordinary object is the
inverse limit of the restricted tower, and `universal` fixes its total right derived
functor, rather than supplying an unconstrained functor.
Source: the derived-limit step of the cited finite-E proof; Stacks 0941
(blueprint: lem-sfb-proper-torsion-adjunction-realization). -/
structure TorsionLimit (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) where
  ordinary : TowerModules l E T ⥤ IntegralModules l E T
  [additive : ordinary.Additive]
  projection : ∀ n : ℕ, ordinary ⋙ integralSections l E T ⟶ integralLevel l E T n
  compatible : ∀ (M : TowerModules l E T) (n : ℕ) (U : T.ProEtᵒᵖ)
      (x : ((integralSections l E T).obj (ordinary.obj M)).val.obj U),
    ((projection n).app M).val.app U x =
      ((transition (Scheme.ProEt.topology T) (coefficients l E T)
        (transitions l E T) (Nat.le_succ n)).app M).val.app U
          (((projection (n + 1)).app M).val.app U x)
  isLimit : ∀ (M : TowerModules l E T) (P : IntegralModules l E T)
      (f : ∀ n : ℕ, (integralSections l E T).obj P ⟶ (integralLevel l E T n).obj M),
    (∀ (n : ℕ) (U : T.ProEtᵒᵖ)
      (x : ((integralSections l E T).obj P).val.obj U),
        (f n).val.app U x =
          ((transition (Scheme.ProEt.topology T) (coefficients l E T)
            (transitions l E T) (Nat.le_succ n)).app M).val.app U
              ((f (n + 1)).val.app U x)) →
    ∃! g : P ⟶ ordinary.obj M,
      ∀ n : ℕ, (integralSections l E T).map g ≫ (projection n).app M = f n
  derived : TowerDerived l E T ⥤ IntegralDerived l E T
  unit : ordinary.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    DerivedCategory.Q ⋙ derived
  universal : derived.IsRightDerivedFunctor unit
    (HomologicalComplex.quasiIso (TowerModules l E T) (.up ℤ))
  adjunction : reduction l E T ⊣ derived

/-- The canonical scalar action on morphisms of actual derived systems.
Source: the global-section action of the coefficient algebra
(blueprint: lem-sfb-proper-torsion-adjunction-realization). -/
def systemSmul (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u})
    (a : Padic.coefficientExtensionIntegers l E)
    {M N : TowerDerived l E T} (f : M ⟶ N) : M ⟶ N := by
  letI := RingedSiteGlobalRHom.modulesLinear
    (systemRing (Scheme.ProEt.topology T) (coefficients l E T) (transitions l E T))
  exact (scalarAlgebra l E T a) • f

/-- The canonical finite constant coefficient presentation of a whole system ring.
Its components are the previously defined finite constant-section isomorphisms.
Source: finite coefficient comparison and Zheng Construction 4.1
(blueprint: lem-sfb-proper-torsion-adjunction-realization). -/
structure FiniteSystemPresentation (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (T : Scheme.{u}) where
  iso : systemRing (Scheme.ProEt.topology T)
      (VaryingRing.coefficients (fun n ↦ CommRingCat.of (Etale.FiniteProperQuotient.Ring l E n)) T)
      (VaryingRing.coefficientTransition
        (fun n ↦ CommRingCat.of (Etale.FiniteProperQuotient.Ring l E n))
        (fun n ↦ CommRingCat.ofHom (Etale.FiniteProperQuotient.quotient l E (Nat.le_succ n))) T) ≅
    systemRing (Scheme.ProEt.topology T) (coefficients l E T) (transitions l E T)
  component : ∀ (n : ℕ) (U : T.ProEtᵒᵖ),
    iso.hom.hom.app (op (n, U.unop)) =
      (finiteConstantIso T (Etale.FiniteProperQuotient.Ring l E n)).hom.hom.app U

/-- Derived system pushforward is the genuine levelwise ringed-topos direct image,
transported through the specified finite constant-section presentations.
Source: total derived system direct image in the node
(blueprint: lem-sfb-proper-torsion-adjunction-realization). -/
def systemPush (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (SZ : FiniteSystemPresentation l E Z) (SY : FiniteSystemPresentation l E Y) :
    TowerDerived l E Z ⥤ TowerDerived l E Y :=
  resD SZ.iso.hom ⋙ VaryingRing.P
    (fun n ↦ CommRingCat.of (Etale.FiniteProperQuotient.Ring l E n))
    (fun n ↦ CommRingCat.ofHom (Etale.FiniteProperQuotient.quotient l E (Nat.le_succ n))) p ⋙
    resD SY.iso.inv

section CoherentIdentity

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The actual coefficient module on the sequence site. Source: Zheng 4.1
(blueprint: lem-sfb-proper-torsion-adjunction-realization). -/
def coefficientUnitModule (T : Scheme.{u}) : TowerModules l E T :=
  SheafOfModules.unit (ring (coefficientSequenceTopology (Scheme.ProEt.topology T))
    (systemRing (Scheme.ProEt.topology T) (coefficients l E T) (transitions l E T)))

/-- The coefficient unit in degree zero. Source: Stacks 08JA
(blueprint: lem-sfb-proper-torsion-adjunction-realization). -/
def coefficientUnit (T : Scheme.{u}) : TowerDerived l E T :=
  DerivedCategory.Q.obj ((CochainComplex.singleFunctor _ 0).obj
    (coefficientUnitModule l E T))

end CoherentIdentity

section RationalCoefficients

variable (l : ℕ) [Fact l.Prime] (E : Type (u + 1)) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The rational condensed coefficient ring with its spectral topology.
Source: Bhatt--Scholze 6.5.1
(blueprint: lem-sfb-proper-torsion-adjunction-realization). -/
abbrev rationalPoint :=
  letI := spectralNorm.normedField ℚ_[l] E
  abelianPoint E

/-- Integral-to-rational coefficients, defined by continuous inclusion.
Source: the inversion-of-ell step of the cited finite-E proof
(blueprint: lem-sfb-proper-torsion-adjunction-realization). -/
def integralRationalPoint : abelianPoint (Padic.coefficientExtensionIntegers l E) ⟶
    rationalPoint l E :=
  letI := spectralNorm.normedField ℚ_[l] E
  (sheafCompose _ (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (continuousPointMap (Padic.coefficientExtensionIntegers l E).subtype
        continuous_subtype_val))

/-- The coefficient inclusion respects ring operations.
Source: continuous postcomposition
(blueprint: lem-sfb-proper-torsion-adjunction-realization). -/
instance integralRationalPoint_isMonHom : IsMonHom (integralRationalPoint l E) := by
  unfold integralRationalPoint
  infer_instance

/-- The rational bounded constructible category has its original cohomology predicate.
Source: the coefficient convention of the node
(blueprint: lem-sfb-proper-torsion-adjunction-realization). -/
abbrev RationalBc (T : Scheme.{u}) :=
  BoundedConstructible (condensedRingObj (rationalPoint l E) T)

/-- The specified total derived extension of integral coefficients to E.
Source: the inversion-of-ell step of the cited finite-E proof
(blueprint: lem-sfb-proper-torsion-adjunction-realization). -/
abbrev rationalExtension (T : Scheme.{u}) :=
  (CategoryTheory.Mod.extendScalars
    (AlgebraicGeometry.ProEtale.coefficientMap (integralRationalPoint l E) T)).leftDerivedFunctor

/-- The actual ordinary-module derived direct image with rational coefficients.
Source: the coefficient convention of the node
(blueprint: lem-sfb-proper-torsion-adjunction-realization). -/
abbrev rationalPush {Z Y : Scheme.{u}} (p : Z ⟶ Y) :=
  (CondensedRing.lowerStar (rationalPoint l E) p).rightDerivedFunctor

/-- The canonical proper integral-to-rational coefficient mate.
Source: the canonical-mate definition of the scalar comparison
(blueprint: lem-sfb-proper-torsion-adjunction-realization). -/
abbrev rationalProjection (hFlat : ∀ T : Scheme.{u}, PreservesFiniteLimits
    (CategoryTheory.Mod.extendScalars
      (AlgebraicGeometry.ProEtale.coefficientMap (integralRationalPoint l E) T)))
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) :=
  letI := hFlat
  CondensedRing.derivedPushHom (integralRationalPoint l E) p

end RationalCoefficients

/-- Integral realization on the bounded constructible categories. The functor on
the left is identified with the actual ordinary-module proper direct image.
The right functor is identified with total derived inverse limit, and its canonical
reduction map is the counit of the reduction--limit adjunction.
Source: the integral adjunction step of the cited finite-E proof
(blueprint: lem-sfb-proper-torsion-adjunction-realization). -/
structure ProperTorsionRealization (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (C : Bc l E Y ⥤ TowerDerived l E Z) where
  limitData : TorsionLimit l E Z
  push : Bc l E Z ⥤ Bc l E Y
  pushComparison : push ⋙ (boundedConstructible
      (internalRing Y (Padic.coefficientExtensionIntegers l E))).ι ≅
    (boundedConstructible (internalRing Z (Padic.coefficientExtensionIntegers l E))).ι ⋙
      integralPush l E p
  right : Bc l E Y ⥤ Bc l E Z
  adjunction : push ⊣ right
  [linearZ : Linear (Padic.coefficientExtensionIntegers l E) (Bc l E Z)]
  [linearY : Linear (Padic.coefficientExtensionIntegers l E) (Bc l E Y)]
  linearZ_spec : ∀ (M N : Bc l E Z) (a : Padic.coefficientExtensionIntegers l E)
      (f : M ⟶ N),
    (reductionBc l E Z).map (a • f) = systemSmul l E Z a ((reductionBc l E Z).map f)
  linearY_spec : ∀ (M N : Bc l E Y) (a : Padic.coefficientExtensionIntegers l E)
      (f : M ⟶ N),
    (reductionBc l E Y).map (a • f) = systemSmul l E Y a ((reductionBc l E Y).map f)
  homEquiv_linear : ∀ (M : Bc l E Z) (K : Bc l E Y)
      (a : Padic.coefficientExtensionIntegers l E) (f : push.obj M ⟶ K),
    adjunction.homEquiv M K (a • f) = a • adjunction.homEquiv M K f
  completeZ : ∀ M : Bc l E Z, IsIso (limitData.adjunction.unit.app M.obj)
  limitComparison : right ⋙ (boundedConstructible
      (internalRing Z (Padic.coefficientExtensionIntegers l E))).ι ≅ C ⋙ limitData.derived
  reductionIso : right ⋙ reductionBc l E Z ≅ C
  reduction_spec : ∀ K : Bc l E Y,
    reductionIso.hom.app K =
      (reduction l E Z).map (limitComparison.hom.app K) ≫
        limitData.adjunction.counit.app (C.obj K)

/-- Rational localization of the integral adjunction, with the actual rational
pushforward and the canonical scalar mate. The last field is the displayed counit
equality in the node.
Source: rationalization and inversion of ell in the cited finite-E proof
(blueprint: lem-sfb-proper-torsion-adjunction-realization). -/
structure ProperRationalRealization (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E]
    [FiniteDimensional ℚ_[l] E] {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (C : Bc l E Y ⥤ TowerDerived l E Z)
    (R : ProperTorsionRealization l E p C) where
  [coefficientFlat : ∀ T : Scheme.{u}, PreservesFiniteLimits
    (CategoryTheory.Mod.extendScalars
      (AlgebraicGeometry.ProEtale.coefficientMap (integralRationalPoint l E) T))]
  extensionZ : Bc l E Z ⥤ RationalBc l E Z
  extensionY : Bc l E Y ⥤ RationalBc l E Y
  extensionZComparison : extensionZ ⋙
      (boundedConstructible (condensedRingObj (rationalPoint l E) Z)).ι ≅
    (boundedConstructible (internalRing Z (Padic.coefficientExtensionIntegers l E))).ι ⋙
      rationalExtension l E Z
  extensionYComparison : extensionY ⋙
      (boundedConstructible (condensedRingObj (rationalPoint l E) Y)).ι ≅
    (boundedConstructible (internalRing Y (Padic.coefficientExtensionIntegers l E))).ι ⋙
      rationalExtension l E Y
  push : RationalBc l E Z ⥤ RationalBc l E Y
  pushComparison : push ⋙
      (boundedConstructible (condensedRingObj (rationalPoint l E) Y)).ι ≅
    (boundedConstructible (condensedRingObj (rationalPoint l E) Z)).ι ⋙ rationalPush l E p
  right : RationalBc l E Y ⥤ RationalBc l E Z
  adjunction : push ⊣ right
  lambda : R.right ⋙ extensionZ ≅ extensionY ⋙ right
  scalarComparison : R.push ⋙ extensionY ≅ extensionZ ⋙ push
  scalar_spec : ∀ M : Bc l E Z,
    extensionYComparison.hom.app (R.push.obj M) ≫
        (rationalExtension l E Y).map (R.pushComparison.hom.app M) ≫
        (rationalProjection l E coefficientFlat p).app M.obj =
      (scalarComparison.hom.app M).hom ≫
        pushComparison.hom.app (extensionZ.obj M) ≫
        (rationalPush l E p).map (extensionZComparison.hom.app M)
  localizationZ : letI := R.linearZ
    ∃ e : ScalarLocalization (Padic.coefficientExtensionIntegers l E) (Bc l E Z)
        (l : Padic.coefficientExtensionIntegers l E) ≌ RationalBc l E Z,
      Nonempty (ScalarLocalization.localization (Padic.coefficientExtensionIntegers l E)
        (Bc l E Z) (l : Padic.coefficientExtensionIntegers l E) ⋙ e.functor ≅ extensionZ)
  localizationY : letI := R.linearY
    ∃ e : ScalarLocalization (Padic.coefficientExtensionIntegers l E) (Bc l E Y)
        (l : Padic.coefficientExtensionIntegers l E) ≌ RationalBc l E Y,
      Nonempty (ScalarLocalization.localization (Padic.coefficientExtensionIntegers l E)
        (Bc l E Y) (l : Padic.coefficientExtensionIntegers l E) ⋙ e.functor ≅ extensionY)
  counit_eq : ∀ K : Bc l E Y,
    scalarComparison.hom.app (R.right.obj K) ≫
        push.map (lambda.hom.app K) ≫ adjunction.counit.app (extensionY.obj K) =
      extensionY.map (R.adjunction.counit.app K)

end AlgebraicGeometry.ProEtale.CoherentReduction
