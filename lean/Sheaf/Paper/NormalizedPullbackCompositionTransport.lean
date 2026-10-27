/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NB
-/
module

public import Sheaf.Paper.CompletedPrimitiveCounitComparison
public import Sheaf.Paper.IntegralComparisonSequenceSystems
public import Sheaf.Paper.ProEtaleCoefficientModulePullbackComposition
public import Sheaf.Paper.CompletedOperationExpressions
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.NormalizedDVRTower
public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Sheaf.Paper.IntegralDerivedOperationsOnSlices
public import Sheaf.Paper.SemilinearDerivedSections
public import Sheaf.Paper.IntegralReductionTowerCanonical
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import Sheaf.Paper.OrdinaryPullbackCompositionEvaluation
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
import Sheaf.Paper.IntegralOperationsWellDefined

/-! # Transport of normalized pullback composition through coherent realization

Source: Stacks Project, sites-modules.tex, Tag 03D8, and sites-cohomology.tex,
Tags 0D6D and 0941; explicit whole-system and counit refinement in the node
(blueprint: lem-pur-normalized-pullback-composition-transport).

All coefficients, reductions and derived categories are the recorded constructions.
An index n means positive exponent n+1. Site and coefficient universes are independent.
The two expressions in the conclusion are pullback (h >> f) (input C) and
pullback h (pullback f (input C)); their recursive beta formulas specialize below.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option linter.privateModule false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.SemilinearSections.moduleAbelian
  WeilConjectures.SemilinearSections.hasDerived



attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.leftAdjoint CategoryTheory.Functor.mapDerivedCategoryFactors
  CategoryTheory.Functor.rightDerivedFunctor
  WeilConjectures.coefficientConstantTowerLimit WeilConjectures.coefficientSequenceLimit
  WeilConjectures.completedIntegralCoefficientSheafUnrestricted
  WeilConjectures.scalarReductionExistence WeilConjectures.scalarReductionDerivedExistence
  WeilConjectures.unrestrictedIntegralReductionExistence

attribute [local instance] WeilConjectures.PrimitiveCounit.levelAdditive
  WeilConjectures.PrimitiveCounit.levelLimits WeilConjectures.PrimitiveCounit.levelColimits
attribute [local implicit_reducible] WeilConjectures.PrimitiveCounit.inverse
  WeilConjectures.PrimitiveCounit.pull WeilConjectures.PrimitiveCounit.direct
  WeilConjectures.PrimitiveCounit.ringMap WeilConjectures.PrimitiveCounit.ringComponent
  WeilConjectures.PrimitiveCounit.base
attribute [local implicit_reducible] SheafOfModules.instAbelian
  CategoryTheory.abelianOfAdjunction CategoryTheory.Abelian.ofCoimageImageComparisonIsIso
  WeilConjectures.scalarReductionSourceDerived WeilConjectures.scalarReductionTargetDerived
  WeilConjectures.coefficientConstantTowerDerived
  WeilConjectures.integralOperationsCommHasDerivedCategory
  WeilConjectures.integralTowerHasDerivedCategory
  WeilConjectures.integralCompletedRingHasDerivedCategory

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
/-- Use the recorded standard localization uniformly, including finite coefficients. -/
local instance standardDerived {A : Type*} [Category A] [Abelian A] :
    HasDerivedCategory A := HasDerivedCategory.standard A

attribute [local irreducible] roosF
  WeilConjectures.completedIntegralCommRingSheafUnrestricted
  WeilConjectures.integralDerivedPullback WeilConjectures.integralDerivedPullbackComparison
  Padic

attribute [local instance 30000] standardDerived

namespace WeilConjectures.PullbackCompositionTransport

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Derived evaluation of whole-system inverse image, normalized by the ordinary units.
Source: Stacks 03D8, 0D6D
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def evaluation {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    integralComparisonDerivedSequencePullback l E f ⋙ coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙
        (integralOperationsLevelPullback l E f n).mapDerivedCategory :=
  letI : (integralOperationsLevelPullback l E f n).Additive :=
    PrimitiveCounit.levelAdditive l E f n
  letI : PreservesFiniteLimits (integralOperationsLevelPullback l E f n) :=
    PrimitiveCounit.levelLimits l E f n
  letI : PreservesFiniteColimits (integralOperationsLevelPullback l E f n) :=
    PrimitiveCounit.levelColimits l E f n
  Functor.mapDerivedCategorySquareIso (ordinaryEvaluation l E f n)

/-- Finite adjunction-normalized derived compositor, obtained termwise by exactness.
Its ordinary map is the mate of fibre-product direct-image composition.
Source: Stacks 03D8, 0D6D
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def finiteComposition {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y) (n : ℕ) :
    (integralOperationsLevelPullback l E (h ≫ f) n).mapDerivedCategory ≅
      (integralOperationsLevelPullback l E f n).mapDerivedCategory ⋙
        (integralOperationsLevelPullback l E h n).mapDerivedCategory :=
  letI : (integralOperationsLevelPullback l E f n).Additive :=
    PrimitiveCounit.levelAdditive l E f n
  letI : PreservesFiniteLimits (integralOperationsLevelPullback l E f n) :=
    PrimitiveCounit.levelLimits l E f n
  letI : PreservesFiniteColimits (integralOperationsLevelPullback l E f n) :=
    PrimitiveCounit.levelColimits l E f n
  letI : (Scheme.coefficientProEtaleModulePullback h
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).Additive :=
    PrimitiveCounit.levelAdditive l E h n
  letI : PreservesFiniteLimits (Scheme.coefficientProEtaleModulePullback h
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    PrimitiveCounit.levelLimits l E h n
  letI : PreservesFiniteColimits (Scheme.coefficientProEtaleModulePullback h
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    PrimitiveCounit.levelColimits l E h n
  letI : (Scheme.coefficientProEtaleModulePullback (h ≫ f)
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).Additive :=
    PrimitiveCounit.levelAdditive l E (h ≫ f) n
  letI : PreservesFiniteLimits (Scheme.coefficientProEtaleModulePullback (h ≫ f)
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    PrimitiveCounit.levelLimits l E (h ≫ f) n
  letI : PreservesFiniteColimits (Scheme.coefficientProEtaleModulePullback (h ≫ f)
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    PrimitiveCounit.levelColimits l E (h ≫ f) n
  letI : (Scheme.coefficientProEtaleModulePullback f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))).Additive :=
    PrimitiveCounit.levelAdditive l E f n
  letI : PreservesFiniteLimits (Scheme.coefficientProEtaleModulePullback f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    PrimitiveCounit.levelLimits l E f n
  letI : PreservesFiniteColimits (Scheme.coefficientProEtaleModulePullback f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) :=
    PrimitiveCounit.levelColimits l E f n
  Functor.mapDerivedCategoryTriangleIso
    (Scheme.coefficientModulePullbackComposition h f
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1)))))

attribute [local irreducible] evaluation finiteComposition

/-- Finite evaluation and both actual quotient-transition squares for the already
constructed whole-system compositor. The last two equations are the extension-form
squares for the actual transition adjoints, with no unit-transition input assumption.
Source: Stacks 03D8, 0D6D; node proof steps 1--3
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
structure SystemLaws {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (S : CoefficientDerivedSystemCalculus l E Z) : Prop where
  finite : ∀ (C : coefficientSequenceDerived l E Y)
    (_hC : IsNormalizedCoefficientSequence l E Y C) (n : ℕ),
    (coefficientSequenceDerivedEvaluation l E Z n).map
        ((integralComparisonSystemComposition l E h f).hom.app C) ≫
      (evaluation l E h n).hom.app ((integralComparisonDerivedSequencePullback l E f).obj C) ≫
      (integralOperationsLevelPullback l E h n).mapDerivedCategory.map
        ((evaluation l E f n).hom.app C) =
      (evaluation l E (h ≫ f) n).hom.app C ≫
        (finiteComposition l E h f n).hom.app
          ((coefficientSequenceDerivedEvaluation l E Y n).obj C)
  transition : ∀ (C : coefficientSequenceDerived l E Y)
    (_hC : IsNormalizedCoefficientSequence l E Y C) {m n : ℕ} (q : n ≤ m),
    (coefficientSequenceDerivedEvaluation l E Z m).map
        ((integralComparisonSystemComposition l E h f).hom.app C) ≫
      (coefficientSequenceDerivedTransition l E Z q).app _ =
      (coefficientSequenceDerivedTransition l E Z q).app _ ≫
        (normalizedDVRRes l E Z q).map
          ((coefficientSequenceDerivedEvaluation l E Z n).map
            ((integralComparisonSystemComposition l E h f).hom.app C))
  inverse_transition : ∀ (C : coefficientSequenceDerived l E Y)
    (_hC : IsNormalizedCoefficientSequence l E Y C) {m n : ℕ} (q : n ≤ m),
    (coefficientSequenceDerivedEvaluation l E Z m).map
        ((integralComparisonSystemComposition l E h f).inv.app C) ≫
      (coefficientSequenceDerivedTransition l E Z q).app _ =
      (coefficientSequenceDerivedTransition l E Z q).app _ ≫
        (normalizedDVRRes l E Z q).map
          ((coefficientSequenceDerivedEvaluation l E Z n).map
            ((integralComparisonSystemComposition l E h f).inv.app C))
  adjoint_transition : ∀ (C : coefficientSequenceDerived l E Y)
    (_hC : IsNormalizedCoefficientSequence l E Y C) {m n : ℕ} (q : n ≤ m),
    (coefficientFiniteQuotientDerived l E Z q).map
        ((coefficientSequenceDerivedEvaluation l E Z m).map
          ((integralComparisonSystemComposition l E h f).hom.app C)) ≫
      coefficientSequenceTransitionAdjoint l E Z S.toCoefficientDerivedSystemTensors
        S.quotientCalculus q _ =
      coefficientSequenceTransitionAdjoint l E Z S.toCoefficientDerivedSystemTensors
        S.quotientCalculus q _ ≫
        (coefficientSequenceDerivedEvaluation l E Z n).map
          ((integralComparisonSystemComposition l E h f).hom.app C)
  inverse_adjoint_transition :
    ∀ (C : coefficientSequenceDerived l E Y)
    (_hC : IsNormalizedCoefficientSequence l E Y C) {m n : ℕ} (q : n ≤ m),
    (coefficientFiniteQuotientDerived l E Z q).map
        ((coefficientSequenceDerivedEvaluation l E Z m).map
          ((integralComparisonSystemComposition l E h f).inv.app C)) ≫
      coefficientSequenceTransitionAdjoint l E Z S.toCoefficientDerivedSystemTensors
        S.quotientCalculus q _ =
      coefficientSequenceTransitionAdjoint l E Z S.toCoefficientDerivedSystemTensors
        S.quotientCalculus q _ ≫
        (coefficientSequenceDerivedEvaluation l E Z n).map
          ((integralComparisonSystemComposition l E h f).inv.app C)

/-- The strict complex compositor, before localization, with every quotient transition.
Source: Stacks 03D8, 0D6D; node proof steps 1--3
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def strictComposition {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :=
  (PrimitiveCounit.restrictComplex l E Z).mapIso
    ((NatIso.mapHomologicalComplex (integralComparisonSequenceComposition l E h f)
      (.up ℤ)).app C)

/-- Restriction of derived pullback agrees with restriction of its exact complex model.
Source: Stacks 0D6D, 0941
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def restrictionFactor {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    (coefficientSequenceDerivedRestriction l E X).obj
        ((integralComparisonDerivedSequencePullback l E f).obj (DerivedCategory.Q.obj C)) ≅
      DerivedCategory.Q.obj ((PrimitiveCounit.restrictComplex l E X).obj
        (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C)) :=
  (coefficientSequenceDerivedRestriction l E X).mapIso
      ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.app C) ≪≫
    (coefficientSequenceRestriction l E X).mapDerivedCategoryFactors.app _

/-- Iterated version of the same localization comparison, preserving the given parentheses.
Source: Stacks 0D6D, 0941
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def iteratedRestrictionFactor {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
    (coefficientSequenceDerivedRestriction l E Z).obj
        ((integralComparisonDerivedSequencePullback l E h).obj
          ((integralComparisonDerivedSequencePullback l E f).obj (DerivedCategory.Q.obj C))) ≅
      DerivedCategory.Q.obj ((PrimitiveCounit.restrictComplex l E Z).obj
        (((integralComparisonSequencePullback l E h).mapHomologicalComplex (.up ℤ)).obj
          (((integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ)).obj C))) :=
  (coefficientSequenceDerivedRestriction l E Z).mapIso
      ((integralComparisonDerivedSequencePullback l E h).mapIso
        ((integralComparisonSequencePullback l E f).mapDerivedCategoryFactors.app C)) ≪≫
    restrictionFactor l E h (((integralComparisonSequencePullback l E f).mapHomologicalComplex
      (.up ℤ)).obj C)

attribute [local irreducible] strictComposition restrictionFactor iteratedRestrictionFactor

/-- The actual product/cone map realizes L(a), and likewise its inverse, on every
strict complex presentation, including complexes representing arbitrary input systems.
The Roos functor is the existing product map on both shifted cone coordinates.
Source: Stacks 0941; node proof step 5
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def RepresentativeForward {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (ρ : PrimitiveCounit.RoosRealization l E Z) : Prop :=
  ∀ (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (_hC : IsNormalizedCoefficientSequence l E Y (DerivedCategory.Q.obj C)),
    ρ.comparison.hom.app _ ≫ (coefficientConstantTowerLimit l E Z).map
      ((restrictionFactor l E (h ≫ f) C).inv ≫
        (coefficientSequenceDerivedRestriction l E Z).map
          ((integralComparisonSystemComposition l E h f).hom.app (DerivedCategory.Q.obj C)) ≫
        (iteratedRestrictionFactor l E h f C).hom) =
      DerivedCategory.Q.map (roosF.map (strictComposition l E h f C).hom) ≫
        ρ.comparison.hom.app _

/-- The unchanged inverse strict-complex/Roos representative equation.
Source: Stacks 0941; parent proof step 5
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def RepresentativeBackward {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (ρ : PrimitiveCounit.RoosRealization l E Z) : Prop :=
  ∀ (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (_hC : IsNormalizedCoefficientSequence l E Y (DerivedCategory.Q.obj C)),
    ρ.comparison.hom.app _ ≫ (coefficientConstantTowerLimit l E Z).map
      ((iteratedRestrictionFactor l E h f C).inv ≫
        (coefficientSequenceDerivedRestriction l E Z).map
          ((integralComparisonSystemComposition l E h f).inv.app (DerivedCategory.Q.obj C)) ≫
        (restrictionFactor l E (h ≫ f) C).hom) =
      DerivedCategory.Q.map (roosF.map (strictComposition l E h f C).inv) ≫
        ρ.comparison.hom.app _


attribute [local irreducible] RepresentativeForward RepresentativeBackward

/-- Both actual strict-complex representative equations, with their predicate types folded.
Source: Stacks 0941; parent proof step 5
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def RepresentativeLaws {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (ρ : PrimitiveCounit.RoosRealization l E Z) : Prop :=
  RepresentativeForward l E h f ρ ∧ RepresentativeBackward l E h f ρ

/-- Forward projection of the two representative equations. -/
theorem RepresentativeLaws.forward {X Y Z : Scheme.{t}} {h : Z ⟶ X} {f : X ⟶ Y}
    {ρ : PrimitiveCounit.RoosRealization l E Z} (H : RepresentativeLaws l E h f ρ) :
    RepresentativeForward l E h f ρ := H.1

/-- Backward projection of the two representative equations. -/
theorem RepresentativeLaws.backward {X Y Z : Scheme.{t}} {h : Z ⟶ X} {f : X ⟶ Y}
    {ρ : PrimitiveCounit.RoosRealization l E Z} (H : RepresentativeLaws l E h f ρ) :
    RepresentativeBackward l E h f ρ := H.2

variable {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
  (SY : CoefficientDerivedSystemReduction l E Y)
  (SX : CoefficientDerivedSystemReduction l E X)
  (SZ : CoefficientDerivedSystemCalculus l E Z)
  (rf : integralDerivedPullback l E f ≅
    SY.reduction ⋙ PrimitiveCounit.pull l E f ⋙ coefficientSequenceLimit l E X)
  (rh : integralDerivedPullback l E h ≅
    SX.reduction ⋙ PrimitiveCounit.pull l E h ⋙ coefficientSequenceLimit l E Z)
  (rhf : integralDerivedPullback l E (h ≫ f) ≅
    SY.reduction ⋙ PrimitiveCounit.pull l E (h ≫ f) ⋙
      coefficientSequenceLimit l E Z)

/-- The primitive comparison as a natural transformation, with canonical codomain.
Source: the recursive beta formula, Stacks 0941
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def canonicalBetaTransformation {V W : Scheme.{t}} (g : V ⟶ W)
    (S : CoefficientDerivedSystemReduction l E W)
    (r : integralDerivedPullback l E g ≅
      S.reduction ⋙ PrimitiveCounit.pull l E g ⋙ coefficientSequenceLimit l E V) :
    coefficientSequenceLimit l E W ⋙ integralDerivedPullback l E g ⟶
      integralComparisonDerivedSequencePullback l E g ⋙ coefficientSequenceLimit l E V :=
  Functor.whiskerLeft (coefficientSequenceLimit l E W) r.hom ≫
    Functor.whiskerRight S.adjunction.counit
      (PrimitiveCounit.pull l E g ⋙ coefficientSequenceLimit l E V)

/-- The component of the recursive primitive comparison.
Source: the recursive beta formula, Stacks 0941
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def canonicalBeta {V W : Scheme.{t}} (g : V ⟶ W)
    (S : CoefficientDerivedSystemReduction l E W)
    (r : integralDerivedPullback l E g ≅
      S.reduction ⋙ PrimitiveCounit.pull l E g ⋙ coefficientSequenceLimit l E V)
    (A : coefficientSequenceDerived l E W) :
    (integralDerivedPullback l E g).obj ((coefficientSequenceLimit l E W).obj A) ⟶
      (coefficientSequenceLimit l E V).obj
        ((integralComparisonDerivedSequencePullback l E g).obj A) :=
  (canonicalBetaTransformation l E g S r).app A

attribute [local irreducible] canonicalBetaTransformation canonicalBeta

/-- Recursive comparison for P=F_(f h)(C); the input comparison is the identity.
Source: node recursive beta formula and proof step 4
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def betaSource (C : coefficientSequenceDerived l E Y) :=
  canonicalBeta l E (h ≫ f) SY rhf C

/-- Recursive comparison for Q=F_h(F_f(C)), applying the inner beta before outer beta.
Source: node recursive beta formula and proof step 4
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def betaTarget (C : coefficientSequenceDerived l E Y) :=
  (integralDerivedPullback l E h).map (canonicalBeta l E f SY rf C) ≫
    canonicalBeta l E h SX rh ((integralComparisonDerivedSequencePullback l E f).obj C)

/-- Coherent reduction of beta_P followed by the one whole-system counit.
Source: node gamma formula (blueprint: lem-pur-normalized-pullback-composition-transport). -/
def gammaSource (C : coefficientSequenceDerived l E Y) :=
  SZ.reduction.map (betaSource l E h f SY rhf C) ≫
    SZ.adjunction.counit.app ((integralComparisonDerivedSequencePullback l E (h ≫ f)).obj C)

/-- Coherent reduction of beta_Q followed by that same counit.
Source: node gamma formula (blueprint: lem-pur-normalized-pullback-composition-transport). -/
def gammaTarget (C : coefficientSequenceDerived l E Y) :=
  SZ.reduction.map (betaTarget l E h f SY SX rf rh C) ≫
    SZ.adjunction.counit.app ((integralComparisonDerivedSequencePullback l E h).obj
      ((integralComparisonDerivedSequencePullback l E f).obj C))

/-- The actual completed compositor: conjugate total limit of the canonical whole-system
compositor by the recursively defined primitive quotient-model comparisons.
Source: node displayed formula and proof steps 4--5
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def completed (C : coefficientSequenceDerived l E Y)
    [IsIso (betaSource l E h f SY rhf C)]
    [IsIso (betaTarget l E h f SY SX rf rh C)] :=
  asIso (betaSource l E h f SY rhf C) ≪≫
    (coefficientSequenceLimit l E Z).mapIso ((integralComparisonSystemComposition l E h f).app C)
      ≪≫ (asIso (betaTarget l E h f SY SX rf rh C)).symm

attribute [local irreducible] betaSource betaTarget gammaSource gammaTarget completed

/- Transport equations and naturality, retaining the actual reduced system morphisms.
Source: node proof steps 4--6
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
--
/-- The unchanged TransportReduction equation. Source: Stacks 0941
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def TransportReduction (C : coefficientSequenceDerived l E Y)
    [IsIso (betaSource l E h f SY rhf C)]
    [IsIso (betaTarget l E h f SY SX rf rh C)] : Prop :=
  SZ.reduction.map (completed l E h f SY SX rf rh rhf C).hom ≫
      gammaTarget l E h f SY SX SZ rf rh C =
    gammaSource l E h f SY SZ rhf C ≫ (integralComparisonSystemComposition l E h f).hom.app C

/-- The unchanged TransportInverseReduction equation. Source: Stacks 0941
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def TransportInverseReduction (C : coefficientSequenceDerived l E Y)
    [IsIso (betaSource l E h f SY rhf C)]
    [IsIso (betaTarget l E h f SY SX rf rh C)] : Prop :=
  SZ.reduction.map (completed l E h f SY SX rf rh rhf C).inv ≫
      gammaSource l E h f SY SZ rhf C =
    gammaTarget l E h f SY SX SZ rf rh C ≫ (integralComparisonSystemComposition l E h f).inv.app C

/-- The unchanged TransportNaturality equation. Source: Stacks 0941
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def TransportNaturality (C : coefficientSequenceDerived l E Y)
    [IsIso (betaSource l E h f SY rhf C)]
    [IsIso (betaTarget l E h f SY SX rf rh C)] : Prop :=
  ∀ (C' : coefficientSequenceDerived l E Y)
    (_hC' : IsNormalizedCoefficientSequence l E Y C')
    [IsIso (betaSource l E h f SY rhf C')]
    [IsIso (betaTarget l E h f SY SX rf rh C')]
    [IsIso (gammaSource l E h f SY SZ rhf C')]
    [IsIso (gammaTarget l E h f SY SX SZ rf rh C')]
    (v : C ⟶ C'),
    (integralDerivedPullback l E (h ≫ f)).map ((coefficientSequenceLimit l E Y).map v) ≫
        (completed l E h f SY SX rf rh rhf C').hom =
      (completed l E h f SY SX rf rh rhf C).hom ≫
        (integralDerivedPullback l E h).map
          ((integralDerivedPullback l E f).map ((coefficientSequenceLimit l E Y).map v))

attribute [local irreducible] TransportReduction TransportInverseReduction TransportNaturality

/-- Completed transport, inverse transport, and naturality.
Source: Stacks 0941 (blueprint: lem-pur-normalized-pullback-composition-transport). -/
def TransportLaws (C : coefficientSequenceDerived l E Y)
    [IsIso (betaSource l E h f SY rhf C)]
    [IsIso (betaTarget l E h f SY SX rf rh C)] : Prop :=
  TransportReduction l E h f SY SX SZ rf rh rhf C ∧
    TransportInverseReduction l E h f SY SX SZ rf rh rhf C ∧
      TransportNaturality l E h f SY SX SZ rf rh rhf C

/-- Projection of the unchanged completed transport law. -/
theorem TransportLaws.reduction (C : coefficientSequenceDerived l E Y)
    [IsIso (betaSource l E h f SY rhf C)]
    [IsIso (betaTarget l E h f SY SX rf rh C)]
    (H : TransportLaws l E h f SY SX SZ rf rh rhf C) :
    TransportReduction l E h f SY SX SZ rf rh rhf C := H.1

/-- Projection of the unchanged completed transport law. -/
theorem TransportLaws.inverse_reduction (C : coefficientSequenceDerived l E Y)
    [IsIso (betaSource l E h f SY rhf C)]
    [IsIso (betaTarget l E h f SY SX rf rh C)]
    (H : TransportLaws l E h f SY SX SZ rf rh rhf C) :
    TransportInverseReduction l E h f SY SX SZ rf rh rhf C := H.2.1

/-- Projection of the unchanged completed transport law. -/
theorem TransportLaws.naturality (C : coefficientSequenceDerived l E Y)
    [IsIso (betaSource l E h f SY rhf C)]
    [IsIso (betaTarget l E h f SY SX rf rh C)]
    (H : TransportLaws l E h f SY SX SZ rf rh rhf C) :
    TransportNaturality l E h f SY SX SZ rf rh rhf C := H.2.2


section SquarePasting

variable {A₀ A₁ A₂ B₀ B₁ B₂ : Type*} [Category A₀] [Category A₁] [Category A₂] [Category B₀]
  [Category B₁] [Category B₂] [Abelian A₀] [Abelian A₁] [Abelian A₂] [Abelian B₀] [Abelian B₁]
  [Abelian B₂] [HasDerivedCategory A₀] [HasDerivedCategory A₁] [HasDerivedCategory A₂]
  [HasDerivedCategory B₀] [HasDerivedCategory B₁] [HasDerivedCategory B₂]
  {r₀ : A₀ ⥤ B₀} {r₁ : A₁ ⥤ B₁} {r₂ : A₂ ⥤ B₂} {P₂ : A₀ ⥤ A₁} {P₁ : A₁ ⥤ A₂} {P₁₂ : A₀ ⥤ A₂}
  {p₂ : B₀ ⥤ B₁} {p₁ : B₁ ⥤ B₂} {p₁₂ : B₀ ⥤ B₂}
  [r₀.Additive] [PreservesFiniteLimits r₀] [PreservesFiniteColimits r₀]
  [r₁.Additive] [PreservesFiniteLimits r₁] [PreservesFiniteColimits r₁]
  [r₂.Additive] [PreservesFiniteLimits r₂] [PreservesFiniteColimits r₂]
  [P₂.Additive] [PreservesFiniteLimits P₂] [PreservesFiniteColimits P₂]
  [P₁.Additive] [PreservesFiniteLimits P₁] [PreservesFiniteColimits P₁]
  [P₁₂.Additive] [PreservesFiniteLimits P₁₂] [PreservesFiniteColimits P₁₂]
  [p₂.Additive] [PreservesFiniteLimits p₂] [PreservesFiniteColimits p₂]
  [p₁.Additive] [PreservesFiniteLimits p₁] [PreservesFiniteColimits p₁]
  [p₁₂.Additive] [PreservesFiniteLimits p₁₂] [PreservesFiniteColimits p₁₂]

private theorem reverse_square_pasting (α₂ : r₀ ⋙ p₂ ≅ P₂ ⋙ r₁)
    (α₁ : r₁ ⋙ p₁ ≅ P₁ ⋙ r₂) (α₁₂ : r₀ ⋙ p₁₂ ≅ P₁₂ ⋙ r₂)
    (e : p₁₂ ≅ p₂ ⋙ p₁) (e' : P₁₂ ≅ P₂ ⋙ P₁)
    (h : ∀ X, α₁₂.hom.app X ≫ r₂.map (e'.hom.app X) =
      e.hom.app (r₀.obj X) ≫ p₁.map (α₂.hom.app X) ≫ α₁.hom.app (P₂.obj X))
    (K : DerivedCategory A₀) :
    r₂.mapDerivedCategory.map ((Functor.mapDerivedCategoryTriangleIso e').hom.app K) ≫
      (Functor.mapDerivedCategorySquareIso α₁).inv.app (P₂.mapDerivedCategory.obj K) ≫
      p₁.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso α₂).inv.app K) =
    (Functor.mapDerivedCategorySquareIso α₁₂).inv.app K ≫
      (Functor.mapDerivedCategoryTriangleIso e).hom.app (r₀.mapDerivedCategory.obj K) := by
  have he := Functor.mapDerivedCategorySquareIso_hom_app_comp α₂ α₁ α₁₂ e e' h K
  apply (cancel_epi ((Functor.mapDerivedCategorySquareIso α₁₂).hom.app K)).1
  simp only [Iso.hom_inv_id_app_assoc]
  rw [reassoc_of% he]
  simp only [← p₁.mapDerivedCategory.map_comp, Iso.hom_inv_id_app,
    Iso.hom_inv_id_app_assoc]
  erw [p₁.mapDerivedCategory.map_id, Category.comp_id]

end SquarePasting

private theorem derived_inverse (F G : Type*) [Category F] [Category G]
    [Abelian F] [Abelian G] [HasDerivedCategory F] [HasDerivedCategory G]
    {P Q : F ⥤ G} [P.Additive] [Q.Additive]
    [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    [PreservesFiniteLimits Q] [PreservesFiniteColimits Q] (e : P ≅ Q) :
    (Functor.mapDerivedCategoryNatIso e.symm).inv =
      (Functor.mapDerivedCategoryNatIso e).hom := by
  have h := Functor.mapDerivedCategoryNatIso_symm e.symm
  simpa only [Iso.symm_symm_eq] using h.symm

section SquareInverse
variable {A B B' E : Type*} [Category A] [Category B] [Category B'] [Category E] [Abelian A]
  [Abelian B] [Abelian B'] [Abelian E] [HasDerivedCategory A] [HasDerivedCategory B]
  [HasDerivedCategory B'] [HasDerivedCategory E]
  {F₁ : A ⥤ B} {F₂ : B ⥤ E} {G₁ : A ⥤ B'} {G₂ : B' ⥤ E}
  [F₁.Additive] [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [F₂.Additive] [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [G₁.Additive] [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
  [G₂.Additive] [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]


private theorem square_inverse (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) :
    (Functor.mapDerivedCategorySquareIso e.symm).inv =
      (Functor.mapDerivedCategorySquareIso e).hom := by
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_inv, Iso.symm_inv,
    Iso.trans_hom, Iso.symm_hom, derived_inverse, Category.assoc]
end SquareInverse

private theorem composition_factors
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Abelian A] [Abelian B] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D)
    [F.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (e : H ≅ F ⋙ G) (K : CochainComplex A ℤ) :
    (Functor.mapDerivedCategoryNatIso e ≪≫
        Functor.mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K) ≫
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      H.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rfl

private theorem restriction_composition
    {A B D T : Type*} [Category A] [Category B] [Category D] [Category T]
    [Abelian A] [Abelian B] [Abelian D] [Abelian T]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory D]
    [HasDerivedCategory T]
    (F : A ⥤ B) (G : B ⥤ D) (H : A ⥤ D) (R : D ⥤ T)
    [F.Additive] [G.Additive] [H.Additive] [R.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (e : H ≅ F ⋙ G) (K : CochainComplex A ℤ) :
    (R.mapDerivedCategory.mapIso (H.mapDerivedCategoryFactors.app K) ≪≫
        R.mapDerivedCategoryFactors.app _).inv ≫
      R.mapDerivedCategory.map
        ((Functor.mapDerivedCategoryNatIso e ≪≫
          Functor.mapDerivedCategoryCompIso F G).hom.app (DerivedCategory.Q.obj K)) ≫
      (R.mapDerivedCategory.mapIso
          (G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app K)) ≪≫
        R.mapDerivedCategory.mapIso (G.mapDerivedCategoryFactors.app _) ≪≫
        R.mapDerivedCategoryFactors.app _).hom =
      DerivedCategory.Q.map ((R.mapHomologicalComplex (.up ℤ)).map
        ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K)) := by
  apply (cancel_epi
    (R.mapDerivedCategory.mapIso (H.mapDerivedCategoryFactors.app K) ≪≫
      R.mapDerivedCategoryFactors.app _).hom).1
  rw [Iso.hom_inv_id_assoc]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Category.assoc]
  have hm := congrArg (fun z ↦ R.mapDerivedCategory.map z)
    (composition_factors F G H e K)
  simp only [CategoryTheory.Functor.map_comp] at hm
  erw [reassoc_of% hm]
  erw [R.mapDerivedCategoryFactors.hom.naturality]
  rfl

private theorem pullBeta_naturality {V W : Scheme.{t}} (g : V ⟶ W)
    (S : CoefficientDerivedSystemReduction l E W)
    (r : integralDerivedPullback l E g ≅
      S.reduction ⋙ PrimitiveCounit.pull l E g ⋙
        coefficientSequenceLimit l E V)
    {A B : coefficientSequenceDerived l E W} (v : A ⟶ B) :
    (integralDerivedPullback l E g).map ((coefficientSequenceLimit l E W).map v) ≫
        canonicalBeta l E g S r B =
      canonicalBeta l E g S r A ≫
        (coefficientSequenceLimit l E V).map
          ((integralComparisonDerivedSequencePullback l E g).map v) := by
  simpa only [canonicalBeta, Functor.comp_map] using
    (canonicalBetaTransformation l E g S r).naturality v

private theorem counit_conjugation
    {A B : Type*} [Category A] [Category B] {R : A ⥤ B} {L : B ⥤ A}
    (adj : R ⊣ L) {P Q : A} {U V : B}
    (b : P ⟶ L.obj U) (c : Q ⟶ L.obj V) [IsIso c] (a : U ⟶ V) :
    R.map (b ≫ L.map a ≫ inv c) ≫ (R.map c ≫ adj.counit.app V) =
      (R.map b ≫ adj.counit.app U) ≫ a := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc (inv c), IsIso.inv_hom_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  exact congrArg (fun z ↦ R.map b ≫ z) (adj.counit.naturality a)

private theorem conjugation_naturality
    {A B C : Type*} [Category A] [Category B] [Category C]
    (F G : A ⥤ B) (L : B ⥤ C) (P Q : A ⥤ C) (a : F ⟶ G)
    {X Y : A} (v : X ⟶ Y)
    (bX : P.obj X ⟶ L.obj (F.obj X)) (bY : P.obj Y ⟶ L.obj (F.obj Y))
    (cX : Q.obj X ⟶ L.obj (G.obj X)) (cY : Q.obj Y ⟶ L.obj (G.obj Y))
    [IsIso cX] [IsIso cY]
    (hb : P.map v ≫ bY = bX ≫ L.map (F.map v))
    (hc : Q.map v ≫ cY = cX ≫ L.map (G.map v)) :
    P.map v ≫ (bY ≫ L.map (a.app Y) ≫ inv cY) =
      (bX ≫ L.map (a.app X) ≫ inv cX) ≫ Q.map v := by
  apply (cancel_mono cY).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← Category.assoc, hb, Category.assoc, ← L.map_comp, a.naturality,
    L.map_comp]
  rw [hc, IsIso.inv_hom_id_assoc]

/-- Canonical pullback composition on arbitrary normalized whole systems, and its
transport through the actual quotient-complex/Roos realization. Realization parameters
are the dependency's normalized presentations, not arbitrary comparison maps.
Source: Stacks Project, sites-modules.tex Tag 03D8; sites-cohomology.tex Tags 0D6D,
0941 (blueprint: lem-pur-normalized-pullback-composition-transport).
Proof: derive the ordinary unit-normalized evaluation/composition square using
mapDerivedCategorySquareIso_hom_app_comp, then cancel the inverse evaluation
comparisons. Both transition equations are naturality of the actual system
transition; their adjoints follow by transposing this same square. The strict
representative equations follow from the defining derived localization factors
and naturality of the given Roos comparison. Finally, apply counit naturality
to the beta-conjugated system compositor and its inverse, and use naturality
of the recursive beta maps for naturality of completed composition. All maps
are whole-system maps; no faithfulness of evaluations or interchange of
pullback with a product is used. -/
theorem normalizedPullbackCompositionTransport
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y))
    (_hZ : ∀ z : Z, IsUnit (l : Z.presheaf.stalk z))
    (ρX : PrimitiveCounit.RoosRealization l E X)
    (ρZ : PrimitiveCounit.RoosRealization l E Z)
    (_hf : PrimitiveCounit.PullModel l E f SY ρX rf)
    (_hh : PrimitiveCounit.PullModel l E h SX ρZ rh)
    (_hhf : PrimitiveCounit.PullModel l E (h ≫ f) SY ρZ rhf)
    (C : coefficientSequenceDerived l E Y)
    (_hC : IsNormalizedCoefficientSequence l E Y C)
    [IsIso (betaSource l E h f SY rhf C)]
    [IsIso (betaTarget l E h f SY SX rf rh C)]
    [IsIso (gammaSource l E h f SY SZ rhf C)]
    [IsIso (gammaTarget l E h f SY SX SZ rf rh C)] :
    SystemLaws l E h f SZ ∧ RepresentativeLaws l E h f ρZ ∧
      TransportLaws l E h f SY SX SZ rf rh rhf C := by
  clear _hf _hh _hhf ρX _hX _hY _hZ _hC
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro A hA n
      let : (integralOperationsLevelPullback l E f n).Additive :=
        PrimitiveCounit.levelAdditive l E f n
      let : PreservesFiniteLimits (integralOperationsLevelPullback l E f n) :=
        PrimitiveCounit.levelLimits l E f n
      let : PreservesFiniteColimits (integralOperationsLevelPullback l E f n) :=
        PrimitiveCounit.levelColimits l E f n
      let : (integralOperationsLevelPullback l E h n).Additive :=
        PrimitiveCounit.levelAdditive l E h n
      let : PreservesFiniteLimits (integralOperationsLevelPullback l E h n) :=
        PrimitiveCounit.levelLimits l E h n
      let : PreservesFiniteColimits (integralOperationsLevelPullback l E h n) :=
        PrimitiveCounit.levelColimits l E h n
      let : (integralOperationsLevelPullback l E (h ≫ f) n).Additive :=
        PrimitiveCounit.levelAdditive l E (h ≫ f) n
      let : PreservesFiniteLimits (integralOperationsLevelPullback l E (h ≫ f) n) :=
        PrimitiveCounit.levelLimits l E (h ≫ f) n
      let : PreservesFiniteColimits (integralOperationsLevelPullback l E (h ≫ f) n) :=
        PrimitiveCounit.levelColimits l E (h ≫ f) n
      let := coefficientSequenceEvaluation_additiveInstance l E Y n
      let := coefficientSequenceEvaluation_additiveInstance l E X n
      let := coefficientSequenceEvaluation_additiveInstance l E Z n
      let := coefficientSequenceEvaluation_limits l E Y n
      let := coefficientSequenceEvaluation_colimits l E Y n
      let := coefficientSequenceEvaluation_limits l E X n
      let := coefficientSequenceEvaluation_colimits l E X n
      let := coefficientSequenceEvaluation_limits l E Z n
      let := coefficientSequenceEvaluation_colimits l E Z n
      have he := reverse_square_pasting
        (p₂ := integralOperationsLevelPullback l E f n)
        (p₁ := integralOperationsLevelPullback l E h n)
        (p₁₂ := integralOperationsLevelPullback l E (h ≫ f) n)
        (ordinaryEvaluation l E f n).symm
        (ordinaryEvaluation l E h n).symm
        (ordinaryEvaluation l E (h ≫ f) n).symm
        (Scheme.coefficientModulePullbackComposition h f
          (CommRingCat.of (ULift.{t + 1}
            (Padic.coefficientExtensionRing l E (n + 1)))))
        (integralComparisonSequenceComposition l E h f)
        (ordinaryCompositionEvaluation l E h f n) A
      simpa only [evaluation, finiteComposition, square_inverse,
        integralComparisonSystemComposition, Functor.mapDerivedCategoryTriangleIso,
        integralComparisonDerivedSequencePullback, coefficientSequenceDerivedEvaluation]
        using he
    · intro A hA m n q
      exact (coefficientSequenceDerivedTransition l E Z q).naturality _
    · intro A hA m n q
      exact (coefficientSequenceDerivedTransition l E Z q).naturality _
    · intro A hA m n q
      exact (SZ.quotientCalculus.adjunction q).homEquiv_naturality_right_square
        _ _ _ _ ((coefficientSequenceDerivedTransition l E Z q).naturality _)
    · intro A hA m n q
      exact (SZ.quotientCalculus.adjunction q).homEquiv_naturality_right_square
        _ _ _ _ ((coefficientSequenceDerivedTransition l E Z q).naturality _)
  · have hstrict (P : CochainComplex (coefficientSequenceModules l E Y) ℤ) :
        (restrictionFactor l E (h ≫ f) P).symm ≪≫
          (coefficientSequenceDerivedRestriction l E Z).mapIso
            ((integralComparisonSystemComposition l E h f).app (DerivedCategory.Q.obj P)) ≪≫
          iteratedRestrictionFactor l E h f P =
        DerivedCategory.Q.mapIso (strictComposition l E h f P) := by
      apply Iso.ext
      have hfac := restriction_composition
        (integralComparisonSequencePullback l E f) (integralComparisonSequencePullback l E h)
        (integralComparisonSequencePullback l E (h ≫ f)) (coefficientSequenceRestriction l E Z)
        (integralComparisonSequenceComposition l E h f) P
      simpa only [restrictionFactor, iteratedRestrictionFactor, strictComposition,
        integralComparisonSystemComposition, coefficientSequenceDerivedRestriction,
        integralComparisonDerivedSequencePullback, PrimitiveCounit.restrictComplex,
        Iso.symm_hom, Category.assoc, Iso.trans_hom, Iso.app_hom,
        Functor.mapIso_hom, Functor.map_comp] using hfac
    refine ⟨?_, ?_⟩
    · unfold RepresentativeForward
      intro P hP
      have he := congrArg Iso.hom (hstrict P)
      simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom] at he
      rw [he]
      exact (ρZ.comparison.hom.naturality (strictComposition l E h f P).hom).symm
    · unfold RepresentativeBackward
      intro P hP
      have he := congrArg Iso.inv (hstrict P)
      simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] at he
      rw [he]
      exact (ρZ.comparison.hom.naturality (strictComposition l E h f P).inv).symm
  · refine ⟨?_, ?_, ?_⟩
    · unfold TransportReduction
      simpa only [completed, gammaSource, gammaTarget, Iso.trans_hom,
        Iso.symm_hom, Functor.mapIso_hom, Iso.app_hom, asIso_hom, asIso_inv,
        Category.assoc, Functor.id_obj] using
        counit_conjugation SZ.adjunction
          (betaSource l E h f SY rhf C) (betaTarget l E h f SY SX rf rh C)
          ((integralComparisonSystemComposition l E h f).hom.app C)
    · unfold TransportInverseReduction
      simpa only [completed, gammaSource, gammaTarget, Iso.trans_inv,
        Iso.symm_inv, Functor.mapIso_inv, Iso.app_inv, asIso_inv, asIso_hom,
        Category.assoc, Functor.id_obj] using
        counit_conjugation SZ.adjunction
          (betaTarget l E h f SY SX rf rh C) (betaSource l E h f SY rhf C)
          ((integralComparisonSystemComposition l E h f).inv.app C)
    · unfold TransportNaturality
      intro C' hC' _ _ _ _ v
      simp only [completed, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
        Iso.app_hom, asIso_hom, asIso_inv]
      apply conjugation_naturality
        (integralComparisonDerivedSequencePullback l E (h ≫ f))
        (integralComparisonDerivedSequencePullback l E f ⋙
          integralComparisonDerivedSequencePullback l E h)
        (coefficientSequenceLimit l E Z)
        (coefficientSequenceLimit l E Y ⋙ integralDerivedPullback l E (h ≫ f))
        (coefficientSequenceLimit l E Y ⋙ integralDerivedPullback l E f ⋙
          integralDerivedPullback l E h)
        (integralComparisonSystemComposition l E h f).hom v
      · simpa only [betaSource, Functor.comp_map] using
          pullBeta_naturality l E (h ≫ f) SY rhf v
      · unfold betaTarget
        have hf := congrArg (fun z ↦ (integralDerivedPullback l E h).map z)
          (pullBeta_naturality l E f SY rf v)
        have hh := pullBeta_naturality l E h SX rh
          ((integralComparisonDerivedSequencePullback l E f).map v)
        simp only [Functor.map_comp] at hf
        dsimp only [Functor.comp_map]
        erw [← Category.assoc, hf, Category.assoc, hh]
        simp only [Category.assoc]

end WeilConjectures.PullbackCompositionTransport
