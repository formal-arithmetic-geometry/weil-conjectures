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
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence
import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients

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
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace WeilConjectures.PullbackCompositionTransport

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Derived evaluation of whole-system inverse image, normalized by the ordinary units.
Source: Stacks 03D8, 0D6D
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def evaluation {X Y : Scheme.{t}} (f : X ⟶ Y) (n : ℕ) :
    PrimitiveCounit.pull l E f ⋙ coefficientSequenceDerivedEvaluation l E X n ≅
      coefficientSequenceDerivedEvaluation l E Y n ⋙
        (integralOperationsLevelPullback l E f n).mapDerivedCategory :=
  letI : (integralOperationsLevelPullback l E f n).Additive :=
    PrimitiveCounit.levelAdditive l E f n
  letI : PreservesFiniteLimits (integralOperationsLevelPullback l E f n) :=
    PrimitiveCounit.levelLimits l E f n
  letI : PreservesFiniteColimits (integralOperationsLevelPullback l E f n) :=
    PrimitiveCounit.levelColimits l E f n
  (Functor.mapDerivedCategoryCompIso (PrimitiveCounit.inverse l E f)
    (coefficientSequenceEvaluation l E X n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (PrimitiveCounit.inverseEvaluation l E f n) ≪≫
    Functor.mapDerivedCategoryCompIso (coefficientSequenceEvaluation l E Y n)
      (integralOperationsLevelPullback l E f n)

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
  Functor.mapDerivedCategoryNatIso
      (Scheme.coefficientModulePullbackComposition h f
        (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionRing l E (n + 1))))) ≪≫
    Functor.mapDerivedCategoryCompIso (integralOperationsLevelPullback l E f n)
      (integralOperationsLevelPullback l E h n)

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
      (evaluation l E h n).hom.app ((PrimitiveCounit.pull l E f).obj C) ≫
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
        (.up ℤ)).app C ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (PrimitiveCounit.inverse l E f ⋙ PrimitiveCounit.inverse l E h))
          (.up ℤ)).app C)

/-- Restriction of derived pullback agrees with restriction of its exact complex model.
Source: Stacks 0D6D, 0941
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def restrictionFactor {X Y : Scheme.{t}} (f : X ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :=
  (coefficientSequenceDerivedRestriction l E X).mapIso
      ((PrimitiveCounit.inverse l E f).mapDerivedCategoryFactors.app C) ≪≫
    (coefficientSequenceRestriction l E X).mapDerivedCategoryFactors.app _

/-- Iterated version of the same localization comparison, preserving the given parentheses.
Source: Stacks 0D6D, 0941
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def iteratedRestrictionFactor {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) :=
  (coefficientSequenceDerivedRestriction l E Z).mapIso
      ((PrimitiveCounit.pull l E h).mapIso
        ((PrimitiveCounit.inverse l E f).mapDerivedCategoryFactors.app C)) ≪≫
    restrictionFactor l E h (((PrimitiveCounit.inverse l E f).mapHomologicalComplex
      (.up ℤ)).obj C)

/-- The actual product/cone map realizes L(a), and likewise its inverse, on every
strict complex presentation, including complexes representing arbitrary input systems.
The Roos functor is the existing product map on both shifted cone coordinates.
Source: Stacks 0941; node proof step 5
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
structure RepresentativeLaws {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
    (ρ : PrimitiveCounit.RoosRealization l E Z) : Prop where
  forward : ∀ (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (_hC : IsNormalizedCoefficientSequence l E Y (DerivedCategory.Q.obj C)),
    ρ.comparison.hom.app _ ≫ (coefficientConstantTowerLimit l E Z).map
      ((restrictionFactor l E (h ≫ f) C).inv ≫
        (coefficientSequenceDerivedRestriction l E Z).map
          ((integralComparisonSystemComposition l E h f).hom.app (DerivedCategory.Q.obj C)) ≫
        (iteratedRestrictionFactor l E h f C).hom) =
      DerivedCategory.Q.map (roosF.map (strictComposition l E h f C).hom) ≫
        ρ.comparison.hom.app _
  backward : ∀ (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
    (_hC : IsNormalizedCoefficientSequence l E Y (DerivedCategory.Q.obj C)),
    ρ.comparison.hom.app _ ≫ (coefficientConstantTowerLimit l E Z).map
      ((iteratedRestrictionFactor l E h f C).inv ≫
        (coefficientSequenceDerivedRestriction l E Z).map
          ((integralComparisonSystemComposition l E h f).inv.app (DerivedCategory.Q.obj C)) ≫
        (restrictionFactor l E (h ≫ f) C).hom) =
      DerivedCategory.Q.map (roosF.map (strictComposition l E h f C).inv) ≫
        ρ.comparison.hom.app _

variable {X Y Z : Scheme.{t}} (h : Z ⟶ X) (f : X ⟶ Y)
  (SY : CoefficientDerivedSystemReduction l E Y)
  (SX : CoefficientDerivedSystemReduction l E X)
  (SZ : CoefficientDerivedSystemCalculus l E Z)
  (rf : integralDerivedPullback l E f ≅
    SY.reduction ⋙ PrimitiveCounit.pull l E f ⋙ coefficientSequenceLimit l E X)
  (rh : integralDerivedPullback l E h ≅
    SX.reduction ⋙ PrimitiveCounit.pull l E h ⋙ coefficientSequenceLimit l E Z)
  (rhf : integralDerivedPullback l E (h ≫ f) ≅
    SY.reduction ⋙ PrimitiveCounit.pull l E (h ≫ f) ⋙ coefficientSequenceLimit l E Z)

/-- Recursive comparison for P=F_(f h)(C); the input comparison is the identity.
Source: node recursive beta formula and proof step 4
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def betaSource (C : coefficientSequenceDerived l E Y) :=
  PrimitiveCounit.pullBeta l E (h ≫ f) SY rhf C

/-- Recursive comparison for Q=F_h(F_f(C)), applying the inner beta before outer beta.
Source: node recursive beta formula and proof step 4
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
def betaTarget (C : coefficientSequenceDerived l E Y) :=
  (integralDerivedPullback l E h).map (PrimitiveCounit.pullBeta l E f SY rf C) ≫
    PrimitiveCounit.pullBeta l E h SX rh ((PrimitiveCounit.pull l E f).obj C)

/-- Coherent reduction of beta_P followed by the one whole-system counit.
Source: node gamma formula (blueprint: lem-pur-normalized-pullback-composition-transport). -/
def gammaSource (C : coefficientSequenceDerived l E Y) :=
  SZ.reduction.map (betaSource l E h f SY rhf C) ≫
    SZ.adjunction.counit.app ((PrimitiveCounit.pull l E (h ≫ f)).obj C)

/-- Coherent reduction of beta_Q followed by that same counit.
Source: node gamma formula (blueprint: lem-pur-normalized-pullback-composition-transport). -/
def gammaTarget (C : coefficientSequenceDerived l E Y) :=
  SZ.reduction.map (betaTarget l E h f SY SX rf rh C) ≫
    SZ.adjunction.counit.app ((PrimitiveCounit.pull l E h).obj
      ((PrimitiveCounit.pull l E f).obj C))

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

/-- Transport equations and naturality, retaining the actual reduced system morphisms.
Source: node proof steps 4--6
(blueprint: lem-pur-normalized-pullback-composition-transport). -/
structure TransportLaws (C : coefficientSequenceDerived l E Y)
    [IsIso (betaSource l E h f SY rhf C)]
    [IsIso (betaTarget l E h f SY SX rf rh C)] : Prop where
  reduction : SZ.reduction.map (completed l E h f SY SX rf rh rhf C).hom ≫
      gammaTarget l E h f SY SX SZ rf rh C =
    gammaSource l E h f SY SZ rhf C ≫ (integralComparisonSystemComposition l E h f).hom.app C
  inverse_reduction : SZ.reduction.map (completed l E h f SY SX rf rh rhf C).inv ≫
      gammaSource l E h f SY SZ rhf C =
    gammaTarget l E h f SY SX SZ rf rh C ≫ (integralComparisonSystemComposition l E h f).inv.app C
  naturality : ∀ (C' : coefficientSequenceDerived l E Y)
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

/-- Canonical pullback composition on arbitrary normalized whole systems, and its
transport through the actual quotient-complex/Roos realization. Realization parameters
are the dependency's normalized presentations, not arbitrary comparison maps.
Source: Stacks Project, sites-modules.tex Tag 03D8; sites-cohomology.tex Tags 0D6D,
0941 (blueprint: lem-pur-normalized-pullback-composition-transport).
Proof, following the node's six steps:
1. The finite compositor is the mate of direct-image fibre-product pasting. Exact
finite module inverse image derives it termwise. On scalar generators its inverse
multiplies the two scalar factors and its forward map inserts 1. Balancing proves
both inverse equations; the insertion unit fixes the adjunction normalization.
2. Quotient reduction before or after multiplication gives the same scalar,
since the constant-section coefficient maps commute with every quotient. Apply
lem-pur-cochain-pullback-tensor-coherence on flat-term K-flat representatives.
3. Compose this square with naturality at the actual input transition adjunct
alpha. Under extension/restriction adjunction this is compatibility with
Res(alpha) after the unit, for every m>=n including equality. The ordinary
whole-system adjunction constructs the map before evaluation; its localization
is integralComparisonSystemComposition. Its evaluated normalization is finite.
The same calculation for the inverse gives both inverse transition equations.
4. Specialize recursive beta to the two displayed expressions. Each primitive
is realization followed by L of the image of the coherent counit, exactly
PrimitiveCounit.pullBeta. Conjugate L of the system compositor as in completed.
Cancellation gives its inverse beta_P inverse, then L(a inverse), then beta_Q.
5. On restricted strict towers, the products of the finite compositor maps
commute with 1-shift. Apply the product map to both coordinates of Cone(1-s)[-1].
The inverse product map is its inverse. The normalized projection-compatible
Roos realization carries this strict map to L(a), also on system resolutions.
The three PullModel hypotheses fix these comparisons on actual quotient models;
lem-pur-integral-operations-well-defined supplies their localization compatibility.
6. Naturality of the one system counit gives e_Q R L(a)=a e_P. Apply R to the
conjugation identity and substitute gamma=e R(beta), obtaining reduction.
Apply the same calculation to a inverse for inverse_reduction. Naturality of
all primitive comparisons and their inverses proves naturality in C. These are
equations of whole-system maps, so keep all actual quotient transitions; no
faithfulness of evaluation and no inverse-image/product interchange is used. -/
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
  sorry

end WeilConjectures.PullbackCompositionTransport
