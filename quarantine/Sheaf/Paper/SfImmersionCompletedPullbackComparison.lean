/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q53
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Sheaf.Paper.PbcActualStrictPullback
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
public import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
public import Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison

import Sheaf.Paper.AdicCoefficientDatum
import Sheaf.Paper.IntrinsicCompletionCompleted
import Sheaf.Paper.ProEtaleConstructibleOrigin
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.Paper.ConstantCompletionEquivalence
import Sheaf.AlgebraicGeometry.ProfiniteCoefficientInverseImage
import Sheaf.AlgebraicGeometry.PullbackBoundedConstructible
import Sheaf.Paper.WeilCompletedTensorReflector
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.CategoryTheory.DerivedCategory.StandardQuotientsPerfect
import Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Sheaf.Paper.PbcQbarCompletedPullback

/-!
# Ordinary immersion pullback and strict completed pullback

Source: smooth-purity localization, returned proof Step 6; Stacks proetale.tex,
Tags 09AA, 099M and 099N (2),(5)
(blueprint: lem-sf-immersion-completed-pullback-comparison).

The coefficient identifications below only transport the two published presentations
of the same quotient system. All comparisons are normalized by their quotient maps,
universal derived counits, or the two coordinates of a strict Roos complex.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale WeilConjectures

namespace AlgebraicGeometry.Scheme
namespace ImmersionCompletedPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The unique size-change identification of the actual positive quotient rings.
Source: coefficient identification in localization Step 6
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: quotient induction defines the displayed map and its inverse from ULift.down;
the principal ideal powers correspond under ULift.ringEquiv. The formula on quotient
representatives proves both inverse identities and uniqueness. -/
theorem quotientEquiv_exists (n : ℕ) :
    ∃! e : PbcQuotient (pbcIntegralDatum l E) n ≃+*
        ULift.{u + 1} (Padic.coefficientExtensionRing l E (n + 1)),
      ∀ a : PbcIntegralRing l E,
        e (Ideal.Quotient.mk ((pbcIntegralDatum l E).ideal ^ (n + 1)) a) =
          ULift.up (Ideal.Quotient.mk (Padic.coefficientExtensionIdeal l E (n + 1)) a.down) := by
  sorry

/-- Canonical quotient size transport, fixed on every quotient representative.
Source: localization Step 6
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def quotientEquiv (n : ℕ) := (quotientEquiv_exists l E n).exists.choose

/-- Canonical finite coefficient sheaf identification, retaining commutativity.
Source: localization Step 6, finite projections
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def finiteRingIso (T : Scheme.{u}) (n : ℕ) :
    (pbcAdicRings T (pbcIntegralDatum l E)).obj (op n) ≅
      integralCoefficientCommRingSheaf l E T n :=
  (pbcLevelConstantComparison T (pbcIntegralDatum l E) n).symm ≪≫
    (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).mapIso
      (quotientEquiv l E n).toCommRingCatIso

/-- The two completed rings have the unique identification with these finite projections.
Source: localization Step 6, coefficient inverse-image normalization
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: the finiteRingIso maps intertwine every quotient homomorphism, by quotient
induction. Their limits give the isomorphism. The limit projections are jointly
monic, proving the displayed normalization and uniqueness. -/
theorem completedRingIso_exists (T : Scheme.{u}) :
    ∃! e : pbcAdicCompletion T (pbcIntegralDatum l E) ≅
        completedIntegralCommRingSheafUnrestricted l E T,
      ∀ n : ℕ, e.hom ≫ completedIntegralCommRingProjectionUnrestricted l E T n =
        pbcAdicProjection T (pbcIntegralDatum l E) n ≫ (finiteRingIso l E T n).hom := by
  sorry

/-- The projection-normalized identification of the two completed coefficient sheaves.
Source: localization Step 6
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def completedRingIso (T : Scheme.{u}) := (completedRingIso_exists l E T).exists.choose

/-- Exact coefficient transport to the recorded integral module category.
Source: localization Step 6, completed coefficients
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
abbrev transport (T : Scheme.{u}) :
    PbcCompletedDerived T (pbcIntegralDatum l E) ⥤
      DerivedCategory (scalarReductionSource.{u, u} l E T) :=
  pbcDerivedRestrict (completedRingIso l E T).inv

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- Equality of the two specified ordinary tensor-pullback objects.
Source: localization Step 6, Step 1; Stacks 03EK
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: the coefficient maps have the same finite projections, hence are equal.
The recorded scalar-extension functor has changeOfRings as its actual objects;
substitution identifies the displayed objects. -/
theorem moduleObj_eq (M : pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))) :
    (pbcActualModulePull f (pbcIntegralDatum l E)).obj M =
      (proEtaleRingModulePullback f _ _ ((pbcIntegralDatum l E).integralRingIso f)).obj M := by
  sorry

/-- The object identifications intertwine the actual tensor maps.
Source: localization Step 6, Step 1
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: both maps act as identity on the coefficient tensor factor and as inverse
image of the supplied arrow on the module factor; tensor generators give equality. -/
theorem moduleObj_eq_naturality
    {M N : pbcModules X (pbcAdicCompletion X (pbcIntegralDatum l E))} (a : M ⟶ N) :
    (pbcActualModulePull f (pbcIntegralDatum l E)).map a ≫
        eqToHom (moduleObj_eq l E f N) =
      eqToHom (moduleObj_eq l E f M) ≫
        (proEtaleRingModulePullback f _ _ ((pbcIntegralDatum l E).integralRingIso f)).map a := by
  sorry

/-- The identity-on-tensor-data ordinary pullback identification.
Source: localization Step 6, Step 1
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def moduleIso : pbcActualModulePull f (pbcIntegralDatum l E) ≅
    proEtaleRingModulePullback f _ _ ((pbcIntegralDatum l E).integralRingIso f) :=
  NatIso.ofComponents (fun M ↦ eqToIso (moduleObj_eq l E f M))
    (fun a ↦ moduleObj_eq_naturality l E f a)

/-- Exact descent is the ordinary left derived pullback with its original counit.
Source: localization Step 6, Step 1; Stacks 06YY
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: exact inverse image sends every quasi-isomorphism to a quasi-isomorphism.
On a K-flat representative both counits identify the same termwise tensor complex,
through moduleIso. The universal left-derived property extends this equation
uniquely and supplies an inverse on every object. -/
theorem derivedIso_exists :
    ∃! e : pbcActualDerivedPull f (pbcIntegralDatum l E) ≅
        (pbcIntegralDatum.{u} l E).pull.{u} f,
      whiskerLeft DerivedCategory.Qh e.hom ≫
          (proEtaleRingModulePullback f _ _
            ((pbcIntegralDatum l E).integralRingIso f)).mapDerivedCategoryFactorsh.hom =
        pbcActualPullCounit f (pbcIntegralDatum l E) ≫
          whiskerRight (NatTrans.mapHomotopyCategory (moduleIso l E f).hom (.up ℤ))
            DerivedCategory.Qh := by
  sorry

/-- The counit-normalized comparison Lu* = u*, with u* computed termwise.
Source: localization Step 6, Step 1
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def derivedIso := (derivedIso_exists l E f).exists.choose

/-- The canonical finite-ring-linear tensor comparison, transported to the actual Lu*.
Source: localization Step 6, Step 2
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def finiteComparison (n : ℕ) :
    (pbcIntegralDatum l E).reduction X n ⋙ (pbcIntegralDatum l E).finitePull f n ≅
      pbcActualDerivedPull f (pbcIntegralDatum l E) ⋙ (pbcIntegralDatum l E).reduction Y n :=
  (pbcIntegralDatum l E).chi f n ≪≫
    isoWhiskerRight (derivedIso l E f).symm ((pbcIntegralDatum l E).reduction Y n)

/-- A reduction with its completed scalar action retained.
Source: localization Step 6, Step 2
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
abbrev restrictedReduction (T : Scheme.{u}) (n : ℕ) :=
  (pbcIntegralDatum l E).reduction T n ⋙
    pbcDerivedRestrict ((pbcIntegralDatum l E).projection T n)

/-- The canonical tensor-unit map to a finite reduction.
Source: localization Step 6, Step 2
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def reductionUnit (T : Scheme.{u}) (n : ℕ) :=
  (pbcDerivedScalarAdjunction ((pbcIntegralDatum l E).projection T n)).unit

/-- All quotient transitions, including equal indices and successive quotients.
Source: localization Step 6, Steps 2 and 5
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def reductionTransition (T : Scheme.{u}) (b a : ℕ) (h : a ≤ b)
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    (restrictedReduction l E T b).obj K ⟶ (restrictedReduction l E T a).obj K :=
  (pbcDerivedRestrict (pbcAdicProjection T (pbcIntegralDatum l E) b)).map
      (pbcReductionTransition (pbcAdicProjection T (pbcIntegralDatum l E) b)
        (pbcAdicQuotient T (pbcIntegralDatum l E) b a h)
        (pbcAdicProjection T (pbcIntegralDatum l E) a)
        (pbcAdicProjection_comp T (pbcIntegralDatum l E) b a h) K) ≫
    (pbcDerivedRestrictComp (pbcAdicProjection T (pbcIntegralDatum l E) b)
      (pbcAdicQuotient T (pbcIntegralDatum l E) b a h)
      (pbcAdicProjection T (pbcIntegralDatum l E) a)
      (pbcAdicProjection_comp T (pbcIntegralDatum l E) b a h)).hom.app
        (((pbcIntegralDatum l E).reduction T a).obj K)

/-- Restrict the canonical finite-ring-linear comparison to completed coefficients.
Source: localization Step 6, Steps 2 and 5
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def restrictedComparison (n : ℕ) :
    restrictedReduction l E X n ⋙ (pbcIntegralDatum l E).pull f ≅
      (pbcIntegralDatum l E).pull f ⋙ restrictedReduction l E Y n :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft ((pbcIntegralDatum l E).reduction X n)
      (proEtaleRingRestrictionDerivedPullback f _ _ _ _
        ((pbcIntegralDatum l E).projection X n) ((pbcIntegralDatum l E).projection Y n)
        ((pbcIntegralDatum l E).integralRingIso f)
        ((pbcIntegralDatum l E).finiteRingIso f n)
        ((pbcIntegralDatum l E).projection_comm f n)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight ((pbcIntegralDatum l E).chi f n)
      (pbcDerivedRestrict ((pbcIntegralDatum l E).projection Y n)) ≪≫
    Functor.associator _ _ _

/-- The finite comparison respects its units and every quotient transition and composite.
Source: localization Step 6, Steps 2 and 5
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: on a flat-term K-flat representative both sides are the balancing map on
pure tensors. The coefficient quotient maps carry 1 to 1 and compose as their
quotient homomorphisms. Therefore the unit square, each transition square and
all successive quotient squares commute before localization. -/
theorem finite_compatibility :
    (∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (n : ℕ),
      ((pbcIntegralDatum l E).pull f).map ((reductionUnit l E X n).app K) ≫
          (restrictedComparison l E f n).hom.app K =
        (reductionUnit l E Y n).app (((pbcIntegralDatum l E).pull f).obj K)) ∧
    (∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (b a : ℕ) (h : a ≤ b),
      ((pbcIntegralDatum l E).pull f).map (reductionTransition l E X b a h K) ≫
          (restrictedComparison l E f a).hom.app K =
        (restrictedComparison l E f b).hom.app K ≫
          reductionTransition l E Y b a h (((pbcIntegralDatum l E).pull f).obj K)) ∧
    (∀ (T : Scheme.{u}) (K : PbcCompletedDerived T (pbcIntegralDatum l E))
        (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c),
      reductionTransition l E T c b hbc K ≫ reductionTransition l E T b a hab K =
        reductionTransition l E T c a (hab.trans hbc) K) := by
  sorry

/-- Evaluation of tower pullback is ordinary pullback of the evaluated tower.
Source: localization Step 6, Step 2
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: whiskering and evaluation have identical objects and maps. Functor
extensionality identifies these functors, including their structural proofs. -/
theorem moduleTowerEvaluation_eq (n : ℕ) :
    (pbcIntegralDatum l E).towerModulePull f ⋙
        reductionTowerEvaluation Y
          (reductionModuleRing Y ((pbcIntegralDatum l E).completedRing Y)) n =
      reductionTowerEvaluation X
        (reductionModuleRing X ((pbcIntegralDatum l E).completedRing X)) n ⋙
        proEtaleRingModulePullback f _ _ ((pbcIntegralDatum l E).integralRingIso f) := by
  sorry

/-- Derive the identity-on-levels evaluation comparison.
Source: localization Step 6, Step 2
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def towerEvaluationIso (n : ℕ) :=
  (Functor.mapDerivedCategoryCompIso ((pbcIntegralDatum l E).towerModulePull f)
    (reductionTowerEvaluation Y
      (reductionModuleRing Y ((pbcIntegralDatum l E).completedRing Y)) n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (eqToIso (moduleTowerEvaluation_eq l E f n)) ≪≫
    Functor.mapDerivedCategoryCompIso
      (reductionTowerEvaluation X
        (reductionModuleRing X ((pbcIntegralDatum l E).completedRing X)) n)
      (proEtaleRingModulePullback f _ _ ((pbcIntegralDatum l E).integralRingIso f))

/-- The actual finite projection from the pulled-back strict quotient tower limit.
Source: localization Step 6, Steps 4 and 5
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def completedProjection
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (n : ℕ) :
    ((pbcIntegralDatum l E).completedPull f).obj K ⟶
      ((pbcIntegralDatum l E).pull f).obj ((restrictedReduction l E X n).obj K) :=
  (completedRlimProjection Y ((pbcIntegralDatum l E).completedRing Y) n).app
      (((pbcIntegralDatum l E).towerPull f).obj
        ((completedReductionTower X (pbcIntegralDatum l E)).obj K)) ≫
    (towerEvaluationIso l E f n).hom.app
      ((completedReductionTower X (pbcIntegralDatum l E)).obj K) ≫
    ((pbcIntegralDatum l E).pull f).map
      ((completedReductionEvaluation X (pbcIntegralDatum l E) n).app K)

/-- Finite projections preserve the specified completion unit and all quotient maps.
Source: localization Step 6, Step 5
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: the derived constant-tower adjunction takes the augmentation to the unit.
Its evaluation is the scalar-extension unit. Naturality of the actual Rlim
projections gives the transition equation, including equal and successive indices. -/
theorem completedProjection_compatibility :
    (∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (n : ℕ),
      (pbcIntegralDatum l E).ordinaryToCompleted f K ≫ completedProjection l E f K n =
        ((pbcIntegralDatum l E).pull f).map ((reductionUnit l E X n).app K)) ∧
    (∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (b a : ℕ) (h : a ≤ b),
      completedProjection l E f K b ≫
          ((pbcIntegralDatum l E).pull f).map (reductionTransition l E X b a h K) =
        completedProjection l E f K a) := by
  sorry

/-- Identify the two strict constructions by their specified augmentation units.
Source: localization Step 6, Steps 2 and 5
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: apply moduleIso levelwise and derive its exact tower functor. The chosen
Rlim functors are the same universal right-derived limit. Their induced comparison
carries the quotient augmentation to itself, giving the displayed equation.
Completion is a reflector into complete objects, so its unit forces uniqueness. -/
theorem strictIso_exists :
    ∃! e : pbcActualStrictCompletedPull (pbcIntegralDatum l E) f ≅
        (pbcIntegralDatum l E).completedPull f,
      ∀ K : PbcCompletedDerived X (pbcIntegralDatum l E),
        (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app K ≫ e.hom.app K =
          (derivedIso l E f).hom.app K ≫ (pbcIntegralDatum l E).ordinaryToCompleted f K := by
  sorry

/-- The unit-normalized identification of the actual strict construction.
Source: localization Step 6, Step 5
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def strictIso := (strictIso_exists l E f).exists.choose

/-- The finite projection of the actual completed pullback, with its finite comparison.
Source: localization Step 6, Step 5
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def actualCompletedProjection
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (n : ℕ) :
    (pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj K ⟶
      (restrictedReduction l E Y n).obj
        ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K) :=
  (strictIso l E f).hom.app K ≫ completedProjection l E f K n ≫
    (restrictedComparison l E f n).hom.app K ≫
    (restrictedReduction l E Y n).map ((derivedIso l E f).inv.app K)

/-- The original strict comparison commutes with every actual finite projection.
Source: localization Step 6, Steps 2 and 5
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: combine the defining unit equation of strictIso with the unit square of
finite_compatibility and completedProjection_compatibility. Naturality of the
quotient units under derivedIso gives the first equality. The transition square
of finite_compatibility and naturality under the same isomorphism give the second,
for all quotients, including equal and successive indices. -/
theorem actualCompletedProjection_compatibility :
    (∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (n : ℕ),
      (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app K ≫
          actualCompletedProjection l E f K n =
        (reductionUnit l E Y n).app
          ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K)) ∧
    (∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (b a : ℕ) (h : a ≤ b),
      actualCompletedProjection l E f K b ≫ reductionTransition l E Y b a h
          ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K) =
        actualCompletedProjection l E f K a) := by
  sorry

/-- The right mate of the identity-on-constant-towers inverse-image comparison.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def rlimComparison
    (M : DerivedCategory (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E)))) :
    ((pbcIntegralDatum l E).pull f).obj
        ((completedRlim X ((pbcIntegralDatum l E).completedRing X)).obj M) ⟶
      (completedRlim Y ((pbcIntegralDatum l E).completedRing Y)).obj
        (((pbcIntegralDatum l E).towerPull f).obj M) :=
  ((pbcIntegralDatum l E).constantRlimAdjunction Y).unit.app _ ≫
    (completedRlim Y ((pbcIntegralDatum l E).completedRing Y)).map
      (((pbcIntegralDatum l E).derivedConstantPullbackIso f).inv.app _ ≫
        ((pbcIntegralDatum l E).towerPull f).map
          (((pbcIntegralDatum l E).constantRlimAdjunction X).counit.app M))

/-- The canonical completion comparison factors through this actual Rlim mate.
Source: localization Step 6, Step 5
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: expand the two constant-tower adjunction units and apply the triangle
identity. Naturality with the quotient augmentation gives precisely this equation. -/
theorem ordinaryToCompleted_eq (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :
    (pbcIntegralDatum l E).ordinaryToCompleted f K =
      ((pbcIntegralDatum l E).pull f).map ((pbcIntegralDatum l E).completionUnit X K) ≫
        rlimComparison l E f ((completedReductionTower X (pbcIntegralDatum l E)).obj K) := by
  sorry

/-- The ordinary module inverse image with canonical completed coefficients.
Source: localization Step 6, Step 1
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
abbrev modulePull := proEtaleRingModulePullback f _ _
  ((pbcIntegralDatum l E).integralRingIso f)

/-- Apply the specified ordinary inverse image to all terms of a complex.
Source: localization Step 6, Step 1
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
abbrev complexPull := (modulePull l E f).mapHomologicalComplex (.up ℤ)

/-- Apply the same inverse image to every level and transition of a strict tower complex.
Source: localization Step 6, Steps 2 and 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
abbrev towerComplexPull :=
  ((Functor.whiskeringRight ℕᵒᵖ _ _).obj (modulePull l E f)).mapHomologicalComplex (.up ℤ)

/-- Evaluation commutes with applying inverse image term by term.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: both complexes have inverse image of M_n in every degree and inverse image
of its differential; their chain maps and differential proofs agree by extensionality. -/
theorem complexEvaluation_eq
    (M : CochainComplex (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ)
    (n : ℕ) :
    (complexPull l E f).obj (M.asFunctor.obj (op n)) =
      ((towerComplexPull l E f).obj M).asFunctor.obj (op n) := by
  sorry

/-- The actual product comparison, determined by its projections.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def productComparison
    (M : CochainComplex (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ) :
    (complexPull l E f).obj (strictRoosProduct M) ⟶
      strictRoosProduct ((towerComplexPull l E f).obj M) :=
  Pi.lift (f := fun n : ℕ ↦
    ((towerComplexPull l E f).obj M).asFunctor.obj (op n))
    (fun n : ℕ ↦ (complexPull l E f).map
    (Pi.π (fun k : ℕ ↦ M.asFunctor.obj (op k)) n) ≫
      eqToHom (complexEvaluation_eq l E f M n))

/-- The coordinatewise Roos comparison, uniquely normalized by the product map.
Source: localization Step 6, Step 4; Stacks 08TC
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: inverse image preserves countable products for an immersion. Its product
comparison intertwines 1-s, since each projection gives the same pulled-back
transition. In the two Roos coordinates use this comparison on each factor.
The differentials (-dy-(1-s)x,dx) commute with this map; the inverse uses the
inverse product comparison. The coordinates jointly determine the chain map. -/
theorem roosIso_exists [IsImmersion f]
    (M : CochainComplex (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ) :
    ∃! e : (complexPull l E f).obj (strictRoosComplex M) ≅
        strictRoosComplex ((towerComplexPull l E f).obj M),
      ∀ p : ℤ, e.hom.f (p + 1) ≫
          (strictRoosCoordinates ((towerComplexPull l E f).obj M) p).hom =
        (modulePull l E f).map (strictRoosCoordinates M p).hom ≫
          biprodComparison (modulePull l E f) _ _ ≫
            biprod.map ((productComparison l E f M).f p)
              ((productComparison l E f M).f (p + 1)) := by
  sorry

/-- The strict Roos isomorphism; its data is fixed on both product coordinates.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def roosIso [IsImmersion f]
    (M : CochainComplex (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ) :=
  (roosIso_exists l E f M).exists.choose

/-- A map of strict towers gives the uniquely coordinate-normalized Roos map.
Source: localization Step 6, Step 4; Stacks 08TC
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: naturality intertwines the two transition endomorphisms. Apply the shifted
mapping-cone construction; its two coordinates give the formula and uniqueness. -/
theorem roosMap_exists (T : Scheme.{u})
    {M N : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ}
    (a : M ⟶ N) :
    ∃! b : strictRoosComplex M ⟶ strictRoosComplex N,
      ∀ p : ℤ, b.f (p + 1) ≫ (strictRoosCoordinates N p).hom =
        (strictRoosCoordinates M p).hom ≫
          biprod.map ((strictRoosProductMap a).f p) ((strictRoosProductMap a).f (p + 1)) := by
  sorry

/-- The strict map of the actual shifted Roos cones.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def roosMap (T : Scheme.{u})
    {M N : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ}
    (a : M ⟶ N) := (roosMap_exists l E T a).exists.choose

/-- The limit embeds into Roos by its zero and compatible-sequence coordinates.
Source: localization Step 6, Step 4; Stacks 07KC
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: a compatible sequence is killed by 1-s. Therefore these coordinates commute
with the displayed Roos differential; the coordinates also give uniqueness. -/
theorem roosInclusion_exists (T : Scheme.{u})
    (I : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :
    ∃! a : limit I.asFunctor ⟶ strictRoosComplex I,
      ∀ p : ℤ, a.f (p + 1) ≫ (strictRoosCoordinates I p).hom =
        biprod.lift 0 ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) := by
  sorry

/-- The compatible-sequence inclusion, fixed on both cone coordinates.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def roosInclusion (T : Scheme.{u})
    (I : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :=
  (roosInclusion_exists l E T I).exists.choose

/-- The termwise limit and the limit of evaluated complexes have the same projections.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: limits of complexes are computed degreewise. Their universal property in
each degree gives this chain isomorphism and determines it by its projections. -/
theorem termwiseLimitIso_exists (T : Scheme.{u})
    (I : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :
    ∃! e : (Functor.mapHomologicalComplex
        (completedTowerLimit T ((pbcIntegralDatum l E).completedRing T))
        (.up ℤ)).obj I ≅ limit I.asFunctor,
      ∀ (n : ℕ) (p : ℤ), e.hom.f p ≫ (limit.π I.asFunctor (op n)).f p =
        limit.π (I.X p) (op n) := by
  sorry

/-- The projection-normalized comparison of the two ordinary limit computations.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def termwiseLimitIso (T : Scheme.{u})
    (I : CochainComplex (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) :=
  (termwiseLimitIso_exists l E T I).exists.choose

/-- Roos computes the recorded Rlim, naturally and with its universal derived unit.
Source: localization Step 6, Step 4; Stacks 07KC and 08TC
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: strictRoosDerivedLimitComparison makes the inclusion a quasi-isomorphism
on a K-injective tower. The universal derived unit identifies its ordinary limit
with Rlim. Every tower has a K-injective resolution; exact countable products make
Roos carry its quasi-isomorphism to a quasi-isomorphism. Descend the normalized
zigzag along that resolution. Naturality and the formula on K-injectives force
uniqueness, independently of the chosen resolution. -/
theorem roosRlim_exists (T : Scheme.{u}) :
    ∃! e : ∀ M : CochainComplex
        (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ,
        DerivedCategory.Q.obj (strictRoosComplex M) ≅
          (completedRlim T ((pbcIntegralDatum l E).completedRing T)).obj
            (DerivedCategory.Q.obj M),
      (∀ (M N : CochainComplex
          (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) (a : M ⟶ N),
        DerivedCategory.Q.map (roosMap l E T a) ≫ (e N).hom =
          (e M).hom ≫ (completedRlim T ((pbcIntegralDatum l E).completedRing T)).map
            (DerivedCategory.Q.map a)) ∧
      (∀ (I : CochainComplex
          (pbcTowers T (pbcAdicCompletion T (pbcIntegralDatum l E))) ℤ) [I.IsKInjective],
        DerivedCategory.Q.map (roosInclusion l E T I) ≫ (e I).hom =
          DerivedCategory.Q.map (termwiseLimitIso l E T I).inv ≫
            (Functor.rightDerivedFunctorObjQIso
              (completedTowerLimit T ((pbcIntegralDatum l E).completedRing T)) I).inv) := by
  sorry

/-- The resolution-independent Roos identification fixed by the derived unit.
Source: localization Step 6, Step 4
(blueprint: lem-sf-immersion-completed-pullback-comparison). -/
def roosRlim (T : Scheme.{u}) := (roosRlim_exists l E T).exists.choose

/-- The actual right mate is the map induced on strict Roos coordinates.
Source: localization Step 6, Steps 4 and 5
(blueprint: lem-sf-immersion-completed-pullback-comparison).
Proof: on strict towers inverse image commutes with both Roos coordinates by
roosIso. Normalize Roos-to-Rlim by its K-injective inclusion and universal unit.
The constant-tower adjunction mate has exactly these normalized coordinates,
so naturality on resolutions gives the displayed equation. The product maps
are invertible for immersions, hence the mate is invertible as well. -/
theorem rlimComparison_roos [IsImmersion f]
    (M : CochainComplex (pbcTowers X (pbcAdicCompletion X (pbcIntegralDatum l E))) ℤ) :
    IsIso (rlimComparison l E f (DerivedCategory.Q.obj M)) ∧
      ((pbcIntegralDatum l E).pull f).map ((roosRlim l E X M).inv) ≫
          (modulePull l E f).mapDerivedCategoryFactors.hom.app (strictRoosComplex M) ≫
          DerivedCategory.Q.map (roosIso l E f M).hom ≫
          (roosRlim l E Y ((towerComplexPull l E f).obj M)).hom ≫
          (completedRlim Y ((pbcIntegralDatum l E).completedRing Y)).map
            (((pbcIntegralDatum l E).towerModulePull f).mapDerivedCategoryFactors.inv.app M) =
        rlimComparison l E f (DerivedCategory.Q.obj M) := by
  sorry

/-- Ordinary immersion inverse image is exact and preserves the specified complete
objects; the actual strict-tower unit is invertible on every derived-complete input.
The last clause uses the recorded integral category and keeps the given interval.
Source: localization Step 6; Stacks 09AA, 099M and 099N (2),(5)
(blueprint: lem-sf-immersion-completed-pullback-comparison).

Proof plan, following the node's Steps 1--6:
1. Identify completed and finite inverse-image coefficients by
   lem-weil-pbc-profinite-coefficient-inverse-image. Use
   lem-weil-pbc-proetale-immersion-limit-preservation for exactness and products;
   lem-sf-exact-functor-derived-triangulated identifies exact descent with Lu*.
2. Choose one flat-term K-flat representative. The canonical tensor-pullback
   comparisons of lem-weil-pbc-ringed-topoi-derived-tensor-pullback and
   lem-weil-pbc-ringed-topoi-module-pullback-tensor identify its strict quotient
   towers, including their augmentation and all quotient maps.
3. The finite-extension DVR gives the Noetherian adic datum (its quotients are
   finite and perfect). Use lem-weil-pbc-constant-completion-equivalence,
   lem-weil-pbc-ringed-koszul-completion-reflector and
   lem-weil-derived-limit-existence to show that the actual source completion
   unit, rather than an arbitrary isomorphism, is invertible. The signed
   Koszul-fibre-to-Roos identification carries the intrinsic unit to this unit.
4. Exact countable products (lem-weil-proetale-countable-products-exact) and
   lem-sf-strict-roos-derived-limit-comparison compute total inverse limit.
   Its inverse-image comparison is roosIso, with productComparison on both
   coordinates and the second coordinate as every finite projection.
5. The quotient augmentation is p mapped to (0,(p tensor 1)_n). Its image is
   the same augmentation for the pulled-back tower. Thus the specified strict
   completed-pullback comparison is the pullback of the source completion
   unit followed by this Roos comparison. All finite and successive quotient
   squares commute by finite_compatibility. This also gives completeness.
6. Use lem-sf-proetale-constructible-origin and
   lem-weil-pbc-pullback-preserves-bounded-constructible on every reduction.
   Each has exactly the original interval [r,s]. Together with completeness
   this is sfIntegralConstructible, with no additional boundedness condition. -/
theorem immersion_completed_pullback_comparison [IsImmersion f] :
    PreservesFiniteLimits (pbcActualModulePull f (pbcIntegralDatum l E)) ∧
    PreservesFiniteColimits (pbcActualModulePull f (pbcIntegralDatum l E)) ∧
    PreservesLimitsOfShape (Discrete ℕ) (modulePull l E f) ∧
    (∀ K : PbcCompletedDerived X (pbcIntegralDatum l E),
      IntegralOnSlice.IsComplete l E X none ((transport l E X).obj K) →
        (pbcIntegralDatum l E).TowerComplete X K ∧
        IsIso ((pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app K) ∧
        IntegralOnSlice.IsComplete l E Y none
          ((transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K))) ∧
    (∀ (K : PbcCompletedDerived X (pbcIntegralDatum l E)) (r s : ℤ),
      r ≤ s → sfIntegralConstructible l E X ((transport l E X).obj K) →
      (∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension.{u, u} l E X n).obj
          ((transport l E X).obj K)) ⊆ Set.Icc r s) →
      sfIntegralConstructible l E Y
        ((transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K)) ∧
      ∀ n : ℕ, proEtaleCohomologicalSupport
        ((scalarReductionDerivedExtension.{u, u} l E Y n).obj
          ((transport l E Y).obj ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K))) ⊆
            Set.Icc r s) := by
  sorry

end ImmersionCompletedPullback
end AlgebraicGeometry.Scheme
