/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormulaCore
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedModuleDerivedPushpull
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstructionData
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.SmoothPurityReductionTowerCurrentStatement
import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import WeilConjectures.AlgebraicGeometry.Compact.CompactSupportUniformTorBound
import WeilConjectures.AlgebraicGeometry.SpShriekTransition.ShriekNormalizedTransitionComparison
import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImage
import WeilConjectures.AlgebraicGeometry.ProEtaleCountableProductsExact
import WeilConjectures.CategoryTheory.LocalizedModuleExactForSystems
import WeilConjectures.AlgebraicGeometry.ProEtale.Ringed.ProEtaleRingedOpenExtensionProducts
import WeilConjectures.AlgebraicGeometry.ExactProductFunctorStrictLimit
import WeilConjectures.CategoryTheory.Ringed.RingedTowerPushforwardLimitComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSlicePresentation
import WeilConjectures.CategoryTheory.Diagram.DiagramRingRestrictionPushforward
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowers
import WeilConjectures.AlgebraicGeometry.Cartesian.CartesianCoefficients
import WeilConjectures.Algebra.Homology.RingedOpenScalar.RingedOpenScalarAdjunction
import WeilConjectures.ProperBaseChange.RingedToposDerivedPushforwardComposition
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek

/-!
# Normalized image towers and canonical integral reconstruction

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/
sk-prop-sp-integral-adjunction/sk-prop-sp-integral-adjunction-direct-image.proof.md,
paragraphs (1)--(2) (blueprint: lem-sp-integral-tower-image-reconstruction).

All natural indices represent positive exponents `n+1`. The geometric scalar
comparison is fixed on ordinary tensor generators and K-flat representatives by
the quotient-tensor and representative equations below. Its right mate is the proper/open limit
comparison. Applying
that mate to the input completion unit defines reconstruction. The comparison of
whole towers is then defined by the actual reduction/limit counit.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The existing integral internal-module derived category.
Source: blueprint, R_T (blueprint: lem-sp-integral-tower-image-reconstruction). -/
abbrev Integral (T : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (spIntegralCondensed l E) T))

/-- The existing constant-model bounded constructible full subcategory.
Source: blueprint, Dbc (blueprint: lem-sp-integral-tower-image-reconstruction). -/
abbrev Constructible (T : Scheme.{u}) :=
  ConstantModelBoundedConstructible (spIntegralCondensed l E) T

/-- The exact section/internal derived equivalence, retaining every module section.
Source: blueprint, the sectionwise coefficient presentation
(blueprint: lem-sp-integral-tower-image-reconstruction). -/
def sectionEquivalence (T : Scheme.{u}) :
    Integral l E T ≌ DerivedCategory (spIntegralSectionModules l E T) :=
  letI := Functor.additive_of_preserves_binary_products
    (spIntegralModuleEquivalence l E T).functor
  (spIntegralModuleEquivalence l E T).mapDerivedCategory

/-- The already recorded separately derived compactification composite Rp_* D(j_!).
Source: blueprint, clause (2) (blueprint: lem-sp-integral-tower-image-reconstruction). -/
abbrev shriek {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Integral l E X ⥤ Integral l E Y :=
  CondensedRing.rightDerivedLowerShriekOfCompactification (spIntegralCondensed l E) c

/-- The existing derived module inverse image; no completion is applied.
Source: blueprint, clause (3) (blueprint: lem-sp-integral-tower-image-reconstruction). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Integral l E Y ⥤ Integral l E X :=
  CondensedRing.moduleObjectDerivedPullback (spIntegralCondensed l E) f

/-- Additivity of the sectionwise equivalence, used for its complex functor.
Source: blueprint, coefficient presentation (blueprint: lem-sp-integral-tower-image-reconstruction).
-/
instance sectionFunctorAdditive (T : Scheme.{u}) :
    (spIntegralModuleEquivalence l E T).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Integral module sheaves before localization.
Source: blueprint, R_T modules (blueprint: lem-sp-integral-tower-image-reconstruction). -/
abbrev Modules (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (spIntegralCondensed l E) T)

/-- The canonical pullback comparison on an actual complex.
Source: blueprint, uncompleted inverse image
(blueprint: lem-sp-integral-tower-image-reconstruction). -/
def pullComplexComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (Modules l E Y) ℤ) :
    (pull l E f).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((CondensedRing.upperStar (spIntegralCondensed l E) f).mapHomologicalComplex
          (.up ℤ)).obj P) :=
  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
    (spIntegralCondensed l E) f).app (DerivedCategory.Q.obj P) ≪≫
    (CondensedRing.upperStar (spIntegralCondensed l E) f).mapDerivedCategoryFactors.app P

/-- Evaluation is the localization of the ordinary quotient-tensor comparison.
This pins the finite quotient units to the same reduction counit on all cochain
representatives, rather than allowing an unrelated natural automorphism of an
already derived evaluation. Source: paragraph (2), scalar and unit normalization
(blueprint: lem-sp-integral-tower-image-reconstruction). -/
def IsEvaluationNormalized (T : Scheme.{u}) (D : SpCoefficientTowersAbelian l E T)
    (r : SpReductionTowerConstruction l E T D) : Prop :=
  letI := D.hasDerived
  letI := D.equivalenceAdditive
  letI := r.additive
  ∀ n : ℕ,
    letI := D.evaluationLimits n
    letI := D.evaluationColimits n
    letI : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
      Functor.additive_of_preserves_binary_products _
    ∀ P : CochainComplex (spIntegralSectionModules l E T) ℤ,
      (r.evaluation n).hom.app (DerivedCategory.Q.obj P) ≫
          (D.scalar (spIntegralReductionScalar l E T r.coefficient n)).model.ε.app P =
        (spDerivedCoefficientEvaluation l E T D n).map (r.counit.app P) ≫
          (spCoefficientEvaluation l E T D.equivalence n).mapDerivedCategoryFactors.hom.app
            ((r.ordinary.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex (r.level n) (.up ℤ)).hom.app P)

/-- Pinned coefficient constructions, with no constructibility or finite-Tor assertion.
Each reduction is the current construction-only record; in particular this record
does not contain `IsSpReductionConstructible`.
Source: blueprint, coefficient conventions and clause (1)
(blueprint: lem-sp-integral-tower-image-reconstruction). -/
structure Coefficients where
  towers : ∀ T : Scheme.{u}, SpCoefficientTowersAbelian l E T
  reduction : ∀ T : Scheme.{u}, SpReductionTowerConstruction l E T (towers T)
  evaluation_normalized : ∀ T : Scheme.{u},
    IsEvaluationNormalized l E T (towers T) (reduction T)
  base : SpTowerShriek.Base l E
  operations : SpTowerShriek.Operations l E base

/-- Reduction of internal integral modules, through the recorded section equivalence.
Source: blueprint, red_T (blueprint: lem-sp-integral-tower-image-reconstruction). -/
def red (s : Coefficients l E) (T : Scheme.{u}) :=
  (sectionEquivalence l E T).functor ⋙ (s.reduction T).red

/-- Exact transport between the two dependency presentations of strict derived towers.
Source: blueprint, strict tower category (blueprint: lem-sp-integral-tower-image-reconstruction). -/
abbrev realization (s : Coefficients l E) (T : Scheme.{u}) :=
  SpTowerProjection.realization l E s.base T (s.towers T)

/-- The actual tower direct image, transported from the recorded ringed sequence site.
Source: blueprint, clause (1) (blueprint: lem-sp-integral-tower-image-reconstruction). -/
def towerShriek (s : Coefficients l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :=
  (realization l E s X).functor ⋙ SpTowerShriek.F l E s.base s.operations c ⋙
    (realization l E s Y).inverse

/-- The finite reduction functor at positive level n+1.
Source: blueprint, M/ell^n (blueprint: lem-sp-integral-tower-image-reconstruction). -/
abbrev level (s : Coefficients l E) (T : Scheme.{u}) (n : ℕ) :=
  red l E s T ⋙ spDerivedCoefficientEvaluation l E T (s.towers T) n

/-- The actual finite compactification composite, in the dependency's quotient coordinates.
Source: blueprint, clause (2) (blueprint: lem-sp-integral-tower-image-reconstruction). -/
abbrev finiteShriek (s : Coefficients l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) := SpTowerShriek.finiteF l E s.base c n

/-- Additivity supplied by the existing reduction interface.
Source: blueprint, strict reduction (blueprint: lem-sp-integral-tower-image-reconstruction). -/
instance ordinaryReductionAdditive (s : Coefficients l E) (T : Scheme.{u}) :
    (s.reduction T).ordinary.Additive := (s.reduction T).additive

/-- Restriction from completed section coefficients to the actual pulled-back
integral section ring, along the recorded normalized ring isomorphism.
Source: blueprint, restriction before limit (blueprint: lem-sp-integral-tower-image-reconstruction).
-/
abbrev completedRestriction (s : Coefficients l E) (T : Scheme.{u}) :=
  restrictScalars.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (s.reduction T).coefficient.hom)

/-- The strict tower after restricting every finite scalar action to R_T. Its
transitions are the actual quotient-semilinear transitions, retained before derivation.
Source: blueprint, clause (2) (blueprint: lem-sp-integral-tower-image-reconstruction). -/
def restrictedTower (s : Coefficients l E) (T : Scheme.{u}) :
    spCoefficientTowers l E T ⥤ (ℕᵒᵖ ⥤ spIntegralSectionModules l E T) :=
  (Functor.ofOpSequence
    (X := fun n : ℕ ↦ spCompletedEvaluation l E T (s.towers T) n ⋙
      completedRestriction l E s T)
    (fun n ↦ Functor.whiskerRight (spCompletedTransition l E T (s.towers T) n)
      (completedRestriction l E s T))).flip

/-- The actual ordinary inverse limit of that restricted strict tower.
Source: blueprint, clause (2) (blueprint: lem-sp-integral-tower-image-reconstruction). -/
def ordinaryLimit (s : Coefficients l E) (T : Scheme.{u}) :=
  restrictedTower l E s T ⋙ Limits.lim

/-- The n-th ordinary inverse-limit projection, with its original finite-level sections.
Source: blueprint, clause (2) (blueprint: lem-sp-integral-tower-image-reconstruction). -/
def ordinaryProjection (s : Coefficients l E) (T : Scheme.{u})
    (C : spCoefficientTowers l E T) (n : ℕ) :=
  limit.π ((restrictedTower l E s T).obj C) (op n)

/-- Normalization of the ordinary tensor/limit adjunction on local tensor generators.
Source: blueprint, clause (2) (blueprint: lem-sp-integral-tower-image-reconstruction). -/
def IsOrdinaryAdjunctionNormalized (s : Coefficients l E) (T : Scheme.{u})
    (adj : (s.reduction T).ordinary ⊣ ordinaryLimit l E s T) : Prop :=
  ∀ (P : spIntegralSectionModules l E T) (n : ℕ)
    (U : T.ProEtᵒᵖ) (x : P.val.obj U),
    (ordinaryProjection l E s T ((s.reduction T).ordinary.obj P) n).val.app U
        ((adj.unit.app P).val.app U x) =
      (((s.reduction T).level n).inv.app P).val.app U
        (systemModelTmul ((s.towers T).scalar
          (spIntegralReductionScalar l E T (s.reduction T).coefficient n)).model P U 1 x)

/-- Representative normalization of the derived tensor/limit adjunction.
Source: blueprint, clause (2) (blueprint: lem-sp-integral-tower-image-reconstruction). -/
def IsDerivedAdjunctionNormalized (s : Coefficients l E) (T : Scheme.{u})
    [(ordinaryLimit l E s T).Additive]
    (ordinaryAdjunction : (s.reduction T).ordinary ⊣ ordinaryLimit l E s T)
    (derived : spDerivedCoefficientTowers l E T (s.towers T) ⥤
      DerivedCategory (spIntegralSectionModules l E T))
    (unit : (ordinaryLimit l E s T).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      spTowerLocalization l E T (s.towers T) ⋙ derived)
    (adjunction : (s.reduction T).red ⊣ derived) : Prop :=
  ∀ (P : CochainComplex (spIntegralSectionModules l E T) ℤ)
    (I : CochainComplex (spCoefficientTowers l E T) ℤ)
    (v : ((s.reduction T).ordinary.mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
    adjunction.homEquiv (DerivedCategory.Q.obj P)
        ((spTowerLocalization l E T (s.towers T)).obj I)
        ((s.reduction T).counit.app P ≫
          (spTowerLocalization l E T (s.towers T)).map v) =
      DerivedCategory.Q.map
        ((ordinaryAdjunction.mapHomologicalComplex (.up ℤ)).homEquiv P I v) ≫ unit.app I

/-- Universal presentation of total derived inverse limit. Ordinary reduction tensors
with each quotient; its right adjoint is precisely the inverse limit of the restricted
finite modules. Both the ordinary and derived universal properties are retained.
The representative equation fixes the derived adjunction to the ordinary one.
Source: blueprint, clause (2), strict tower inverse limit; Stacks 0940 and 09T5
(blueprint: lem-sp-integral-tower-image-reconstruction). -/
structure DerivedLimit (s : Coefficients l E) (T : Scheme.{u}) where
  [additive : (ordinaryLimit l E s T).Additive]
  ordinaryAdjunction : (s.reduction T).ordinary ⊣ ordinaryLimit l E s T
  ordinary_normalization : IsOrdinaryAdjunctionNormalized l E s T ordinaryAdjunction
  derived : spDerivedCoefficientTowers l E T (s.towers T) ⥤
    DerivedCategory (spIntegralSectionModules l E T)
  unit : (ordinaryLimit l E s T).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
    spTowerLocalization l E T (s.towers T) ⋙ derived
  universal : derived.IsRightDerivedFunctor unit
    (HomologicalComplex.quasiIso (spCoefficientTowers l E T) (.up ℤ))
  computes : ∀ I : CochainComplex (spCoefficientTowers l E T) ℤ,
    I.IsKInjective → IsIso (unit.app I)
  adjunction : (s.reduction T).red ⊣ derived
  normalization : IsDerivedAdjunctionNormalized l E s T ordinaryAdjunction derived unit
    adjunction

/-- The compact-support image as one object of the original strict derived tower category.
Source: blueprint, clause (1) (blueprint: lem-sp-integral-tower-image-reconstruction). -/
def imageTower (s : Coefficients l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : Integral l E X) :
    spDerivedCoefficientTowers l E Y (s.towers Y) :=
  (towerShriek l E s c).obj ((red l E s X).obj M)

/-- One evaluated finite compact-support image, keeping the recorded scalar action.
Source: blueprint, clause (1) (blueprint: lem-sp-integral-tower-image-reconstruction). -/
def imageLevel (s : Coefficients l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : Integral l E X) (n : ℕ) :
    Scheme.proEtaleDerivedCategory Y (SpTowerShriek.R l E n) :=
  (spDerivedCoefficientEvaluation l E Y (s.towers Y) n).obj (imageTower l E s c M)

/-- Additivity of the recorded sequence-site realization.
Source: blueprint, strict tower realization (blueprint: lem-sp-integral-tower-image-reconstruction).
-/
instance realizationFunctorAdditive (s : Coefficients l E) (T : Scheme.{u}) :
    (s.base.realization T).functor.Additive := s.base.realizationAdditive T

/-- Ordinary scalar extension at the specified positive quotient level.
Source: blueprint, reduction (blueprint: lem-sp-integral-tower-image-reconstruction). -/
abbrev ordinaryLevel (s : Coefficients l E) (T : Scheme.{u}) (n : ℕ) :=
  (spIntegralModuleEquivalence l E T).functor ⋙
    ((s.towers T).scalar
      (spIntegralReductionScalar l E T (s.reduction T).coefficient n)).model.E

/-- The strict reduction functor in the sequence-site coordinates, before derivation.
Source: blueprint, strict tensor tower (blueprint: lem-sp-integral-tower-image-reconstruction). -/
abbrev ordinaryReduction (s : Coefficients l E) (T : Scheme.{u}) :=
  (spIntegralModuleEquivalence l E T).functor ⋙
    (s.reduction T).ordinary ⋙ (s.base.realization T).functor

/-- The same reduction after localization, retaining every transition.
Source: blueprint, strict reduction (blueprint: lem-sp-integral-tower-image-reconstruction). -/
abbrev derivedReduction (s : Coefficients l E) (T : Scheme.{u}) :=
  red l E s T ⋙ (realization l E s T).functor

/-- Ordinary evaluation transports with identity on every underlying section.
Source: blueprint, sectionwise tower realization
(blueprint: lem-sp-integral-tower-image-reconstruction). -/
structure Evaluation (s : Coefficients l E) where
  ordinary : ∀ (T : Scheme.{u}) (n : ℕ),
    (s.base.realization T).functor ⋙ SpTowerShriek.ev l E T n ≅
      spCoefficientEvaluation l E T (s.towers T).equivalence n
  sections : ∀ (T : Scheme.{u}) (n : ℕ) (C : spCoefficientTowers l E T)
    (U : T.ProEtᵒᵖ) (x : ((SpTowerShriek.ev l E T n).obj
      ((s.base.realization T).functor.obj C)).val.obj U),
    HEq (((ordinary T n).hom.app C).val.app U x) x

set_option linter.style.haveILetI false in
/-- Derived evaluation is the localization of that sectionwise identity.
Source: blueprint, evaluation comparison (blueprint: lem-sp-integral-tower-image-reconstruction). -/
def Evaluation.derived (s : Coefficients l E) (e : Evaluation l E s)
    (T : Scheme.{u}) (n : ℕ) :
    (realization l E s T).functor ⋙ SpTowerShriek.Ev l E T n ≅
      spDerivedCoefficientEvaluation l E T (s.towers T) n :=
  letI := (s.towers T).hasDerived
  letI := s.base.realizationAdditive T
  letI := (s.towers T).equivalenceAdditive
  letI := (s.towers T).evaluationLimits n
  letI := (s.towers T).evaluationColimits n
  letI hAdd : (spCoefficientEvaluation l E T (s.towers T).equivalence n).Additive := by
    letI := (s.towers T).equivalenceAdditive
    letI := (s.towers T).evaluationLimits n
    exact Functor.additive_of_preserves_binary_products _
  letI : ((s.base.realization T).functor ⋙ SpTowerShriek.ev l E T n).Additive := by
    infer_instance
  letI : PreservesFiniteLimits ((s.base.realization T).functor ⋙ SpTowerShriek.ev l E T n) := by
    infer_instance
  letI : PreservesFiniteColimits ((s.base.realization T).functor ⋙ SpTowerShriek.ev l E T n) := by
    infer_instance
  let e' : (s.base.realization T).functor ⋙ SpTowerShriek.ev l E T n ≅
      spCoefficientEvaluation l E T (s.towers T).equivalence n := e.ordinary T n
  (Functor.mapDerivedCategoryCompIso (s.base.realization T).functor
      (SpTowerShriek.ev l E T n)).symm ≪≫
    @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _
      ((s.base.realization T).functor ⋙ SpTowerShriek.ev l E T n)
      (spCoefficientEvaluation l E T (s.towers T).equivalence n)
      _ hAdd _ _
      ((s.towers T).evaluationLimits n) ((s.towers T).evaluationColimits n) e'

/-- Ordinary scalar evaluation of strict reduction, with the existing tensor generator.
Source: blueprint, quotient tensor (blueprint: lem-sp-integral-tower-image-reconstruction). -/
def ordinaryReductionEvaluation (s : Coefficients l E) (e : Evaluation l E s)
    (T : Scheme.{u}) (n : ℕ) :
    ordinaryReduction l E s T ⋙ SpTowerShriek.ev l E T n ≅ ordinaryLevel l E s T n :=
  Functor.associator (spIntegralModuleEquivalence l E T).functor
      ((s.reduction T).ordinary ⋙ (s.base.realization T).functor)
      (SpTowerShriek.ev l E T n) ≪≫
    Functor.isoWhiskerLeft (spIntegralModuleEquivalence l E T).functor
      (Functor.associator (s.reduction T).ordinary (s.base.realization T).functor
          (SpTowerShriek.ev l E T n) ≪≫
        Functor.isoWhiskerLeft (s.reduction T).ordinary (e.ordinary T n) ≪≫
        (s.reduction T).level n)

/-- The universal reduction counit on a complex, transported without any choice of map.
Source: blueprint, K-flat reduction (blueprint: lem-sp-integral-tower-image-reconstruction). -/
def reductionComplexComparison (s : Coefficients l E) (T : Scheme.{u})
    (P : CochainComplex (Modules l E T) ℤ) :
    (derivedReduction l E s T).obj (DerivedCategory.Q.obj P) ⟶
      DerivedCategory.Q.obj
        (((ordinaryReduction l E s T).mapHomologicalComplex (.up ℤ)).obj P) :=
  letI := (s.towers T).hasDerived
  letI := Functor.additive_of_preserves_binary_products
    (spIntegralModuleEquivalence l E T).functor
  letI := s.base.realizationAdditive T
  (realization l E s T).functor.map
    ((s.reduction T).red.map
      ((spIntegralModuleEquivalence l E T).functor.mapDerivedCategoryFactors.hom.app P) ≫
      (s.reduction T).counit.app
        (((spIntegralModuleEquivalence l E T).functor.mapHomologicalComplex (.up ℤ)).obj P)) ≫
    (s.base.realization T).functor.mapDerivedCategoryFactors.hom.app
      ((((spIntegralModuleEquivalence l E T).functor ⋙
        (s.reduction T).ordinary).mapHomologicalComplex (.up ℤ)).obj P)

/-- The evaluated ordinary pullback comparison, in scalar-extension coordinates.
Source: blueprint, scalar extension and pullback
(blueprint: lem-sp-integral-tower-image-reconstruction). -/
def ordinaryPullLevelMap (s : Coefficients l E) (e : Evaluation l E s)
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (q : CondensedRing.upperStar (spIntegralCondensed l E) f ⋙ ordinaryReduction l E s X ≅
      ordinaryReduction l E s Y ⋙ (s.operations.geometry f).pull)
    (M : Modules l E Y) (n : ℕ) :=
  (ordinaryReductionEvaluation l E s e X n).inv.app
      ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M) ≫
    (SpTowerShriek.ev l E X n).map (q.hom.app M) ≫
    ((s.operations.geometry f).ordinaryPullEvaluation n).hom.app
      ((ordinaryReduction l E s Y).obj M) ≫
    (Scheme.proEtaleConstantRingPullback (SpTowerShriek.R l E n) f).map
      ((ordinaryReductionEvaluation l E s e Y n).hom.app M)

/-- A strict scalar/pullback comparison fixed on local tensor units before localization,
and on flat-term K-flat representatives afterwards. These equations determine the maps;
they are not an unnormalized family of derived isomorphisms.
Source: blueprint, proof (2)--(3), K-flat scalar extension/pullback compatibility
(blueprint: lem-sp-integral-tower-image-reconstruction). -/
structure ScalarPull (s : Coefficients l E) (e : Evaluation l E s)
    {X Y : Scheme.{u}} (f : X ⟶ Y) where
  ordinary : CondensedRing.upperStar (spIntegralCondensed l E) f ⋙
      ordinaryReduction l E s X ≅
    ordinaryReduction l E s Y ⋙ (s.operations.geometry f).pull
  generators : ∀ (M : Modules l E Y) (n : ℕ) (V : Y.ProEt)
    (x : ((spIntegralModuleEquivalence l E Y).functor.obj M).val.obj (op V)),
    ((ordinaryPullLevelMap l E s e f ordinary M n).val.app
      (op ((Scheme.proEtaleBaseChange f).obj V)))
      (systemModelTmul ((s.towers X).scalar
        (spIntegralReductionScalar l E X (s.reduction X).coefficient n)).model
        ((spIntegralModuleEquivalence l E X).functor.obj
          ((CondensedRing.upperStar (spIntegralCondensed l E) f).obj M))
        (op ((Scheme.proEtaleBaseChange f).obj V)) 1
        (((CondensedRing.upperStarLowerStarAdjunction (spIntegralCondensed l E) f).unit.app
          M).hom.hom.app (op V) x)) =
      (((Scheme.proEtaleConstantRingAdjunction (SpTowerShriek.R l E n) f).unit.app
        ((ordinaryLevel l E s Y n).obj M)).val.app (op V))
        (systemModelTmul ((s.towers Y).scalar
          (spIntegralReductionScalar l E Y (s.reduction Y).coefficient n)).model
          ((spIntegralModuleEquivalence l E Y).functor.obj M) (op V) 1 x)
  derived : pull l E f ⋙ derivedReduction l E s X ≅
    derivedReduction l E s Y ⋙ SpTowerShriek.pull l E s.base (s.operations.geometry f)
  representatives : ∀ P : CochainComplex (Modules l E Y) ℤ,
    CochainComplex.IsKFlatIndependentCoefficients (R := spIntegralSectionRing l E Y)
      (((spIntegralModuleEquivalence l E Y).functor.mapHomologicalComplex (.up ℤ)).obj P) →
    (∀ i : ℤ, IsFlatOnSite.{u + 1, u, u + 1, u + 1}
      (J := Scheme.ProEt.topology Y) (R := spIntegralSectionRing l E Y)
      ((spIntegralModuleEquivalence l E Y).functor.obj (P.X i))) →
    derived.hom.app (DerivedCategory.Q.obj P) ≫
      (SpTowerShriek.pull l E s.base (s.operations.geometry f)).map
        (reductionComplexComparison l E s Y P) ≫
      (s.operations.geometry f).pull.mapDerivedCategoryFactors.hom.app
        (((ordinaryReduction l E s Y).mapHomologicalComplex (.up ℤ)).obj P) =
    (derivedReduction l E s X).map ((pullComplexComparison l E f P).hom) ≫
      reductionComplexComparison l E s X
        (((CondensedRing.upperStar (spIntegralCondensed l E) f).mapHomologicalComplex
          (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatIso.mapHomologicalComplex ordinary (.up ℤ)).hom.app P)

/-- All geometric comparisons use this one sectionwise and representative normalization.
Source: blueprint, proof (2)--(3) (blueprint: lem-sp-integral-tower-image-reconstruction). -/
structure ScalarCompatibility (s : Coefficients l E) where
  evaluation : Evaluation l E s
  pullback : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), ScalarPull l E s evaluation f

/-- The proper coefficient comparison is the transpose of the integral counit through
exactly the recorded tower geometric adjunction.
Source: blueprint, proof (2) (blueprint: lem-sp-integral-tower-image-reconstruction). -/
def properReduction (s : Coefficients l E) (q : ScalarCompatibility l E s)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Integral l E X) :=
  ((SpTowerShriek.adjunction l E s.base (s.operations.geometry f)).homEquiv _ _)
    ((q.pullback f).derived.inv.app
        ((CondensedRing.lowerStar (spIntegralCondensed l E) f).rightDerivedFunctor.obj N) ≫
      (derivedReduction l E s X).map
        ((CondensedRing.derivedUpperStarLowerStarAdjunction
          (spIntegralCondensed l E) f).counit.app N))

/-- The inverse open coefficient comparison is the transpose of the integral open unit
through exactly the recorded strict-system open adjunction.
Source: blueprint, proof (2) (blueprint: lem-sp-integral-tower-image-reconstruction). -/
def openReductionInverse (s : Coefficients l E) (q : ScalarCompatibility l E s)
    {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (N : Integral l E U) :=
  ((s.operations.openOp j).derivedAdjunction.homEquiv _ _).symm
    ((derivedReduction l E s U).map
        (((CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
          (spIntegralCondensed l E) j).ofNatIsoRight
          (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
            (spIntegralCondensed l E) j).symm).unit.app N) ≫
      (q.pullback j).derived.hom.app
        ((CondensedRing.openImmersionLowerShriek
          (spIntegralCondensed l E) j).mapDerivedCategory.obj N))

/-- Invertibility of the specified open tensor mate, rather than a chosen open comparison.
Source: blueprint, exact open extension (blueprint: lem-sp-integral-tower-image-reconstruction). -/
def OpenScalarIsIso (s : Coefficients l E) (q : ScalarCompatibility l E s) : Prop :=
  ∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (N : Integral l E U),
    IsIso (openReductionInverse l E s q j N)

/-- The integral-to-strict-tower base-change map: proper counit mate, then the inverse
open-unit mate. Every map is constructed before any invertibility assertion for f_!.
Source: blueprint, proof (2) (blueprint: lem-sp-integral-tower-image-reconstruction). -/
def towerBaseChange (s : Coefficients l E) (q : ScalarCompatibility l E s)
    (hq : OpenScalarIsIso l E s q)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (M : Integral l E X) :
    (red l E s Y).obj ((shriek l E c).obj M) ⟶ imageTower l E s c M :=
  letI := hq c.i M
  (realization l E s Y).unitIso.hom.app _ ≫
    (realization l E s Y).inverse.map
      (properReduction l E s q c.g
          ((CondensedRing.openImmersionLowerShriek
            (spIntegralCondensed l E) c.i).mapDerivedCategory.obj M) ≫
        (SpTowerShriek.push l E s.base (s.operations.geometry c.g)).map
          (inv (openReductionInverse l E s q c.i M)))

/-- Finite evaluation of tower shriek, transported from the actual Fcomparison.
Source: blueprint, finite Rf_! (blueprint: lem-sp-integral-tower-image-reconstruction). -/
def finiteComparison (s : Coefficients l E) (e : Evaluation l E s)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ) :
    towerShriek l E s c ⋙ spDerivedCoefficientEvaluation l E Y (s.towers Y) n ≅
      spDerivedCoefficientEvaluation l E X (s.towers X) n ⋙ finiteShriek l E s c n :=
  Functor.associator (realization l E s X).functor
      (SpTowerShriek.F l E s.base s.operations c ⋙ (realization l E s Y).inverse)
      (spDerivedCoefficientEvaluation l E Y (s.towers Y) n) ≪≫
    Functor.isoWhiskerLeft (realization l E s X).functor
      (Functor.associator (SpTowerShriek.F l E s.base s.operations c)
          (realization l E s Y).inverse
          (spDerivedCoefficientEvaluation l E Y (s.towers Y) n) ≪≫
        Functor.isoWhiskerLeft (SpTowerShriek.F l E s.base s.operations c)
          (Functor.isoWhiskerLeft (realization l E s Y).inverse
              (Evaluation.derived l E s e Y n).symm ≪≫
            (Functor.associator (realization l E s Y).inverse
              (realization l E s Y).functor (SpTowerShriek.Ev l E Y n)).symm ≪≫
            Functor.isoWhiskerRight (realization l E s Y).counitIso
              (SpTowerShriek.Ev l E Y n) ≪≫
            Functor.leftUnitor (SpTowerShriek.Ev l E Y n)) ≪≫
        SpTowerShriek.Fcomparison l E s.base s.operations c n) ≪≫
    (Functor.associator (realization l E s X).functor (SpTowerShriek.Ev l E X n)
      (finiteShriek l E s c n)).symm ≪≫
    Functor.isoWhiskerRight (Evaluation.derived l E s e X n) (finiteShriek l E s c n)

/-- The named integral-to-finite reduction mate: evaluate the constructed strict map
and apply the transported Fcomparison. It is defined as a morphism, not as an iso field.
Source: blueprint, clause (2) (blueprint: lem-sp-integral-tower-image-reconstruction). -/
def finiteBaseChange (s : Coefficients l E) (q : ScalarCompatibility l E s)
    (hq : OpenScalarIsIso l E s q)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Integral l E X) (n : ℕ) :
    (level l E s Y n).obj ((shriek l E c).obj M) ⟶
      (finiteShriek l E s c n).obj ((level l E s X n).obj M) :=
  (spDerivedCoefficientEvaluation l E Y (s.towers Y) n).map
      (towerBaseChange l E s q hq c M) ≫
    (finiteComparison l E s q.evaluation c n).hom.app ((red l E s X).obj M)

/-- Total derived inverse limit after restriction of the finite coefficient actions,
transported through the recorded section equivalence. Source: source paragraph (2)
(blueprint: lem-sp-integral-tower-image-reconstruction). -/
def limit (s : Coefficients l E)
    (A : ∀ T : Scheme.{u}, DerivedLimit l E s T)
    (T : Scheme.{u}) : spDerivedCoefficientTowers l E T (s.towers T) ⥤ Integral l E T :=
  (A T).derived ⋙ (sectionEquivalence l E T).inverse

/-- The actual normalized reduction/total-limit adjunction in integral module coordinates.
Source: source paragraph (2) (blueprint: lem-sp-integral-tower-image-reconstruction). -/
def adjunction (s : Coefficients l E)
    (A : ∀ T : Scheme.{u}, DerivedLimit l E s T)
    (T : Scheme.{u}) : red l E s T ⊣ limit l E s A T :=
  (sectionEquivalence l E T).toAdjunction.comp (A T).adjunction

/-- The right mate of the normalized proper/open scalar comparison, constructed in
whole derived towers. This is the compact-support/total-limit comparison; its
normalization is inherited from the ordinary units and K-flat scalar comparison,
not from finite evaluation. Source: source paragraph (2)
(blueprint: lem-sp-integral-tower-image-reconstruction). -/
def limitComparison (s : Coefficients l E) (q : ScalarCompatibility l E s)
    (hq : OpenScalarIsIso l E s q)
    (A : ∀ T : Scheme.{u}, DerivedLimit l E s T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (C : spDerivedCoefficientTowers l E X (s.towers X)) :
    (shriek l E c).obj ((limit l E s A X).obj C) ⟶
      (limit l E s A Y).obj ((towerShriek l E s c).obj C) :=
  (adjunction l E s A Y).unit.app ((shriek l E c).obj ((limit l E s A X).obj C)) ≫
    (limit l E s A Y).map
      (towerBaseChange l E s q hq c ((limit l E s A X).obj C) ≫
        (towerShriek l E s c).map ((adjunction l E s A X).counit.app C))

/-- Apply compact support to the input completion unit, then the normalized
proper/open total-limit comparison. Source: source paragraph (2)
(blueprint: lem-sp-integral-tower-image-reconstruction). -/
def reconstruction (s : Coefficients l E) (q : ScalarCompatibility l E s)
    (hq : OpenScalarIsIso l E s q)
    (A : ∀ T : Scheme.{u}, DerivedLimit l E s T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (M : Integral l E X) :
    (shriek l E c).obj M ⟶ (limit l E s A Y).obj (imageTower l E s c M) :=
  (shriek l E c).map ((adjunction l E s A X).unit.app M) ≫
    limitComparison l E s q hq A c ((red l E s X).obj M)

/-- The actual adjoint transpose of reconstruction, defined before asserting
invertibility and before evaluating. Source: source paragraph (2)
(blueprint: lem-sp-integral-tower-image-reconstruction). -/
def towerComparison (s : Coefficients l E) (q : ScalarCompatibility l E s)
    (hq : OpenScalarIsIso l E s q)
    (A : ∀ T : Scheme.{u}, DerivedLimit l E s T)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (M : Integral l E X) :
    (red l E s Y).obj ((shriek l E c).obj M) ⟶ imageTower l E s c M :=
  (red l E s Y).map (reconstruction l E s q hq A c M) ≫
    (adjunction l E s A Y).counit.app (imageTower l E s c M)

/-- Restriction from a finite quotient to the integral ring, with the section
coordinate equivalence. Source: source paragraph (2), scalar identifications
(blueprint: lem-sp-integral-tower-image-reconstruction). -/
def finiteRestriction (s : Coefficients l E) (T : Scheme.{u}) (n : ℕ) :=
  (restrictScalars.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      (spIntegralReductionScalar l E T (s.reduction T).coefficient n))).mapDerivedCategory ⋙
    (sectionEquivalence l E T).inverse

/-- The quotient tensor/restriction adjunction, with its specified quotient unit.
Source: source paragraph (2), finite projections
(blueprint: lem-sp-integral-tower-image-reconstruction). -/
def finiteAdjunction (s : Coefficients l E) (T : Scheme.{u}) (n : ℕ) :
    level l E s T n ⊣ finiteRestriction l E s T n :=
  ((sectionEquivalence l E T).toAdjunction.comp
    ((s.towers T).scalar
      (spIntegralReductionScalar l E T (s.reduction T).coefficient n)).adjunction).ofNatIsoLeft
    (Functor.isoWhiskerLeft (sectionEquivalence l E T).functor
        ((s.reduction T).evaluation n).symm ≪≫
      (Functor.associator (sectionEquivalence l E T).functor (s.reduction T).red
        (spDerivedCoefficientEvaluation l E T (s.towers T) n)).symm)

/-- A finite projection of the actual derived limit, as the quotient adjoint of
its evaluated counit. Both adjunctions retain their ordinary-unit normalizations.
Source: source paragraph (2), finite projections
(blueprint: lem-sp-integral-tower-image-reconstruction). -/
def projection (s : Coefficients l E)
    (A : ∀ T : Scheme.{u}, DerivedLimit l E s T)
    (T : Scheme.{u}) (C : spDerivedCoefficientTowers l E T (s.towers T)) (n : ℕ) :
    (limit l E s A T).obj C ⟶
      (finiteRestriction l E s T n).obj
        ((spDerivedCoefficientEvaluation l E T (s.towers T) n).obj C) :=
  (finiteAdjunction l E s T n).homEquiv _ _
    ((spDerivedCoefficientEvaluation l E T (s.towers T) n).map
      ((adjunction l E s A T).counit.app C))

/-- The proper/open scalar-restriction comparison, as the finite scalar right mate
of the representative-normalized compact-support scalar comparison. Source:
source paragraph (2), proper/open images of quotient units
(blueprint: lem-sp-integral-tower-image-reconstruction). -/
def finiteRestrictionComparison (s : Coefficients l E) (q : ScalarCompatibility l E s)
    (hq : OpenScalarIsIso l E s q)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) (n : ℕ)
    (N : Scheme.proEtaleDerivedCategory X (SpTowerShriek.R l E n)) :
    (shriek l E c).obj ((finiteRestriction l E s X n).obj N) ⟶
      (finiteRestriction l E s Y n).obj ((finiteShriek l E s c n).obj N) :=
  (finiteAdjunction l E s Y n).unit.app
      ((shriek l E c).obj ((finiteRestriction l E s X n).obj N)) ≫
    (finiteRestriction l E s Y n).map
      (finiteBaseChange l E s q hq c ((finiteRestriction l E s X n).obj N) n ≫
        (finiteShriek l E s c n).map ((finiteAdjunction l E s X n).counit.app N))

/-- Normalized constructible image towers, uniform bounds, and canonical reconstruction.
The inputs are only pinned realizations of the canonical coefficient constructions.
There is no unrestricted constructibility assertion in them. Normalized scalar
and derived-limit comparisons are constructed as output, not assumed.
Noetherianity and invertibility of the coefficient prime are deduced from the
finite-type-over-field hypotheses before invoking constructible reduction or the
tower equivalence.

Source: source paragraphs (1)--(2)
(blueprint: lem-sp-integral-tower-image-reconstruction).

Proof: first derive Noetherianity of X and Y from finite type over the
Noetherian field, and of the middle scheme from properness over Y. The positive
characteristic is different from l, so l is invertible in all stalks. Deduce that
the open factor is quasi-compact. Only now apply the Noetherian, l-invertible
constructibility clause of `sp_reduction_tower_current_statement` and the
constructible restriction of the reduction/limit adjunction on X and Y. Reduction supplies a
normalized input with uniform Tor bounds.
Tower-shriek evaluation and the finite uniform bound give constructibility,
cohomology and Tor bounds widened by `2*d`. The actual transition is the finite
scalar mate composed with the image of the input transition, hence invertible.
Exact countable products and the quasi-compact open extension/product theorem
give the augmentation-preserving open/derived-limit comparison. Proper direct
image commutes with the derived strict limit. Restrict the finite scalar actions
on the whole diagram; the normalized proper and open scalar comparisons identify
this diagram with the restricted image tower, before evaluation. Their right mate
is `limitComparison`. Apply it after compact support of the input completion unit;
that unit and the comparisons are isomorphisms on constructible inputs, proving
invertibility of `reconstruction`. The normalized tower equivalence makes its
limit constructible, hence also the integral image. The actual counit is invertible
on the normalized image tower, giving `towerComparison`; adjunction triangle
identities identify it with the original normalized proper/open mate. Evaluation
gives the specified finite comparisons. Naturality of units, counits, scalar mates
and derived functors gives both displayed naturality equations. -/
theorem image_reconstruction
    (D : ∀ T : Scheme.{u}, SpCoefficientTowersAbelian l E T)
    (r : ∀ T : Scheme.{u}, SpReductionTowerConstruction l E T (D T))
    (hn : ∀ T : Scheme.{u}, IsEvaluationNormalized l E T (D T) (r T))
    (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b) :
    let s : Coefficients l E := ⟨D, r, hn, b, o⟩
    ∃ q : ScalarCompatibility l E s,
      ∃ hq : OpenScalarIsIso l E s q,
      ∃ A : ∀ T : Scheme.{u}, DerivedLimit l E s T,
      ∀ (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
        (X Y : Scheme.{u}) [X.Over (Spec (.of k))] [Y.Over (Spec (.of k))]
        [LocallyOfFiniteType (X ↘ Spec (.of k))] [QuasiCompact (X ↘ Spec (.of k))]
        [IsSeparated (X ↘ Spec (.of k))]
        [LocallyOfFiniteType (Y ↘ Spec (.of k))] [QuasiCompact (Y ↘ Spec (.of k))]
        [IsSeparated (Y ↘ Spec (.of k))]
        (f : X ⟶ Y) [f.IsOver (Spec (.of k))] (d : ℕ) [SmoothOfRelativeDimension d f],
      ∀ c : Compactification f,
        (∀ M : Constructible l E X,
          spNormalizedConstructibleTorTowers l E Y (s.towers Y)
            (imageTower l E s c M.obj) ∧
          (∀ a b : ℤ, a ≤ b → DerivedCategory.torAmplitudeIn _ a b M.obj → ∀ n : ℕ,
            Scheme.HasProEtaleTorAmplitude Y (SpTowerShriek.R l E n)
              (imageLevel l E s c M.obj n) a (b + 2 * d) ∧
            ∀ i : ℤ, (i < a ∨ b + 2 * d < i) →
              IsZero ((@DerivedCategory.homologyFunctor
                (Scheme.proEtaleRingModules Y
                  (Scheme.proEtaleConstantRing Y (SpTowerShriek.R l E n)))
                _ _ (HasDerivedCategory.standard _) i).obj
                  (imageLevel l E s c M.obj n))) ∧
          constantModelBoundedConstructible (spIntegralCondensed l E) Y
            ((shriek l E c).obj M.obj) ∧
          constantModelBoundedConstructible (spIntegralCondensed l E) Y
            ((limit l E s A Y).obj (imageTower l E s c M.obj)) ∧
          IsIso (reconstruction l E s q hq A c M.obj) ∧
          IsIso (towerComparison l E s q hq A c M.obj) ∧
          towerComparison l E s q hq A c M.obj = towerBaseChange l E s q hq c M.obj ∧
          (∀ n : ℕ,
            (spDerivedCoefficientEvaluation l E Y (s.towers Y) n).map
                (towerComparison l E s q hq A c M.obj) ≫
              (finiteComparison l E s q.evaluation c n).hom.app
                ((red l E s X).obj M.obj) = finiteBaseChange l E s q hq c M.obj n) ∧
          (∀ n : ℕ, IsIso (finiteBaseChange l E s q hq c M.obj n)) ∧
          (∀ n : ℕ,
            reconstruction l E s q hq A c M.obj ≫
                projection l E s A Y (imageTower l E s c M.obj) n ≫
                (finiteRestriction l E s Y n).map
                  ((finiteComparison l E s q.evaluation c n).hom.app
                    ((red l E s X).obj M.obj)) =
              (shriek l E c).map ((finiteAdjunction l E s X n).unit.app M.obj) ≫
                finiteRestrictionComparison l E s q hq c n
                  ((level l E s X n).obj M.obj))) ∧
        (∀ (M N : Constructible l E X) (u : M.obj ⟶ N.obj),
          (shriek l E c).map u ≫ reconstruction l E s q hq A c N.obj =
            reconstruction l E s q hq A c M.obj ≫
              (limit l E s A Y).map ((towerShriek l E s c).map ((red l E s X).map u))) ∧
        (∀ (M N : Constructible l E X) (u : M.obj ⟶ N.obj),
          (red l E s Y).map ((shriek l E c).map u) ≫
              towerComparison l E s q hq A c N.obj =
            towerComparison l E s q hq A c M.obj ≫
              (towerShriek l E s c).map ((red l E s X).map u)) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Current
