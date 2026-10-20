/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.Paper.SmoothPurityReductionTowerNormalized
public import Sheaf.Paper.TowerCompactSupportProjectionFormula
public import Sheaf.Paper.SmoothPurityTowerReconstruction
public import Sheaf.Paper.CompactificationCoherenceCocycle
public import Sheaf.Paper.ModuleObjectProjectionMap
public import Sheaf.Paper.CompletedCondensedCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.Compactification.Refinement
public import WeilConjectures.Compactification.RefinementCategory
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.LowerShriek
public import Sheaf.Paper.CondensedConstantConstructibility
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

public import Sheaf.Paper.SmoothPurityCoefficientTowers
import Sheaf.Paper.SmoothPurityCoefficientTowersAbelian
public import Sheaf.Paper.SmoothPurityTowerShriekLevels
import Sheaf.SecSmoothPurity.ReductionDirectImage
public import Sheaf.Paper.SmoothPurityNormalizedTowers
import Sheaf.Paper.SemilinearDerivedSections
import Sheaf.AlgebraicGeometry.ProEtaleOpenExtensionProducts
import Sheaf.CategoryTheory.RingedTowerPushforwardLimitComparison
import Sheaf.CategoryTheory.RingedToposMorphism
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.LocalizingAdmissibleCoefficients
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Paper.IntegralTensorProduct
import Sheaf.Paper.IntegralTensorPullback
import Sheaf.Paper.SmoothPurityNormalizedEquivalence
import Sheaf.SixFunctors.ProEtale.DerivedCompletion
/-!
# Integral compact support and its strict reduction tower

Source: blueprint main-20261015, sec-smooth-purity/sk-prop-sp-integral-adjunction,
`sk-prop-sp-integral-adjunction-direct-image.md`, clauses (1)--(3)
(blueprint: det-sp-integral-direct-image-tower).

All integral modules are over the actual pulled-back condensed ring of integers.
The section-module presentation is the recorded exact equivalence, and a natural
index n represents the positive exponent n+1. The inverse limit below is the total
right derived functor of the right adjoint to ordinary strict reduction: this is
inverse limit after restriction of all finite scalar actions to the integral ring.

## Main definitions

* `restrictedTower`, `ordinaryLimit`, `Limit`: restriction before total derived limit.
* `reconstruction`: the completion-unit comparison of integral direct images.
* `properProjection`, `compactOpenProjection`: the actual adjunction projection mates.

## Main statements

* `integral_direct_image_tower`: the three conclusions of the node.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false


universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.IntegralDirectImageTower

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The existing integral internal-module derived category.
Source: blueprint, R_T (blueprint: det-sp-integral-direct-image-tower). -/
abbrev Integral (T : Scheme.{u}) :=
  DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (spIntegralCondensed l E) T))

/-- The existing constant-model bounded constructible full subcategory.
Source: blueprint, Dbc (blueprint: det-sp-integral-direct-image-tower). -/
abbrev Constructible (T : Scheme.{u}) :=
  ConstantModelBoundedConstructible (spIntegralCondensed l E) T

/-- The exact section/internal derived equivalence, retaining every module section.
Source: blueprint, the sectionwise coefficient presentation
(blueprint: det-sp-integral-direct-image-tower). -/
def sectionEquivalence (T : Scheme.{u}) :
    Integral l E T ≌ DerivedCategory (spIntegralSectionModules l E T) :=
  letI := Functor.additive_of_preserves_binary_products
    (spIntegralModuleEquivalence l E T).functor
  (spIntegralModuleEquivalence l E T).mapDerivedCategory

/-- The already recorded separately derived compactification composite Rp_* D(j_!).
Source: blueprint, clause (2) (blueprint: det-sp-integral-direct-image-tower). -/
abbrev shriek {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Integral l E X ⥤ Integral l E Y :=
  CondensedRing.rightDerivedLowerShriekOfCompactification (spIntegralCondensed l E) c

/-- The existing derived module inverse image; no completion is applied.
Source: blueprint, clause (3) (blueprint: det-sp-integral-direct-image-tower). -/
abbrev pull {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Integral l E Y ⥤ Integral l E X :=
  CondensedRing.moduleObjectDerivedPullback (spIntegralCondensed l E) f

/-- The existing relative K-flat derived tensor over the pulled-back integral ring.
Source: blueprint, clause (3) (blueprint: det-sp-integral-direct-image-tower). -/
abbrev tensor (T : Scheme.{u}) : Integral l E T ⥤ Integral l E T ⥤ Integral l E T :=
  CondensedRing.derivedTensor (spIntegralCondensed l E) T

/-- The canonical presentation data already supplied by the dependency nodes.
These are coefficient constructions, not hypotheses on a scheme or on an input.
Source: blueprint, coefficient conventions and clause (1)
(blueprint: det-sp-integral-direct-image-tower). -/
structure Presentation where
  towers : ∀ T : Scheme.{u}, SpCoefficientTowersAbelian l E T
  reduction : ∀ T : Scheme.{u}, SpReductionTower l E T (towers T)
  base : SpTowerShriek.Base l E
  operations : SpTowerShriek.Operations l E base
  exchange : SpTowerShriek.OpenExchange l E base operations
  laws : SpTowerShriek.Laws l E base operations exchange

/-- Reduction of internal integral modules, through the recorded section equivalence.
Source: blueprint, red_T (blueprint: det-sp-integral-direct-image-tower). -/
def red (s : Presentation l E) (T : Scheme.{u}) :=
  (sectionEquivalence l E T).functor ⋙ (s.reduction T).red

/-- Exact transport between the two dependency presentations of strict derived towers.
Source: blueprint, strict tower category (blueprint: det-sp-integral-direct-image-tower). -/
abbrev realization (s : Presentation l E) (T : Scheme.{u}) :=
  SpTowerProjection.realization l E s.base T (s.towers T)

/-- The actual tower direct image, transported from the recorded ringed sequence site.
Source: blueprint, clause (1) (blueprint: det-sp-integral-direct-image-tower). -/
def towerShriek (s : Presentation l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :=
  (realization l E s X).functor ⋙ SpTowerShriek.F l E s.base s.operations c ⋙
    (realization l E s Y).inverse

/-- The finite reduction functor at positive level n+1.
Source: blueprint, M/ell^n (blueprint: det-sp-integral-direct-image-tower). -/
abbrev level (s : Presentation l E) (T : Scheme.{u}) (n : ℕ) :=
  red l E s T ⋙ spDerivedCoefficientEvaluation l E T (s.towers T) n

/-- The actual finite compactification composite, in the dependency's quotient coordinates.
Source: blueprint, clause (2) (blueprint: det-sp-integral-direct-image-tower). -/
abbrev finiteShriek (s : Presentation l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (n : ℕ) := SpTowerShriek.finiteF l E s.base c n

/-- Additivity supplied by the existing reduction interface.
Source: blueprint, strict reduction (blueprint: det-sp-integral-direct-image-tower). -/
instance ordinaryReductionAdditive (s : Presentation l E) (T : Scheme.{u}) :
    (s.reduction T).ordinary.Additive := (s.reduction T).additive

/-- Restriction from completed section coefficients to the actual pulled-back
integral section ring, along the recorded normalized ring isomorphism.
Source: blueprint, restriction before limit (blueprint: det-sp-integral-direct-image-tower). -/
abbrev completedRestriction (s : Presentation l E) (T : Scheme.{u}) :=
  restrictScalars.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map (s.reduction T).coefficient.hom)

/-- The strict tower after restricting every finite scalar action to R_T. Its
transitions are the actual quotient-semilinear transitions, retained before derivation.
Source: blueprint, clause (2) (blueprint: det-sp-integral-direct-image-tower). -/
def restrictedTower (s : Presentation l E) (T : Scheme.{u}) :
    spCoefficientTowers l E T ⥤ (ℕᵒᵖ ⥤ spIntegralSectionModules l E T) :=
  (Functor.ofOpSequence
    (X := fun n : ℕ ↦ spCompletedEvaluation l E T (s.towers T) n ⋙
      completedRestriction l E s T)
    (fun n ↦ Functor.whiskerRight (spCompletedTransition l E T (s.towers T) n)
      (completedRestriction l E s T))).flip

/-- The actual ordinary inverse limit of that restricted strict tower.
Source: blueprint, clause (2) (blueprint: det-sp-integral-direct-image-tower). -/
def ordinaryLimit (s : Presentation l E) (T : Scheme.{u}) :=
  restrictedTower l E s T ⋙ Limits.lim

/-- The n-th ordinary inverse-limit projection, with its original finite-level sections.
Source: blueprint, clause (2) (blueprint: det-sp-integral-direct-image-tower). -/
def ordinaryProjection (s : Presentation l E) (T : Scheme.{u})
    (C : spCoefficientTowers l E T) (n : ℕ) :=
  limit.π ((restrictedTower l E s T).obj C) (op n)

/-- Normalization of the ordinary tensor/limit adjunction on local tensor generators.
Source: blueprint, clause (2) (blueprint: det-sp-integral-direct-image-tower). -/
def IsOrdinaryAdjunctionNormalized (s : Presentation l E) (T : Scheme.{u})
    (adj : (s.reduction T).ordinary ⊣ ordinaryLimit l E s T) : Prop :=
  ∀ (P : spIntegralSectionModules l E T) (n : ℕ)
    (U : T.ProEtᵒᵖ) (x : P.val.obj U),
    (ordinaryProjection l E s T ((s.reduction T).ordinary.obj P) n).val.app U
        ((adj.unit.app P).val.app U x) =
      (((s.reduction T).level n).inv.app P).val.app U
        (systemModelTmul ((s.towers T).scalar
          (spIntegralReductionScalar l E T (s.reduction T).coefficient n)).model P U 1 x)

/-- Representative normalization of the derived tensor/limit adjunction.
Source: blueprint, clause (2) (blueprint: det-sp-integral-direct-image-tower). -/
def IsDerivedAdjunctionNormalized (s : Presentation l E) (T : Scheme.{u})
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
(blueprint: det-sp-integral-direct-image-tower). -/
structure Limit (s : Presentation l E) (T : Scheme.{u}) where
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

/-- The total derived limit, with values back in internal integral modules.
Source: blueprint, clause (2) (blueprint: det-sp-integral-direct-image-tower). -/
def lim (s : Presentation l E) (T : Scheme.{u}) (L : Limit l E s T) :=
  L.derived ⋙ (sectionEquivalence l E T).inverse

/-- The canonical reduction/limit adjunction, transported through the exact equivalence.
Source: blueprint, canonical completion comparison in clause (2)
(blueprint: det-sp-integral-direct-image-tower). -/
def redLimitAdjunction (s : Presentation l E) (T : Scheme.{u}) (L : Limit l E s T) :
    red l E s T ⊣ lim l E s T L :=
  (sectionEquivalence l E T).toAdjunction.comp L.adjunction

/-- The compact-support image as one object of the original strict derived tower category.
Source: blueprint, clause (1) (blueprint: det-sp-integral-direct-image-tower). -/
def imageTower (s : Presentation l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : Integral l E X) :
    spDerivedCoefficientTowers l E Y (s.towers Y) :=
  (towerShriek l E s c).obj ((red l E s X).obj M)

/-- One evaluated finite compact-support image, keeping the recorded scalar action.
Source: blueprint, clause (1) (blueprint: det-sp-integral-direct-image-tower). -/
def imageLevel (s : Presentation l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (M : Integral l E X) (n : ℕ) :
    Scheme.proEtaleDerivedCategory Y (SpTowerShriek.R l E n) :=
  (spDerivedCoefficientEvaluation l E Y (s.towers Y) n).obj (imageTower l E s c M)

/-- The natural comparison of whole strict towers on the bounded constructible domain.
Source: blueprint, clause (2) (blueprint: det-sp-integral-direct-image-tower). -/
abbrev TowerComparison (s : Presentation l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :=
  (constantModelBoundedConstructible (spIntegralCondensed l E) X).ι ⋙
      shriek l E c ⋙ red l E s Y ≅
    (constantModelBoundedConstructible (spIntegralCondensed l E) X).ι ⋙
      red l E s X ⋙ towerShriek l E s c

/-- Additivity of the sectionwise equivalence, used for its complex functor.
Source: blueprint, coefficient presentation (blueprint: det-sp-integral-direct-image-tower). -/
instance sectionFunctorAdditive (T : Scheme.{u}) :
    (spIntegralModuleEquivalence l E T).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Additivity of the recorded sequence-site realization.
Source: blueprint, strict tower realization (blueprint: det-sp-integral-direct-image-tower). -/
instance realizationFunctorAdditive (s : Presentation l E) (T : Scheme.{u}) :
    (s.base.realization T).functor.Additive := s.base.realizationAdditive T

/-- Integral module sheaves before localization.
Source: blueprint, R_T modules (blueprint: det-sp-integral-direct-image-tower). -/
abbrev Modules (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (spIntegralCondensed l E) T)

/-- Ordinary scalar extension at the specified positive quotient level.
Source: blueprint, reduction (blueprint: det-sp-integral-direct-image-tower). -/
abbrev ordinaryLevel (s : Presentation l E) (T : Scheme.{u}) (n : ℕ) :=
  (spIntegralModuleEquivalence l E T).functor ⋙
    ((s.towers T).scalar
      (spIntegralReductionScalar l E T (s.reduction T).coefficient n)).model.E

/-- The strict reduction functor in the sequence-site coordinates, before derivation.
Source: blueprint, strict tensor tower (blueprint: det-sp-integral-direct-image-tower). -/
abbrev ordinaryReduction (s : Presentation l E) (T : Scheme.{u}) :=
  (spIntegralModuleEquivalence l E T).functor ⋙
    (s.reduction T).ordinary ⋙ (s.base.realization T).functor

/-- The same reduction after localization, retaining every transition.
Source: blueprint, strict reduction (blueprint: det-sp-integral-direct-image-tower). -/
abbrev derivedReduction (s : Presentation l E) (T : Scheme.{u}) :=
  red l E s T ⋙ (realization l E s T).functor

/-- Ordinary evaluation transports with identity on every underlying section.
Source: blueprint, sectionwise tower realization
(blueprint: det-sp-integral-direct-image-tower). -/
structure Evaluation (s : Presentation l E) where
  ordinary : ∀ (T : Scheme.{u}) (n : ℕ),
    (s.base.realization T).functor ⋙ SpTowerShriek.ev l E T n ≅
      spCoefficientEvaluation l E T (s.towers T).equivalence n
  sections : ∀ (T : Scheme.{u}) (n : ℕ) (C : spCoefficientTowers l E T)
    (U : T.ProEtᵒᵖ) (x : ((SpTowerShriek.ev l E T n).obj
      ((s.base.realization T).functor.obj C)).val.obj U),
    HEq (((ordinary T n).hom.app C).val.app U x) x

/-- Derived evaluation is the localization of that sectionwise identity.
Source: blueprint, evaluation comparison (blueprint: det-sp-integral-direct-image-tower). -/
def Evaluation.derived (s : Presentation l E) (e : Evaluation l E s)
    (T : Scheme.{u}) (n : ℕ) :
    (realization l E s T).functor ⋙ SpTowerShriek.Ev l E T n ≅
      spDerivedCoefficientEvaluation l E T (s.towers T) n :=
  letI := (s.towers T).hasDerived
  letI := s.base.realizationAdditive T
  letI := (s.towers T).equivalenceAdditive
  letI := (s.towers T).evaluationLimits n
  letI := (s.towers T).evaluationColimits n
  letI := Functor.additive_of_preserves_binary_products
    (spCoefficientEvaluation l E T (s.towers T).equivalence n)
  (Functor.mapDerivedCategoryCompIso (s.base.realization T).functor
      (SpTowerShriek.ev l E T n)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (e.ordinary T n)

/-- Ordinary scalar evaluation of strict reduction, with the existing tensor generator.
Source: blueprint, quotient tensor (blueprint: det-sp-integral-direct-image-tower). -/
def ordinaryReductionEvaluation (s : Presentation l E) (e : Evaluation l E s)
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

/-- The canonical pullback comparison on an actual complex.
Source: blueprint, uncompleted inverse image
(blueprint: det-sp-integral-direct-image-tower). -/
def pullComplexComparison {X Y : Scheme.{u}} (f : X ⟶ Y)
    (P : CochainComplex (Modules l E Y) ℤ) :
    (pull l E f).obj (DerivedCategory.Q.obj P) ≅
      DerivedCategory.Q.obj
        (((CondensedRing.upperStar (spIntegralCondensed l E) f).mapHomologicalComplex
          (.up ℤ)).obj P) :=
  (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
    (spIntegralCondensed l E) f).app (DerivedCategory.Q.obj P) ≪≫
    (CondensedRing.upperStar (spIntegralCondensed l E) f).mapDerivedCategoryFactors.app P

/-- The universal reduction counit on a complex, transported without any choice of map.
Source: blueprint, K-flat reduction (blueprint: det-sp-integral-direct-image-tower). -/
def reductionComplexComparison (s : Presentation l E) (T : Scheme.{u})
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
(blueprint: det-sp-integral-direct-image-tower). -/
def ordinaryPullLevelMap (s : Presentation l E) (e : Evaluation l E s)
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
(blueprint: det-sp-integral-direct-image-tower). -/
structure ReductionPull (s : Presentation l E) (e : Evaluation l E s)
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
Source: blueprint, proof (2)--(3) (blueprint: det-sp-integral-direct-image-tower). -/
structure ReductionGeometry (s : Presentation l E) where
  evaluation : Evaluation l E s
  pullback : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), ReductionPull l E s evaluation f

/-- The proper coefficient comparison is the transpose of the integral counit through
exactly the recorded tower geometric adjunction.
Source: blueprint, proof (2) (blueprint: det-sp-integral-direct-image-tower). -/
def properReduction (s : Presentation l E) (q : ReductionGeometry l E s)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Integral l E X) :=
  ((SpTowerShriek.adjunction l E s.base (s.operations.geometry f)).homEquiv _ _)
    ((q.pullback f).derived.inv.app
        ((CondensedRing.lowerStar (spIntegralCondensed l E) f).rightDerivedFunctor.obj N) ≫
      (derivedReduction l E s X).map
        ((CondensedRing.derivedUpperStarLowerStarAdjunction
          (spIntegralCondensed l E) f).counit.app N))

/-- The inverse open coefficient comparison is the transpose of the integral open unit
through exactly the recorded strict-system open adjunction.
Source: blueprint, proof (2) (blueprint: det-sp-integral-direct-image-tower). -/
def openReductionInverse (s : Presentation l E) (q : ReductionGeometry l E s)
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
Source: blueprint, exact open extension (blueprint: det-sp-integral-direct-image-tower). -/
def OpenReductionIsIso (s : Presentation l E) (q : ReductionGeometry l E s) : Prop :=
  ∀ {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] (N : Integral l E U),
    IsIso (openReductionInverse l E s q j N)

/-- The integral-to-strict-tower base-change map: proper counit mate, then the inverse
open-unit mate. Every map is constructed before any invertibility assertion for f_!.
Source: blueprint, proof (2) (blueprint: det-sp-integral-direct-image-tower). -/
def towerBaseChange (s : Presentation l E) (q : ReductionGeometry l E s)
    (hq : OpenReductionIsIso l E s q)
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
Source: blueprint, finite Rf_! (blueprint: det-sp-integral-direct-image-tower). -/
def finiteComparison (s : Presentation l E) (e : Evaluation l E s)
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
Source: blueprint, clause (2) (blueprint: det-sp-integral-direct-image-tower). -/
def finiteBaseChange (s : Presentation l E) (q : ReductionGeometry l E s)
    (hq : OpenReductionIsIso l E s q)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Integral l E X) (n : ℕ) :
    (level l E s Y n).obj ((shriek l E c).obj M) ⟶
      (finiteShriek l E s c n).obj ((level l E s X n).obj M) :=
  (spDerivedCoefficientEvaluation l E Y (s.towers Y) n).map
      (towerBaseChange l E s q hq c M) ≫
    (finiteComparison l E s q.evaluation c n).hom.app ((red l E s X).obj M)

/-- Whole-tower invertibility of the constructed mate on the constructible domain.
The equality pins the entire arrow, including any morphisms invisible to evaluation.
Source: blueprint, clause (2) (blueprint: det-sp-integral-direct-image-tower). -/
structure CanonicalTowerComparison (s : Presentation l E) (q : ReductionGeometry l E s)
    (hq : OpenReductionIsIso l E s q)
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) where
  iso : TowerComparison l E s c
  hom_eq : ∀ M : Constructible l E X, iso.hom.app M = towerBaseChange l E s q hq c M.obj

/-- The canonical reconstruction arrow: the normalized completion unit followed by
limit of the constructed proper/open mate. No isomorphism field defines this arrow.
Source: blueprint, clause (2) and proof paragraphs (2)--(3)
(blueprint: det-sp-integral-direct-image-tower). -/
def reconstruction (s : Presentation l E) {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) (L : Limit l E s Y)
    (q : ReductionGeometry l E s) (hq : OpenReductionIsIso l E s q)
    (M : Constructible l E X) :
    (shriek l E c).obj M.obj ⟶
      (lim l E s Y L).obj (imageTower l E s c M.obj) :=
  (redLimitAdjunction l E s Y L).unit.app ((shriek l E c).obj M.obj) ≫
    (lim l E s Y L).map (towerBaseChange l E s q hq c M.obj)

/-- Pullback reductions use the same representative-normalized strict comparison,
then the published pullEvaluation. This fixes the finite comparison in clause (3).
Source: blueprint, clause (3) (blueprint: det-sp-integral-direct-image-tower). -/
def pullbackLevelComparison (s : Presentation l E) (q : ReductionGeometry l E s)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : Integral l E Y) (n : ℕ) :
    (level l E s X n).obj ((pull l E f).obj K) ≅
      (Scheme.proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) f).obj
        ((level l E s Y n).obj K) :=
  ((Evaluation.derived l E s q.evaluation X n).app
      ((red l E s X).obj ((pull l E f).obj K))).symm ≪≫
    (SpTowerShriek.Ev l E X n).mapIso ((q.pullback f).derived.app K) ≪≫
    ((s.operations.geometry f).pullEvaluation n).app ((derivedReduction l E s Y).obj K) ≪≫
    (Scheme.proEtaleConstantRingDerivedPullback (SpTowerShriek.R l E n) f).mapIso
      ((Evaluation.derived l E s q.evaluation Y n).app ((red l E s Y).obj K))

/-- The open factor in the separately derived compact-support composite.
Source: blueprint, clause (2) (blueprint: det-sp-integral-direct-image-tower). -/
abbrev openD {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :
    Integral l E U ⥤ Integral l E T :=
  (CondensedRing.openImmersionLowerShriek (spIntegralCondensed l E) j).mapDerivedCategory

/-- The exact derived open adjunction, expressed using total derived inverse image.
Source: blueprint, clause (3) (blueprint: det-sp-integral-direct-image-tower). -/
def openAdjunction {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j] :=
  (CondensedRing.derivedOpenImmersionLowerShriekUpperStarAdjunction
    (spIntegralCondensed l E) j).ofNatIsoRight
      (CondensedRing.leftDerivedUpperStarIsoMapDerivedCategory
        (spIntegralCondensed l E) j).symm

/-- The canonical open projection arrow: the transpose of unit tensor identity,
followed by the inverse K-flat pullback/tensor comparison.
Source: blueprint, clause (3) (blueprint: det-sp-integral-direct-image-tower). -/
def openProjection {U T : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]
    (M : Integral l E U) (K : Integral l E T) :
    (openD l E j).obj (((tensor l E U).obj M).obj ((pull l E j).obj K)) ⟶
      ((tensor l E T).obj ((openD l E j).obj M)).obj K :=
  ((openAdjunction l E j).homEquiv _ _).symm
    ((((tensor l E U).map ((openAdjunction l E j).unit.app M)).app
        ((pull l E j).obj K)) ≫
      ((CondensedRing.leftDerivedUpperStarTensorIso (spIntegralCondensed l E) j).inv.app
        ((CondensedRing.openImmersionLowerShriek (spIntegralCondensed l E) j)
          |>.mapDerivedCategory.obj M)).app K)

/-- The common middle object of the proper and open projection mates.
Source: blueprint, clause (3) (blueprint: det-sp-integral-direct-image-tower). -/
def projectionMiddle {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Integral l E X) (K : Integral l E Y) : Integral l E Y :=
  (CondensedRing.lowerStar (spIntegralCondensed l E) c.g).rightDerivedFunctor.obj
    (((tensor l E c.Z).obj ((openD l E c.i).obj M)).obj ((pull l E c.g).obj K))

/-- The proper projection mate at j_!M.
Source: blueprint, clause (3) (blueprint: det-sp-integral-direct-image-tower). -/
def properProjection {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Integral l E X) (K : Integral l E Y) :
    ((tensor l E Y).obj ((shriek l E c).obj M)).obj K ⟶ projectionMiddle l E c M K :=
  CondensedRing.moduleObjectProjectionMap (spIntegralCondensed l E) c.g
    ((openD l E c.i).obj M) K

/-- The canonical pullback factorization belonging to the compactification.
Source: blueprint, clause (3) (blueprint: det-sp-integral-direct-image-tower). -/
def pullFactor {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    pull l E f ≅ pull l E c.g ⋙ pull l E c.i :=
  eqToIso (congrArg (fun h ↦ pull l E h) c.comm) ≪≫
    CondensedRing.leftDerivedUpperStarComp (spIntegralCondensed l E) c.i c.g

/-- The open projection mate, pushed forward properly, after the specified pullback
factorization. Together with properProjection it is the canonical projection span
Rf_!M tensor K -> Rp_*(j_!M tensor p^*K) <- Rf_!(M tensor f^*K).
Source: blueprint, clause (3) (blueprint: det-sp-integral-direct-image-tower). -/
def compactOpenProjection {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    (M : Integral l E X) (K : Integral l E Y) :
    (shriek l E c).obj (((tensor l E X).obj M).obj ((pull l E f).obj K)) ⟶
      projectionMiddle l E c M K :=
  (shriek l E c).map (((tensor l E X).obj M).map ((pullFactor l E c).hom.app K)) ≫
    (CondensedRing.lowerStar (spIntegralCondensed l E) c.g).rightDerivedFunctor.map
      (openProjection l E c.i M ((pull l E c.g).obj K))

/-- All three clauses of the integral tower description, with canonical strict tower
comparisons, completed-coefficient inverse limit, natural compactification comparisons,
and the actual proper and open projection mates.

Source: blueprint main-20261015,
sec-smooth-purity/sk-prop-sp-integral-adjunction/direct-image, clauses (1)--(3);
Stacks 09BP (blueprint: det-sp-integral-direct-image-tower).

Proof, following the eight DAG steps:
1. Use the completed-condensed coefficient comparison and cofinal ell/uniformizer
powers. The standing schemes are Noetherian. The integral-model criterion gives
finite Tor amplitude and derived completeness of M. Reduction-tower-normalized
makes red_X M a normalized constructible strict derived tower with the same Tor bounds.
2. First construct the scalar/pullback map on local generators: 1 tensor f*(x)
goes to f*(1 tensor x), using the specified geometric units. Assemble the ordinary
strict map since these formulas commute with every quotient transition. Localize
on flat-term K-flat representatives, using the recorded reduction counit and exact
pullback comparison; this gives ReductionGeometry with its representative equation.
The exact slice tensor identity makes openReductionInverse invertible. Transpose
the integral proper counit and open unit through the recorded strict adjunctions;
their composite is towerBaseChange. Its evaluations use the actual Fcomparison.
Tower-shriek-levels evaluates its compact-support image as the finite Rf_! values.
Tower-bound-uniform gives common Tor interval [a,b+2d] and constructibility. The
reduction transitions are the finite coefficient direct-image comparison followed
by Rf_! of the input reduction maps; reduction-direct-image makes both invertible.
The semilinear-derived-sections model fixes these as actual tower maps and cocycles.
3. Completion identifies M with Rlim red_X M. The compactification open is
quasi-compact by the Nagata open-immersion criterion. Open-closed-extension-zero-limits
and ringed-tower-pushforward-limit-comparison commute its two separate derived
factors with the strict inverse limit, preserving projections. Derived pushforward
composition identifies every finite term after restriction of scalars to R_Y.
4. Tower reconstruction gives bounded integral constructibility of that limit.
The adjunction/counit clauses of normalized-equivalence identify its reduction
with the original normalized strict tower. Evaluating yields all finite reductions.
The normalized derived adjunction above identifies reconstruction with the completion
unit followed by the limit of the same constructed strict tower comparison.
5. Compactification-coherence-cocycle applies on the ambient localizing closure:
O_E is admissible, Dbc equals Dctf by integral-models, and the localizing closure
contains Dctf. Restrict its natural comparisons to Dbc. Their common-dense-refinement
normalization, identity and cocycle persist in this full subcategory.
6. Integral-tensor-pullback preserves Dbc without completion. The canonical
ringed-topoi-derived-tensor-pullback comparison, computed on K-flat representatives,
commutes with the actual quotient maps, giving the stated pullback reductions.
7. Integral-tensor-product closes Dbc under ordinary relative derived tensor.
On flat-term K-flat Q,Q', the map (q tensor a) tensor (q' tensor b) maps to
(q tensor q') tensor ab, with inverse inserting 1. K-flat change of rings and
site-derived-tensor-descent give a comparison of strict reduction towers.
8. Apply tower-compact-support-projection-formula to red_X M and red_Y K over the
arbitrary standing field. Its proper counit and open unit mates are invertible.
Steps 2--7 identify their limits with the actual integral mates displayed here.
Integral completeness detects their invertibility; both projection endpoints lie
in Dbc. The inverse of the open mate composed with the proper mate gives the
projection isomorphism, or its inverse in the direction displayed in the source.
-/
theorem integral_direct_image_tower (s : Presentation l E) :
    ∃ (q : ReductionGeometry l E s) (hq : OpenReductionIsIso l E s q),
    ∃ L : ∀ T : Scheme.{u}, Limit l E s T,
    ∀ (k : Type u) [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
      (X Y : Scheme.{u}) [X.Over (Spec (.of k))]
      [Y.Over (Spec (.of k))]
      [LocallyOfFiniteType (X ↘ Spec (.of k))]
      [QuasiCompact (X ↘ Spec (.of k))]
      [IsSeparated (X ↘ Spec (.of k))]
      [LocallyOfFiniteType (Y ↘ Spec (.of k))]
      [QuasiCompact (Y ↘ Spec (.of k))]
      [IsSeparated (Y ↘ Spec (.of k))]
      (f : X ⟶ Y) [f.IsOver (Spec (.of k))]
      (d : ℕ) [SmoothOfRelativeDimension d f],
    (∃ φ : ∀ c₁ c₂ : Compactification f,
        (constantModelBoundedConstructible (spIntegralCondensed l E) X).ι ⋙ shriek l E c₁ ≅
          (constantModelBoundedConstructible (spIntegralCondensed l E) X).ι ⋙ shriek l E c₂,
      (∀ c : Compactification f, φ c c = Iso.refl _) ∧
      (∀ c₁ c₂ c₃ : Compactification f, φ c₁ c₂ ≪≫ φ c₂ c₃ = φ c₁ c₃) ∧
      ∀ (c₁ c₂ : Compactification.BoundaryCompactification f)
        (r : Compactification.DenseBoundaryCompactification f)
        (h₁ : r.obj ⟶ c₁) (h₂ : r.obj ⟶ c₂) (M : Constructible l E X),
        (φ c₁.obj.obj c₂.obj.obj).hom.app M ≫
          CondensedRing.compactificationRefinementComponent (spIntegralCondensed l E) h₂ M.obj =
        CondensedRing.compactificationRefinementComponent (spIntegralCondensed l E) h₁ M.obj) ∧
    ∀ c : Compactification f,
      ∃ _v : CanonicalTowerComparison l E s q hq c,
      (∀ M : Constructible l E X,
        spNormalizedConstructibleTorTowers l E Y (s.towers Y)
          (imageTower l E s c M.obj) ∧
        (∀ a b : ℤ,
          DerivedCategory.torAmplitudeIn _ a b M.obj → ∀ n : ℕ,
          Scheme.HasProEtaleTorAmplitude Y (SpTowerShriek.R l E n)
            (imageLevel l E s c M.obj n) a (b + 2 * d)) ∧
        constantModelBoundedConstructible (spIntegralCondensed l E) Y
          ((shriek l E c).obj M.obj) ∧
        constantModelBoundedConstructible (spIntegralCondensed l E) Y
          ((lim l E s Y (L Y)).obj
            (imageTower l E s c M.obj)) ∧
        IsIso (reconstruction l E s c (L Y) q hq M) ∧
        ∀ n : ℕ, IsIso (finiteBaseChange l E s q hq c M.obj n)) ∧
      (∀ K : Constructible l E Y,
        constantModelBoundedConstructible (spIntegralCondensed l E) X
          ((pull l E f).obj K.obj)) ∧
      ∀ (M : Constructible l E X) (K : Constructible l E Y),
        constantModelBoundedConstructible (spIntegralCondensed l E) Y
          ((shriek l E c).obj
            (((tensor l E X).obj M.obj).obj ((pull l E f).obj K.obj))) ∧
        constantModelBoundedConstructible (spIntegralCondensed l E) Y
          (((tensor l E Y).obj ((shriek l E c).obj M.obj)).obj K.obj) ∧
        IsIso (properProjection l E c M.obj K.obj) ∧
        IsIso (compactOpenProjection l E c M.obj K.obj) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralDirectImageTower


