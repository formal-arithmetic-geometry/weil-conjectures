/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q58
-/
module

public import Sheaf.Paper.RingedStrictTowerProjectionMorphism
public import Sheaf.Paper.RingedExchangeTensorCoherence
public import Sheaf.Paper.StrictPerfectCoefficientPackageOfUniverses
public import Sheaf.CategoryTheory.TowerDerivedEvaluationNormalization
public import Sheaf.CategoryTheory.DiagramSiteRealization
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.RingedComparisonTensorAdjunction

/-! # The strict perfect-coefficient exchange and its coaugmentation

Source: Stacks Project, sites-cohomology.tex, Tags 0E48 and 0944;
strict augmented perfect-diagram refinement, agent supplied
(blueprint: def-sbc-strict-augmented-coefficient-presentation).

All towers are objects of the derived category of strict module diagrams.
The presentation data below fix maps on complexes before localization.

## Main definitions and statements

`Reduction`, `PullReduction`, `TowerAdjunction`, and `Coefficients` specify the
normalized coefficient data and canonical ordinary/derived comparisons.
-/

@[expose] public noncomputable section

set_option autoImplicit false
-- Keep normalized representative proofs in the public definitions.
set_option backward.proofsInPublic true
set_option synthInstance.maxSize 2048
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genCtorIdx false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w uData vData wData xData yData zData

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.StrictQuotientExchange

/-- Reassemble a strict sequence of complexes as a complex of strict sequences.
Source: Stacks 0A07 (blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
abbrev reassemble (A : RingedTensorCorner.{u, w}) :=
  (HomologicalComplex.functorEquivalence A.mateModules (.up ℤ) ℕᵒᵖ).inverse

/-- The ordinary tensor with a fixed strict coefficient sequence, with direct-sum totalization.
Source: Stacks 0944 (blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
def total (A : RingedTensorCorner.{u, w})
    (Q : ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ) :
    CochainComplex A.mateModules ℤ ⥤ CochainComplex A.projectionTowers ℤ :=
  A.projectionTotal ⋙
    (Functor.whiskeringRight ℕᵒᵖ _ _ ) ⋙
    (CategoryTheory.evaluation (ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ)
      (ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ)).obj Q ⋙ reassemble A

/-- The exact constant-sequence functor, localized only after forming the sequence category.
Source: Stacks 0A07 (blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
abbrev delta (A : RingedTensorCorner.{u, w})
    [HasDerivedCategory.{w} A.projectionTowers] :=
  ((Functor.const ℕᵒᵖ : A.mateModules ⥤ A.projectionTowers)).mapDerivedCategory

/-- Total-derived reduction data with canonical augmentation, over abstract data types.
Its predicates below are the unchanged concrete representative equations.
Source: Stacks 0944, 0A07
(blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
structure ReductionData (F : Type uData) (E : F → Type vData) (I : F → Type wData)
    (D C : (f : F) → E f → Prop)
    (N : (f : F) → E f → I f → Prop) where
  functor : F
  epsilon : E functor
  derived : D functor epsilon
  computes : C functor epsilon
  augmentation : I functor
  augmentation_normalized : N functor epsilon augmentation

/-- The concrete representative normalization predicate.
Source: Stacks 0944, 0A07
(blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
def reductionDerived (A : RingedTensorCorner.{u, w})
    [HasDerivedCategory.{w} A.projectionTowers]
    (Q : ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ)
    (_z : (Functor.const ℕᵒᵖ).obj A.mateUnitComplex ⟶ Q) : (f : (A.mateDerived ⥤ DerivedCategory
      A.projectionTowers)) → (fun functor ↦ DerivedCategory.Q ⋙ functor ⟶ total A Q ⋙
      DerivedCategory.Q) f → Prop :=
  (fun functor epsilon ↦ functor.IsLeftDerivedFunctor epsilon
    (HomologicalComplex.quasiIso A.mateModules (.up ℤ)))

/-- The concrete representative normalization predicate.
Source: Stacks 0944, 0A07
(blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
def reductionComputes (A : RingedTensorCorner.{u, w})
    [HasDerivedCategory.{w} A.projectionTowers]
    (Q : ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ)
    (_z : (Functor.const ℕᵒᵖ).obj A.mateUnitComplex ⟶ Q) : (f : (A.mateDerived ⥤ DerivedCategory
      A.projectionTowers)) → (fun functor ↦ DerivedCategory.Q ⋙ functor ⟶ total A Q ⋙
      DerivedCategory.Q) f → Prop :=
  (fun _ epsilon ↦ ∀ P : CochainComplex A.mateModules ℤ, A.mateFlat P → IsIso (epsilon.app P))

/-- The concrete representative normalization predicate.
Source: Stacks 0944, 0A07
(blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
def reductionAugmentationNormalized (A : RingedTensorCorner.{u, w})
    [HasDerivedCategory.{w} A.projectionTowers]
    (Q : ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ)
    (z : (Functor.const ℕᵒᵖ).obj A.mateUnitComplex ⟶ Q) : (f : (A.mateDerived ⥤ DerivedCategory
      A.projectionTowers)) → (fun functor ↦ DerivedCategory.Q ⋙ functor ⟶ total A Q ⋙
      DerivedCategory.Q) f → (fun functor ↦ delta A ⟶ functor) f → Prop :=
  (fun _ epsilon augmentation ↦ ∀ (P : CochainComplex A.mateModules ℤ), A.mateFlat P →
    ∃ i : ((Functor.const ℕᵒᵖ : A.mateModules ⥤ A.projectionTowers).mapHomologicalComplex
        (.up ℤ)).obj P ⟶ (total A Q).obj P,
      (∀ (n : ℕᵒᵖ) (r : ℤ), (i.f r).app n =
        ((A.projectionRightUnitor P).inv ≫ (A.projectionTotal.obj P).map (z.app n)).f r) ∧
      augmentation.app (DerivedCategory.Q.obj P) ≫ epsilon.app P =
        ((Functor.const ℕᵒᵖ : A.mateModules ⥤
          A.projectionTowers).mapDerivedCategoryFactors).hom.app P ≫ DerivedCategory.Q.map i)

/-- The normalized presentation using its named representative predicates.
Source: Stacks 0944, 0A07
(blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
abbrev Reduction (A : RingedTensorCorner.{u, w})
    [HasDerivedCategory.{w} A.projectionTowers]
    (Q : ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ)
    (z : (Functor.const ℕᵒᵖ).obj A.mateUnitComplex ⟶ Q) :=
  ReductionData
    (A.mateDerived ⥤ DerivedCategory A.projectionTowers)
    (fun functor ↦ DerivedCategory.Q ⋙ functor ⟶ total A Q ⋙ DerivedCategory.Q)
    (fun functor ↦ delta A ⟶ functor)
    (reductionDerived A Q z)
    (reductionComputes A Q z)
    (reductionAugmentationNormalized A Q z)

/-- A specified j and its ordinary representative normalization.
The generic record keeps the mathematical datum unchanged.
Source: Stacks 0A07, 07A6
(blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
structure ConstantLimitData (D : Type uData) (P : D → Prop) where
  j : D
  normalized : P j

/-- The concrete representative normalization predicate.
Source: Stacks 0944, 0A07
(blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
def constantLimitNormalized (A : RingedTensorCorner.{u, w})
    [HasDerivedCategory.{w} A.projectionTowers]
    [HasCountableProducts A.mateDerived] (l : StrictProjectionLimit A) : (𝟭 A.mateDerived ≅ delta
      A ⋙ l.L) → Prop :=
  letI : (lim : A.projectionTowers ⥤ A.mateModules).Additive :=
    (constLimAdj : (Functor.const ℕᵒᵖ : A.mateModules ⥤ A.projectionTowers) ⊣
      lim).right_adjoint_additive
  (fun j ↦ ∀ P : CochainComplex A.mateModules ℤ,
    j.hom.app (DerivedCategory.Q.obj P) ≫
        l.L.map (((Functor.const ℕᵒᵖ : A.mateModules ⥤
          A.projectionTowers).mapDerivedCategoryFactors).hom.app P) =
      DerivedCategory.Q.map
        (((constLimAdj : (Functor.const ℕᵒᵖ : A.mateModules ⥤ A.projectionTowers) ⊣
          lim).mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        l.eta.app (((Functor.const ℕᵒᵖ : A.mateModules ⥤
          A.projectionTowers).mapHomologicalComplex (.up ℤ)).obj P))

/-- The normalized presentation using its named representative predicates.
Source: Stacks 0944, 0A07
(blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
abbrev ConstantLimit (A : RingedTensorCorner.{u, w})
    [HasDerivedCategory.{w} A.projectionTowers]
    [HasCountableProducts A.mateDerived] (l : StrictProjectionLimit A) :=
  ConstantLimitData
    (𝟭 A.mateDerived ≅ delta A ⋙ l.L)
    (constantLimitNormalized A l)

/-- Completion with the given coefficient sequence; no reflector property is imposed.
Source: Stacks 0A07 (blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
abbrev completion {A : RingedTensorCorner.{u, w}}
    [HasDerivedCategory.{w} A.projectionTowers] [HasCountableProducts A.mateDerived]
    {Q : ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ}
    {z : (Functor.const ℕᵒᵖ).obj A.mateUnitComplex ⟶ Q}
    (r : Reduction A Q z) (l : StrictProjectionLimit A) := r.functor ⋙ l.L

/-- The specified strict augmentation followed by total derived inverse limit.
Source: Stacks 0A07 (blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
def kappa {A : RingedTensorCorner.{u, w}}
    [HasDerivedCategory.{w} A.projectionTowers] [HasCountableProducts A.mateDerived]
    {Q : ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ}
    {z : (Functor.const ℕᵒᵖ).obj A.mateUnitComplex ⟶ Q}
    (r : Reduction A Q z) (l : StrictProjectionLimit A) (j : ConstantLimit A l) :
    𝟭 A.mateDerived ⟶ completion r l :=
  j.j.hom ≫ Functor.whiskerRight r.augmentation l.L

/-- The exact inverse image on strict diagrams, then localized.
Source: Stacks 0A07 (blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
abbrev towerLeft {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
    [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
    [HasDerivedCategory.{w} A.projectionTowers]
    [HasDerivedCategory.{w} B.projectionTowers] :=
  (projectionPost (I := ℕᵒᵖ) e.pullback).mapDerivedCategory

/-- The canonical tensor comparison on ordinary total complexes, in pullback direction.
Source: Stacks 07A4 (blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
def chainTensorPullback {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
    (P Q : CochainComplex A.mateModules ℤ) :=
  (e.ordinaryTensor.totalIso A.ring B.ring e.inverseRing e.inverse e.algebraic
    e.ringMap e.pullback e.object_eq e.pushforward e.moduleAdjunction P Q).inv

/-- A pair of specified comparisons with their representative normalizations.
The generic record avoids duplicating large categorical types in generated recursors.
Source: Stacks 07A4, 0944
(blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
structure PullReductionData (A : Type uData) (B : Type vData)
    (z : A → Prop) (n : A → B → Prop) where
  coefficient : A
  coefficient_augmentation : z coefficient
  pull : B
  normalized : n coefficient pull

/-- The concrete representative normalization predicate.
Source: Stacks 0944, 0A07
(blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
def pullCoefficientNormalized {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
    [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
    [HasDerivedCategory.{w} A.projectionTowers]
    [HasDerivedCategory.{w} B.projectionTowers]
    {QA : ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ}
    {QB : ℕᵒᵖ ⥤ CochainComplex B.mateModules ℤ}
    {zA : (Functor.const ℕᵒᵖ).obj A.mateUnitComplex ⟶ QA}
    {zB : (Functor.const ℕᵒᵖ).obj B.mateUnitComplex ⟶ QB}
    (_rA : Reduction A QA zA) (_rB : Reduction B QB zB) : (QA ⋙ e.pullback.mapHomologicalComplex
      (.up ℤ) ≅ QB) → Prop :=
  (fun coefficient ↦ ∀ n : ℕᵒᵖ,
    e.projectionUnitComplex.inv ≫
      (e.pullback.mapHomologicalComplex (.up ℤ)).map (zA.app n) ≫
        coefficient.hom.app n = zB.app n)

/-- The concrete representative normalization predicate.
Source: Stacks 0944, 0A07
(blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
def pullReductionNormalized {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
    [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
    [HasDerivedCategory.{w} A.projectionTowers]
    [HasDerivedCategory.{w} B.projectionTowers]
    {QA : ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ}
    {QB : ℕᵒᵖ ⥤ CochainComplex B.mateModules ℤ}
    {zA : (Functor.const ℕᵒᵖ).obj A.mateUnitComplex ⟶ QA}
    {zB : (Functor.const ℕᵒᵖ).obj B.mateUnitComplex ⟶ QB}
    (rA : Reduction A QA zA) (rB : Reduction B QB zB) : (QA ⋙ e.pullback.mapHomologicalComplex
      (.up ℤ) ≅ QB) → (rA.functor ⋙ towerLeft e ≅ e.left ⋙ rB.functor) → Prop :=
  (fun coefficient pull ↦ ∀ (P : CochainComplex A.mateModules ℤ), A.mateFlat P →
    ∃ t : ((projectionPost (I := ℕᵒᵖ) e.pullback).mapHomologicalComplex (.up ℤ)).obj
          ((total A QA).obj P) ⟶
        (total B QB).obj ((e.pullback.mapHomologicalComplex (.up ℤ)).obj P),
      (∀ (n : ℕᵒᵖ) (r : ℤ), (t.f r).app n =
        (chainTensorPullback e P (QA.obj n) ≫
          (B.projectionTotal.obj ((e.pullback.mapHomologicalComplex (.up ℤ)).obj P)).map
            (coefficient.hom.app n)).f r) ∧
      pull.hom.app (DerivedCategory.Q.obj P) ≫
          rB.functor.map (derivedPullbackComplexComparison e.pullback e.left e.epsilon P) ≫
          rB.epsilon.app ((e.pullback.mapHomologicalComplex (.up ℤ)).obj P) =
        (towerLeft e).map (rA.epsilon.app P) ≫
          (projectionPost (I := ℕᵒᵖ) e.pullback).mapDerivedCategoryFactors.hom.app
            ((total A QA).obj P) ≫ DerivedCategory.Q.map t)

/-- The normalized presentation using its named representative predicates.
Source: Stacks 0944, 0A07
(blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
abbrev PullReduction {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
    [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
    [HasDerivedCategory.{w} A.projectionTowers]
    [HasDerivedCategory.{w} B.projectionTowers]
    {QA : ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ}
    {QB : ℕᵒᵖ ⥤ CochainComplex B.mateModules ℤ}
    {zA : (Functor.const ℕᵒᵖ).obj A.mateUnitComplex ⟶ QA}
    {zB : (Functor.const ℕᵒᵖ).obj B.mateUnitComplex ⟶ QB}
    (rA : Reduction A QA zA) (rB : Reduction B QB zB) :=
  PullReductionData
    (QA ⋙ e.pullback.mapHomologicalComplex (.up ℤ) ≅ QB)
    (rA.functor ⋙ towerLeft e ≅ e.left ⋙ rB.functor)
    (pullCoefficientNormalized e rA rB)
    (pullReductionNormalized e rA rB)

/-- A specified adjunction and its ordinary representative normalization.
The generic record keeps the mathematical datum unchanged.
Source: Stacks 0A07, 07A6
(blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
structure TowerAdjunctionData (D : Type uData) (P : D → Prop) where
  adjunction : D
  normalized : P adjunction

/-- The concrete representative normalization predicate.
Source: Stacks 0944, 0A07
(blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
def towerAdjunctionNormalized {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
    [e.pushforward.Additive]
    [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
    [HasDerivedCategory.{w} A.projectionTowers]
    [HasDerivedCategory.{w} B.projectionTowers]
    [HasCountableProducts A.mateDerived] [HasCountableProducts B.mateDerived]
    {lA : StrictProjectionLimit A} {lB : StrictProjectionLimit B}
    (d : StrictProjectionDirectImage e lB lA) : (towerLeft e ⊣ d.Rt) → Prop :=
  (fun adjunction ↦ ∀ (P : CochainComplex A.projectionTowers ℤ)
      (I : CochainComplex B.projectionTowers ℤ)
      (a : ((projectionPost (I := ℕᵒᵖ) e.pullback).mapHomologicalComplex (.up ℤ)).obj P ⟶ I),
    adjunction.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj I)
        ((projectionPost (I := ℕᵒᵖ) e.pullback).mapDerivedCategoryFactors.hom.app P ≫
          DerivedCategory.Q.map a) =
      DerivedCategory.Q.map
        (((e.moduleAdjunction.whiskerRight ℕᵒᵖ).mapHomologicalComplex (.up ℤ)).homEquiv
          P I a) ≫ d.towerEta.app I)

/-- The normalized presentation using its named representative predicates.
Source: Stacks 0944, 0A07
(blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
abbrev TowerAdjunction {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
    [e.pushforward.Additive]
    [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
    [HasDerivedCategory.{w} A.projectionTowers]
    [HasDerivedCategory.{w} B.projectionTowers]
    [HasCountableProducts A.mateDerived] [HasCountableProducts B.mateDerived]
    {lA : StrictProjectionLimit A} {lB : StrictProjectionLimit B}
    (d : StrictProjectionDirectImage e lB lA) :=
  TowerAdjunctionData
    (towerLeft e ⊣ d.Rt)
    (towerAdjunctionNormalized e d)

/-- The strict projection-formula map is the adjunct of the pullback comparison
followed by the ordinary counit, before applying derived inverse limit.
Source: Stacks 0944 (blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
def projection {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
    [e.pushforward.Additive]
    [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
    [HasDerivedCategory.{w} A.projectionTowers]
    [HasDerivedCategory.{w} B.projectionTowers]
    [HasCountableProducts A.mateDerived] [HasCountableProducts B.mateDerived]
    {QA : ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ}
    {QB : ℕᵒᵖ ⥤ CochainComplex B.mateModules ℤ}
    {zA : (Functor.const ℕᵒᵖ).obj A.mateUnitComplex ⟶ QA}
    {zB : (Functor.const ℕᵒᵖ).obj B.mateUnitComplex ⟶ QB}
    {rA : Reduction A QA zA} {rB : Reduction B QB zB}
    {lA : StrictProjectionLimit A} {lB : StrictProjectionLimit B}
    {d : StrictProjectionDirectImage e lB lA}
    (a : TowerAdjunction e d) (p : PullReduction e rA rB) (E : B.mateDerived) :
    rA.functor.obj (e.right.obj E) ⟶ d.Rt.obj (rB.functor.obj E) :=
  a.adjunction.homEquiv _ _
    (p.pull.hom.app (e.right.obj E) ≫ rB.functor.map (e.derivedAdjunction.counit.app E))

/-- The canonical identification of exact localization with the recorded derived pullback.
Source: Stacks 07A4 (blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
def exactLeft {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
    [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback] :
    e.pullback.mapDerivedCategory ≅ e.left :=
  letI := e.isLeftDerived
  (Functor.leftDerivedUnique e.pullback.mapDerivedCategory e.left e.epsilon
    e.pullback.mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso A.mateModules (.up ℤ))).symm

/-- The normalized inverse-image/evaluation comparison, including the exact-derived
comparison of the recorded ambient inverse image.
Source: Stacks 0A07 (blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
def leftEvaluation {A B : RingedTensorCorner.{u, w}} (e : RingedTensorEdge A B)
    [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
    [HasDerivedCategory.{w} A.projectionTowers]
    [HasDerivedCategory.{w} B.projectionTowers] (n : ℕᵒᵖ) :
    towerLeft e ⋙ ((CategoryTheory.evaluation ℕᵒᵖ B.mateModules).obj n).mapDerivedCategory ≅
      ((CategoryTheory.evaluation ℕᵒᵖ A.mateModules).obj n).mapDerivedCategory ⋙ e.left :=
  towerDerivedEvaluationInterchange e.pullback n ≪≫
    Functor.isoWhiskerLeft _ (exactLeft e)

variable {S T X Y : RingedTensorCorner.{u, w}}
  (f : RingedTensorEdge S X) (g : RingedTensorEdge S T)
  (h : RingedTensorEdge X Y) (e : RingedTensorEdge T Y)
  [PreservesFiniteLimits f.pullback] [PreservesFiniteColimits f.pullback]
  [PreservesFiniteLimits g.pullback] [PreservesFiniteColimits g.pullback]
  [PreservesFiniteLimits h.pullback] [PreservesFiniteColimits h.pullback]
  [PreservesFiniteLimits e.pullback] [PreservesFiniteColimits e.pullback]
  [HasDerivedCategory.{w} S.projectionTowers]
  [HasDerivedCategory.{w} T.projectionTowers]
  [HasDerivedCategory.{w} X.projectionTowers]
  [HasDerivedCategory.{w} Y.projectionTowers]

/-- The ordinary ring-compatible square, postcomposed on strict diagrams and then
localized by the canonical exact-functor comparisons.
Source: Stacks 0E48 (blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
def towerSquare (s : RingedTensorSquare S T X Y g f e h) :
    towerLeft f ⋙ towerLeft h ≅ towerLeft g ⋙ towerLeft e :=
  (Functor.mapDerivedCategoryCompIso (projectionPost (I := ℕᵒᵖ) f.pullback)
    (projectionPost (I := ℕᵒᵖ) h.pullback)).symm ≪≫
  Functor.mapDerivedCategoryNatIso
    ((Functor.whiskeringRight ℕᵒᵖ S.mateModules Y.mateModules).mapIso s.modules) ≪≫
  Functor.mapDerivedCategoryCompIso (projectionPost (I := ℕᵒᵖ) g.pullback)
    (projectionPost (I := ℕᵒᵖ) e.pullback)

variable [g.pushforward.Additive] [h.pushforward.Additive]
  [HasCountableProducts S.mateDerived] [HasCountableProducts T.mateDerived]
  [HasCountableProducts X.mateDerived] [HasCountableProducts Y.mateDerived]
  {lS : StrictProjectionLimit S} {lT : StrictProjectionLimit T}
  {lX : StrictProjectionLimit X} {lY : StrictProjectionLimit Y}
  {dg : StrictProjectionDirectImage g lT lS} {dh : StrictProjectionDirectImage h lY lX}

/-- The actual derived diagram-site square mate, computed in the category of strict towers.
Source: Stacks 0E48 (blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
def towerMate (s : RingedTensorSquare S T X Y g f e h)
    (ag : TowerAdjunction g dg) (ah : TowerAdjunction h dh) :
    dg.Rt ⋙ towerLeft f ⟶ towerLeft e ⋙ dh.Rt :=
  (mateEquiv ag.adjunction ah.adjunction
    (TwoSquare.mk (towerLeft f) (towerLeft g) (towerLeft h) (towerLeft e)
      (towerSquare f g h e s).hom)).natTrans

/-- A strict coefficient diagram, its augmentation and normalized derived reduction.
Source: Stacks 0E48, 0944
(blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
structure CoefficientAtData (D : Type uData) (Z : D → Type vData)
    (R : (Q : D) → Z Q → Type wData) where
  Q : D
  z : Z Q
  r : R Q z

/-- The coefficient presentation at one corner.
Source: Stacks 0E48, 0944
(blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
abbrev CoefficientAt (A : RingedTensorCorner.{u, w})
    [HasDerivedCategory.{w} A.projectionTowers] :=
  CoefficientAtData (ℕᵒᵖ ⥤ CochainComplex A.mateModules ℤ)
    (fun Q ↦ (Functor.const ℕᵒᵖ).obj A.mateUnitComplex ⟶ Q)
    (fun Q z ↦ Reduction A Q z)

/-- Four coefficient presentations, their pullback comparisons and strict square equation.
Source: Stacks 0E48, 0944
(blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
structure CoefficientSquareData (AS AT AX AY : Type uData)
    (PF : AS → AX → Type vData) (PG : AS → AT → Type vData)
    (PH : AX → AY → Type vData) (PE : AT → AY → Type vData)
    (Sq : (cs : AS) → (ct : AT) → (cx : AX) → (cy : AY) →
      PF cs cx → PG cs ct → PH cx cy → PE ct cy → Prop) where
  atS : AS
  atT : AT
  atX : AX
  atY : AY
  pf : PF atS atX
  pg : PG atS atT
  ph : PH atX atY
  pe : PE atT atY
  square : Sq atS atT atX atY pf pg ph pe

/-- The original strict coefficient square equation, named to avoid copying its type.
Source: Stacks 0E48, 0944
(blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
def coefficientSquareNormalized (s : RingedTensorSquare S T X Y g f e h)
    (cs : CoefficientAt S) (ct : CoefficientAt T)
    (cx : CoefficientAt X) (cy : CoefficientAt Y)
    (pf : PullReduction f cs.r cx.r) (pg : PullReduction g cs.r ct.r)
    (ph : PullReduction h cx.r cy.r) (pe : PullReduction e ct.r cy.r) : Prop :=
  ∀ n : ℕᵒᵖ,
    (h.pullback.mapHomologicalComplex (.up ℤ)).map (pf.coefficient.hom.app n) ≫
        ph.coefficient.hom.app n =
      s.complexComparison.hom.app (cs.Q.obj n) ≫
        (e.pullback.mapHomologicalComplex (.up ℤ)).map (pg.coefficient.hom.app n) ≫
        pe.coefficient.hom.app n

/-- An augmented strict coefficient diagram on the square. The last equation is the
specified ring-compatible square on the coefficient complexes, before localization.
Source: Stacks 0E48, 0944
(blueprint: def-sbc-strict-augmented-coefficient-presentation). -/
abbrev Coefficients (s : RingedTensorSquare S T X Y g f e h) :=
  CoefficientSquareData (CoefficientAt S) (CoefficientAt T) (CoefficientAt X) (CoefficientAt Y)
    (fun cs cx ↦ PullReduction f cs.r cx.r)
    (fun cs ct ↦ PullReduction g cs.r ct.r)
    (fun cx cy ↦ PullReduction h cx.r cy.r)
    (fun ct cy ↦ PullReduction e ct.r cy.r)
    (coefficientSquareNormalized f g h e s)


end SheafOfModules.StrictQuotientExchange
