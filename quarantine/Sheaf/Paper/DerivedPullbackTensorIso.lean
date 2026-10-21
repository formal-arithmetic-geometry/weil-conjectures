/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q45
-/
module

public import Sheaf.Paper.CompletedPullbackTensorComparison
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ProEtaleCanonicalTensorPullback
public import Sheaf.AlgebraicGeometry.ProEtaleOperations
public import Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
public import Sheaf.AlgebraicGeometry.SfIntrinsicRealizationTransport
public import Sheaf.Paper.IntegralPullbackComposition
import Sheaf.Paper.NormalizedDVRTower
import Mathlib.Algebra.Homology.BifunctorShift
import Sheaf.Paper.IntegralDerivedOperationsOnSlices
import Sheaf.Paper.GeneralAlgebraicallyClosedCoefficients
import Sheaf.Paper.SfIntegralConstructible
import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.SfDerivedComplete
import Sheaf.Paper.IntegralScalarExtensionUniverses
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.Paper.SfRationalizationKaroubi
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Sheaf.Paper.IntegralOperationsPreserveConstructible
import Sheaf.Paper.IntegralOperationsScalarComparisons
import Sheaf.Paper.IntegralOperationsWellDefined
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Sheaf.Paper.KFlatRingedToposPullback
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses
import Sheaf.CategoryTheory.ModulePullbackTensorIso
import Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent
import Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import Sheaf.Algebra.Homology.KFlatTotalTensorModel
import Sheaf.AlgebraicGeometry.ProEtaleConstantExact
import Sheaf.Paper.CoefficientExtensionReductionModel
import Sheaf.Paper.CompletedOperationTowerSubstitution
import Sheaf.Paper.IntegralCoherenceTower
import Sheaf.Paper.IntegralTowerLimitComparison
import Sheaf.Paper.ScalarExtensionTowerCoherence
import Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence

/-! # Derived pullback and derived tensor comparison

Source: `literature/stacks-project/sites-cohomology.tex`, Lemma 21.18.4
(Tag 07A4, label `lemma-pullback-tensor-product`), together with the integral,
rational, and algebraically closed coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso).

## Main definitions

* The four `canonical*PullbackTensor` families are the prescribed comparisons.
* The higher coherence predicates state equations on those same comparisons.

## Main statements

* `derivedPullbackTensorIso` packages naturality and the higher compatibilities.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

-- Residue fields only occur in hypotheses; avoid unfolding them during instance search.
attribute [local irreducible] Scheme.residueField

private theorem existsUnique_iso_of_eq {C : Type*} [Category* C]
    {A B A' B' : C} (hA : A = A') (hB : B = B') (e : A' ≅ B') :
    ∃! d : A ≅ B, HEq d.hom e.hom := by
  subst A'
  subst B'
  exact ⟨e, HEq.rfl, fun d hd ↦ Iso.ext (eq_of_heq hd)⟩

section HigherCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]

/-- The canonical completed composition family, normalized by every finite reduction.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorIntegralComposition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)] :
    (@constructibleIntegralPullback l _ E _ _ _ Z Y (h ≫ f) hZ hY) ≅
      (@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY) ⋙ (@constructibleIntegralPullback l _
        E _ _ _ Z X h hZ hX) :=
  (integralPullbackComposition l E).choose h f

/-- The canonical rational composition comparison on unchanged integral objects.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: localize the specified integral composition
  map and conjugate by the object equalities in rationalDerivedPullback_existsUnique. This fixes
  every component and its inverse, so the required isomorphism exists uniquely. -/
theorem pullbackTensorRationalComposition_existsUnique {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : sfRationalConstructibleCategory l E Y) :
    ∃! e : ((@rationalDerivedPullback l _ E _ _ _ Z Y (h ≫ f) hZ hY)).obj M ≅
      ((@rationalDerivedPullback l _ E _ _ _ Z X h hZ hX)).obj (((@rationalDerivedPullback l _ E _ _
        _ X Y f hX hY)).obj M),
      HEq e.hom ((sfRationalConstructibleLocalization l E Z).map
        (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app M.obj)) := by
  apply existsUnique_iso_of_eq
    ((rationalDerivedPullback_existsUnique l E (h ≫ f)).exists.choose_spec.2.1 M)
    ?_
    ((sfRationalConstructibleLocalization l E Z).mapIso
      ((pullbackTensorIntegralComposition l E f h).app M.obj))
  have hf (K) : (rationalDerivedPullback l E f).obj K =
      ⟨(constructibleIntegralPullback l E f).obj K.obj⟩ :=
    (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K
  have hh (K) : (rationalDerivedPullback l E h).obj K =
      ⟨(constructibleIntegralPullback l E h).obj K.obj⟩ :=
    (rationalDerivedPullback_existsUnique l E h).exists.choose_spec.2.1 K
  rw [hh, hf]
  rfl

/-- Rationalization of the finite-reduction-normalized integral composition.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorRationalComposition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : sfRationalConstructibleCategory l E Y) :=
  ((@pullbackTensorRationalComposition_existsUnique l _ E _ _ _ X Y Z f h hX hY hZ) M).exists.choose

/-- Common-stage composition, specified at every larger finite coefficient field.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: represent the rational composition at the
  stage of M. Conjugate by the three prescribed transition/pullback comparisons. Their scalar
  cocycles identify these representatives at every enlargement. The rational inverse gives an
  inverse class; the representative at the original stage determines the class uniquely. -/
theorem pullbackTensorCommonComposition_existsUnique {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :
    ∃! e : ((@commonStageDerivedPullback l _ Ω _ _ _ Z Y (h ≫ f) hZ hY)).obj M ≅
      ((@commonStageDerivedPullback l _ Ω _ _ _ Z X h hZ hX)).obj (((@commonStageDerivedPullback l _
        Ω _ _ _ X Y f hX hY)).obj M),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω) (hM : M.stage ≤ L),
        HEq e.hom (ofHom (commonStagePullbackObject l Ω (h ≫ f) M)
          (commonStagePullbackObject l Ω h (commonStagePullbackObject l Ω f M)) L hM hM
          ((commonStagePullbackComparison l Ω (h ≫ f) M L hM).hom ≫
            ((@pullbackTensorRationalComposition l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ X
              Y Z f h hX hY
              hZ)
              (M.toStage hM)).hom ≫
            ((@rationalDerivedPullback l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ Z
              X h hZ hX)).map
              (commonStagePullbackComparison l Ω f M L hM).inv ≫
            (commonStagePullbackComparison l Ω h
              (commonStagePullbackObject l Ω f M) L hM).inv)) := by
  sorry

/-- The composition isomorphism represented by the prescribed rational comparison.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorCommonComposition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω Y) :=
  ((@pullbackTensorCommonComposition_existsUnique l _ Ω _ _ _ X Y Z f h hX hY hZ) M).exists.choose

/-- Composition equation on the actual canonical integral comparison, with both transports.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalIntegralPullbackTensor_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : sfIntegralConstructibleCategory l E Y) : Prop :=
  ((@canonicalIntegralPullbackTensor l _ E _ _ _ Z Y (h ≫ f) hZ hY) M N).hom ≫
      ((@constructibleIntegralTensor l _ E _ _ _ Z hZ)).map (Prod.mkHom
        (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app M)
          (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app N)) =
    ((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app
      (((@constructibleIntegralTensor l _ E _ _ _
      Y hY)).obj
      (M,N)) ≫
      ((@constructibleIntegralPullback l _ E _ _ _ Z X h hZ hX)).map
        ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
      ((@canonicalIntegralPullbackTensor l _ E _ _ _ Z X h hZ hX)
        (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)
          (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj
          N)).hom

/-- Composition equation on the actual canonical rational comparison, with both transports.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalRationalPullbackTensor_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : sfRationalConstructibleCategory l E Y) : Prop :=
  ((@canonicalRationalPullbackTensor l _ E _ _ _ Z Y (h ≫ f) hZ hY) M N).hom ≫
      ((@rationalDerivedTensor l _ E _ _ _ Z hZ)).map (Prod.mkHom
        (((@pullbackTensorRationalComposition l _ E _ _ _ X Y Z f h hX hY hZ)
        M).hom) (((@pullbackTensorRationalComposition l _ E _ _ _ X Y Z f h hX hY hZ) N).hom)) =
    ((@pullbackTensorRationalComposition l _ E _ _ _ X Y Z f h hX hY hZ) (((@rationalDerivedTensor l
      _ E _ _ _ Y hY)).obj
      (M,N))).hom ≫
      ((@rationalDerivedPullback l _ E _ _ _ Z X h hZ hX)).map ((@canonicalRationalPullbackTensor l
        _ E _ _ _ X Y f hX hY) M N).hom ≫
      ((@canonicalRationalPullbackTensor l _ E _ _ _ Z X h hZ hX)
        (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj M) (((@rationalDerivedPullback l _
          E _ _ _ X Y f hX hY)).obj N)).hom

/-- Composition equation on the actual canonical commonstage comparison, with both transports.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalCommonStagePullbackTensor_composition {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y) : Prop :=
  ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ Z Y (h ≫ f) hZ hY) M N).hom ≫
      ((@commonStageDerivedTensor l _ Ω _ _ _ Z hZ)).map (Prod.mkHom
        (((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ)
        M).hom) (((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ) N).hom)) =
    ((@pullbackTensorCommonComposition l _ Ω _ _ _ X Y Z f h hX hY hZ) (((@commonStageDerivedTensor
      l _ Ω _ _ _ Y hY)).obj
      (M,N))).hom ≫
      ((@commonStageDerivedPullback l _ Ω _ _ _ Z X h hZ hX)).map
        ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M N).hom ≫
      ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ Z X h hZ hX)
        (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj M)
          (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj N)).hom

/-- Reduction of the actual completed tensor via its fixed Roos realization and counit.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorIntegralReductionTensor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W) :
    (pullbackTensorCalculus l E W).reduction.obj
      (((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,N)).obj ≅
    (pullbackTensorCalculus l E W).systemClosed.tensor.obj
      ((pullbackTensorCalculus l E W).reduction.obj M.obj,
       (pullbackTensorCalculus l E W).reduction.obj N.obj) :=
  (pullbackTensorCalculus l E W).reduction.mapIso
    ((pullbackTensorIntegralTensorModel l E W).app (M.obj,N.obj)) ≪≫
    @asIso _ _ _ _ ((pullbackTensorCalculus l E W).adjunction.counit.app
      ((pullbackTensorCalculus l E W).systemClosed.tensor.obj
        ((pullbackTensorCalculus l E W).reduction.obj M.obj,
         (pullbackTensorCalculus l E W).reduction.obj N.obj)))
      (((@pullbackTensorComparisonCounits l _ E _ _ _ W W (𝟙 W) hW hW) M N).1)

/-- Reduction of completed pullback via its actual normalized Roos model and counit.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorIntegralReductionPullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M : sfIntegralConstructibleCategory l E Y) :
    (pullbackTensorCalculus l E X).reduction.obj
      (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M).obj ≅
    (pullbackTensorSequenceDerived l E f).obj
      ((pullbackTensorCalculus l E Y).reduction.obj M.obj) :=
  letI := ((@pullbackTensorComparisonCounits l _ E _ _ _ X Y f hX hY) M M).2.1
  (pullbackTensorCalculus l E X).reduction.mapIso
    ((pullbackTensorIntegralPullbackModel l E f).app M.obj) ≪≫
    asIso ((pullbackTensorCalculus l E X).adjunction.counit.app _)

/-- The actual integral comparison reduces to the same coherent comparison at all levels.
Source: Stacks 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalIntegralPullbackTensor_reduction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) : Prop :=
  (pullbackTensorCalculus l E X).reduction.map
      ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom.hom ≫
    ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ X hX)
      (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)
      (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj N)).hom ≫
    (pullbackTensorCalculus l E X).systemClosed.tensor.map
      (Prod.mkHom ((@pullbackTensorIntegralReductionPullback l _ E _ _ _ X Y f hX hY) M).hom
        ((@pullbackTensorIntegralReductionPullback l _ E _ _ _ X Y f hX hY) N).hom) =
  ((@pullbackTensorIntegralReductionPullback l _ E _ _ _ X Y f hX hY)
      (((@constructibleIntegralTensor l _ E _ _ _ Y hY)).obj (M,N))).hom ≫
    (pullbackTensorSequenceDerived l E f).map
      ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ Y hY) M N).hom ≫
    (pullbackTensorSystemComparison l E f).hom.app
      ((pullbackTensorCalculus l E Y).reduction.obj M.obj,
       (pullbackTensorCalculus l E Y).reduction.obj N.obj)

/-- The integral associator is uniquely fixed in the coherent reduction category.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Reduction is fully faithful on
  derived-complete constructible objects: its unit is invertible by normalized DVR effectivity.
  Conjugate the specified coherent tensor associator by the actual reduction/tensor comparisons and
  lift along that fully faithful functor. Lift the inverse too; faithfulness gives the inverse
  identities and uniqueness. -/
theorem pullbackTensorIntegralAssociator_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (((@constructibleIntegralTensor l _
      E _ _ _ W hW)).obj (M,N),P)
      ≅
      ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,((@constructibleIntegralTensor l _ E
        _ _ _ W hW)).obj (N,P)),
      (pullbackTensorCalculus l E W).reduction.map e.hom.hom ≫
        ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) M
          (((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (N,P))).hom ≫
        (pullbackTensorCalculus l E W).systemClosed.tensor.map
          (Prod.mkHom (𝟙 _) ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) N P).hom) =
      ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW)
        (((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,N)) P).hom ≫
        (pullbackTensorCalculus l E W).systemClosed.tensor.map
          (Prod.mkHom ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) M N).hom (𝟙 _)) ≫
        ((pullbackTensorCalculus l E W).systemClosed.monoidal.associator
          ((pullbackTensorCalculus l E W).reduction.obj M.obj)
          ((pullbackTensorCalculus l E W).reduction.obj N.obj)
          ((pullbackTensorCalculus l E W).reduction.obj P.obj)).hom := by
  sorry

/-- The canonical completed associator, fixed by its coherent reduction.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorIntegralAssociator (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfIntegralConstructibleCategory l E W) :=
  ((@pullbackTensorIntegralAssociator_existsUnique l _ E _ _ _ W hW) M N P).exists.choose

/-- The rational associator is the actual localization of the integral map.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Use the object equalities in
  rationalDerivedTensor_existsUnique to identify the endpoints. Localize the preceding integral
  isomorphism and its inverse. The displayed equality fixes its hom, so the isomorphism is unique.
-/
theorem pullbackTensorRationalAssociator_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (((@rationalDerivedTensor l _ E _ _ _ W
      hW)).obj (M,N),P) ≅
      ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (M,((@rationalDerivedTensor l _ E _ _ _ W
        hW)).obj (N,P)),
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralAssociator l _ E _ _ _ W hW) M.obj N.obj P.obj).hom) := by
  have hT (MN) : (rationalDerivedTensor l E W).obj MN =
      ⟨(constructibleIntegralTensor l E W).obj (MN.1.obj,MN.2.obj)⟩ :=
    (rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 MN
  apply existsUnique_iso_of_eq ?_ ?_
    ((sfRationalConstructibleLocalization l E W).mapIso
      (pullbackTensorIntegralAssociator l E W M.obj N.obj P.obj))
  · rw [hT, hT]
    rfl
  · rw [hT, hT]
    rfl

/-- The localized integral associator.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorRationalAssociator (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : sfRationalConstructibleCategory l E W) :=
  ((@pullbackTensorRationalAssociator_existsUnique l _ E _ _ _ W hW) M N P).exists.choose

/-- The integral braiding is uniquely fixed in the coherent reduction category.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Reduction is fully faithful on
  derived-complete constructible objects: its unit is invertible by normalized DVR effectivity.
  Conjugate the specified coherent tensor Koszul symmetry by the actual reduction/tensor comparisons
  and lift along that fully faithful functor. Lift the inverse too; faithfulness gives the inverse
  identities and uniqueness. -/
theorem pullbackTensorIntegralBraiding_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,N) ≅
      ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (N,M),
      (pullbackTensorCalculus l E W).reduction.map e.hom.hom ≫
        ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) N M).hom =
      ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) M N).hom ≫
        (pullbackTensorBraiding (coefficientSequenceTopology (ProEt.topology W))
          (coefficientSequenceCommRingSheaf l E W)
          (pullbackTensorCalculus l E W).systemClosed
          (pullbackTensorCalculus l E W).systemTensorModel).hom.app
            ((pullbackTensorCalculus l E W).reduction.obj M.obj,
             (pullbackTensorCalculus l E W).reduction.obj N.obj) := by
  sorry

/-- The canonical completed braiding, fixed by its coherent reduction.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorIntegralBraiding (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfIntegralConstructibleCategory l E W) :=
  ((@pullbackTensorIntegralBraiding_existsUnique l _ E _ _ _ W hW) M N).exists.choose

/-- The rational braiding is the actual localization of the integral map.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Use the object equalities in
  rationalDerivedTensor_existsUnique to identify the endpoints. Localize the preceding integral
  isomorphism and its inverse. The displayed equality fixes its hom, so the isomorphism is unique.
-/
theorem pullbackTensorRationalBraiding_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (M,N) ≅
      ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (N,M),
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralBraiding l _ E _ _ _ W hW) M.obj N.obj).hom) := by
  apply existsUnique_iso_of_eq
    ((rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 (M,N))
    ((rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1 (N,M))
    ((sfRationalConstructibleLocalization l E W).mapIso
      (pullbackTensorIntegralBraiding l E W M.obj N.obj))

/-- The localized integral braiding.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorRationalBraiding (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : sfRationalConstructibleCategory l E W) :=
  ((@pullbackTensorRationalBraiding_existsUnique l _ E _ _ _ W hW) M N).exists.choose

/-- The left nested tensor expressed at an arbitrary common finite stage.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorCommonLeft (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : (commonStageTensorObject l Ω W
      (commonStageTensorObject l Ω W M N) P).stage ≤ L) :=
  commonStageTensorComparison l Ω W (commonStageTensorObject l Ω W M N) P L h ≪≫
    ((@rationalDerivedTensor l _
      (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
      hW)).mapIso
      (Iso.prod (commonStageTensorComparison l Ω W M N L (((Padic.finiteCoefficientFields_properties
        l Ω).1 (commonStageTensorObject l Ω W M N).stage P.stage).1.trans h)) (Iso.refl _))

/-- The right nested tensor expressed at an arbitrary common finite stage.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorCommonRight (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W)
    (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : (commonStageTensorObject l Ω W M
      (commonStageTensorObject l Ω W N P)).stage ≤ L) :=
  commonStageTensorComparison l Ω W M (commonStageTensorObject l Ω W N P) L h ≪≫
    ((@rationalDerivedTensor l _
      (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
      hW)).mapIso
      (Iso.prod (Iso.refl _) (commonStageTensorComparison l Ω W N P L
        (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage (commonStageTensorObject l Ω W N
        P).stage).2.trans h)))

/-- The common-stage associator has its prescribed representative at every larger field.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Conjugate the rational associator by the
  displayed transition/tensor comparisons. Their scalar-extension cocycles show independence of
  enlargement. The inverse formula gives an inverse class. Directedness supplies common stages, and
  a representative determines its colimit hom class uniquely. -/
theorem pullbackTensorCommonAssociator_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (((@commonStageDerivedTensor l _ Ω _ _
      _ W hW)).obj (M,N),P) ≅
      ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (M,((@commonStageDerivedTensor l _ Ω _ _ _
        W hW)).obj (N,P)),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (hS : (commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P).stage ≤ L) (hT :
          (commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)).stage ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P)
          (commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)) L hS hT
          (((@pullbackTensorCommonLeft l _ Ω _ _ _ W hW) M N P L hS).hom ≫
            ((@pullbackTensorRationalAssociator l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1.trans
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).1.trans hS))) (N.toStage
                (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).2.trans
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).1.trans hS))) (P.toStage
                (((Padic.finiteCoefficientFields_properties l Ω).1 (commonStageTensorObject l Ω W M
                N).stage P.stage).2.trans hS))).hom ≫
            ((@pullbackTensorCommonRight l _ Ω _ _ _ W hW) M N P L hT).inv)) := by
  sorry

/-- The stage-independent rational associator class.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorCommonAssociator (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  ((@pullbackTensorCommonAssociator_existsUnique l _ Ω _ _ _ W hW) M N P).exists.choose

/-- The common-stage braiding has its prescribed representative at every larger field.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Conjugate the rational braiding by the
  displayed transition/tensor comparisons. Their scalar-extension cocycles show independence of
  enlargement. The inverse formula gives an inverse class. Directedness supplies common stages, and
  a representative determines its colimit hom class uniquely. -/
theorem pullbackTensorCommonBraiding_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (M,N) ≅
      ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (N,M),
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (hS : (commonStageTensorObject l Ω W M N).stage ≤ L) (hT : (commonStageTensorObject l Ω W N
          M).stage ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W M N)
          (commonStageTensorObject l Ω W N M) L hS hT
          ((commonStageTensorComparison l Ω W M N L hS).hom ≫
            ((@pullbackTensorRationalBraiding l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage N.stage).1.trans
                hS)) (N.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage
                N.stage).2.trans hS))).hom ≫
            (commonStageTensorComparison l Ω W N M L hT).inv)) := by
  sorry

/-- The stage-independent rational braiding class.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorCommonBraiding (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N : generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  ((@pullbackTensorCommonBraiding_existsUnique l _ Ω _ _ _ W hW) M N).exists.choose

/-- The limit of the coherent ring unit is constructible and complete.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: The coherent ring unit is the constant
  rank-one finite coefficient tower. Its quotient transitions are normalized. Normalized DVR
  effectivity computes its limit as the completed rank-one coefficient module, whose reductions are
  the finite constructible ring units; these have uniform amplitude zero. -/
theorem pullbackTensorIntegralUnit_constructible (W : Scheme.{u})
    [_hW : ∀ w : W, Invertible (l : W.residueField w)] :
    sfIntegralConstructible l E W ((coefficientSequenceLimit l E W).obj
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit) := by
  sorry

/-- The actual derived limit of the coherent coefficient-ring unit.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorIntegralUnit (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] : sfIntegralConstructibleCategory l E W :=
  ⟨_, @pullbackTensorIntegralUnit_constructible l _ E _ _ _ W hW⟩

/-- The reduction counit of the normalized coefficient-ring unit is invertible.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: The finite ring units and their quotient
  tensor comparisons form a normalized system. Apply normalized DVR effectivity to this system. The
  reconstruction isomorphism is precisely the reduction/limit adjunction counit. -/
theorem pullbackTensorIntegralUnit_counit (W : Scheme.{u})
    [_hW : ∀ w : W, Invertible (l : W.residueField w)] : IsIso ((pullbackTensorCalculus l E
      W).adjunction.counit.app
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit) := by
  sorry

/-- The fixed identification of the reduced integral unit with the coherent ring unit.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorIntegralUnitReduction (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :
    (pullbackTensorCalculus l E W).reduction.obj ((@pullbackTensorIntegralUnit l _ E _ _ _ W
      hW)).obj ≅
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit :=
  letI := (@pullbackTensorIntegralUnit_counit l _ E _ _ _ W hW)
  asIso ((pullbackTensorCalculus l E W).adjunction.counit.app _)

/-- The rational unit is the localization of the completed coefficient-ring unit.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorRationalUnit (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :=
  (sfRationalConstructibleLocalization l E W).obj ((@pullbackTensorIntegralUnit l _ E _ _ _ W hW))

/-- The integral left unitor is fixed by coherent reduction.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Conjugate the coherent unitor by the actual
  tensor-reduction and unit-reduction isomorphisms. Reduction is fully faithful on the complete
  constructible subcategory by normalized effectivity, so this arrow and its inverse lift uniquely.
  Faithfulness gives the inverse identities. -/
theorem pullbackTensorIntegralLeftUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj ((@pullbackTensorIntegralUnit l _ E
      _ _ _ W hW),M) ≅ M,
      (pullbackTensorCalculus l E W).reduction.map e.hom.hom =
        ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) ((@pullbackTensorIntegralUnit l _
          E _ _ _ W hW)) M).hom ≫
          (pullbackTensorCalculus l E W).systemClosed.tensor.map
            (Prod.mkHom ((@pullbackTensorIntegralUnitReduction l _ E _ _ _ W hW)).hom (𝟙 _)) ≫
          ((pullbackTensorCalculus l E W).systemClosed.monoidal.leftUnitor
            ((pullbackTensorCalculus l E W).reduction.obj M.obj)).hom := by
  sorry

/-- The normalized completed left unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorIntegralLeftUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W) :=
  ((@pullbackTensorIntegralLeftUnitor_existsUnique l _ E _ _ _ W hW) M).exists.choose

/-- The rational left unitor is the localized completed one.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Use the prescribed rational tensor object
  equality and localize the integral unitor and its inverse. The displayed hom equality uniquely
  determines the iso. -/
theorem pullbackTensorRationalLeftUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj ((@pullbackTensorRationalUnit l _ E _ _ _
      W hW),M) ≅ M,
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ W hW) M.obj).hom) := by
  apply existsUnique_iso_of_eq
    ((rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1
      (pullbackTensorRationalUnit l E W,M)) rfl
    ((sfRationalConstructibleLocalization l E W).mapIso
      (pullbackTensorIntegralLeftUnitor l E W M.obj))

/-- The localized completed left unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorRationalLeftUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :=
  ((@pullbackTensorRationalLeftUnitor_existsUnique l _ E _ _ _ W hW) M).exists.choose

/-- The integral right unitor is fixed by coherent reduction.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Conjugate the coherent unitor by the actual
  tensor-reduction and unit-reduction isomorphisms. Reduction is fully faithful on the complete
  constructible subcategory by normalized effectivity, so this arrow and its inverse lift uniquely.
  Faithfulness gives the inverse identities. -/
theorem pullbackTensorIntegralRightUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W) :
    ∃! e : ((@constructibleIntegralTensor l _ E _ _ _ W hW)).obj (M,(@pullbackTensorIntegralUnit l _
      E _ _ _ W hW)) ≅ M,
      (pullbackTensorCalculus l E W).reduction.map e.hom.hom =
        ((@pullbackTensorIntegralReductionTensor l _ E _ _ _ W hW) M ((@pullbackTensorIntegralUnit l
          _ E _ _ _ W hW))).hom ≫
          (pullbackTensorCalculus l E W).systemClosed.tensor.map
            (Prod.mkHom (𝟙 _) ((@pullbackTensorIntegralUnitReduction l _ E _ _ _ W hW)).hom) ≫
          ((pullbackTensorCalculus l E W).systemClosed.monoidal.rightUnitor
            ((pullbackTensorCalculus l E W).reduction.obj M.obj)).hom := by
  sorry

/-- The normalized completed right unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorIntegralRightUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W) :=
  ((@pullbackTensorIntegralRightUnitor_existsUnique l _ E _ _ _ W hW) M).exists.choose

/-- The rational right unitor is the localized completed one.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Use the prescribed rational tensor object
  equality and localize the integral unitor and its inverse. The displayed hom equality uniquely
  determines the iso. -/
theorem pullbackTensorRationalRightUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (M,(@pullbackTensorRationalUnit l _ E _ _
      _ W hW)) ≅ M,
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ W hW) M.obj).hom) := by
  apply existsUnique_iso_of_eq
    ((rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1
      (M,pullbackTensorRationalUnit l E W)) rfl
    ((sfRationalConstructibleLocalization l E W).mapIso
      (pullbackTensorIntegralRightUnitor l E W M.obj))

/-- The localized completed right unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorRationalRightUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :=
  ((@pullbackTensorRationalRightUnitor_existsUnique l _ E _ _ _ W hW) M).exists.choose

/-- Scalar extension preserves the canonical rational coefficient-ring unit.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: For integral coefficients, scalar extension
  sends the coefficient-ring unit to the new coefficient ring by multiplication. Its unit equations
  hold on pure tensors, remain true in both Roos coordinates, and localize. The tensor comparison is
  invertible; cancellation in the unit square at the unit object proves uniqueness. -/
theorem pullbackTensorRationalScalarUnit_existsUnique
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :
    ∃! e : (sfRationalScalarExtension l E W 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj
          ((@pullbackTensorRationalUnit l _ E _ _ _ W hW)) ≅ (@pullbackTensorRationalUnit l _ L _ _
            _ W hW),
      ∀ M : sfRationalConstructibleCategory l E W,
        ((rationalTensorScalarComparison l E L ι W).hom.app ((@pullbackTensorRationalUnit l _ E _ _
          _ W hW),M) ≫
          ((@rationalDerivedTensor l _ L _ _ _ W hW)).map (Prod.mkHom e.hom (𝟙 _)) ≫
          ((@pullbackTensorRationalLeftUnitor l _ L _ _ _ W hW) ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)).hom =
          (sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map ((@pullbackTensorRationalLeftUnitor l
              _ E _ _ _ W hW) M).hom) ∧
        ((rationalTensorScalarComparison l E L ι W).hom.app (M,(@pullbackTensorRationalUnit l _ E _
          _ _ W hW)) ≫
          ((@rationalDerivedTensor l _ L _ _ _ W hW)).map (Prod.mkHom (𝟙 _) e.hom) ≫
          ((@pullbackTensorRationalRightUnitor l _ L _ _ _ W hW) ((sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).obj M)).hom =
          (sfRationalScalarExtension l E W 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L ι).map ((@pullbackTensorRationalRightUnitor l
              _ E _ _ _ W hW) M).hom) := by
  sorry

/-- The coefficient-ring scalar comparison fixed by the two tensor unit squares.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorRationalScalarUnit
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :=
  (@pullbackTensorRationalScalarUnit_existsUnique l _ E _ _ _ L _ _ _ ι W hW).exists.choose

/-- The common-stage unit represented over the least finite coefficient field.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorCommonUnit (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :
      generalAlgebraicallyClosedConstructibleCategory l
      Ω W :=
  ⟨Padic.finiteCoefficientBase l Ω,
    (@pullbackTensorRationalUnit l _
      (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        (Padic.finiteCoefficientBase l Ω)) _ _ _ W hW)⟩

/-- The common-stage ring unit is the rational ring unit at every larger stage.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorCommonUnitStage (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (L : AlgebraicallyClosedCoefficients.Index l Ω)
    (h : ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage ≤ L) :
    ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).toStage h ≅
      (@pullbackTensorRationalUnit l _
        (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W hW)
        :=
  (operationStageTransitionIso l Ω W _ L h).app _ ≪≫
    @pullbackTensorRationalScalarUnit l _
      (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω
        (Padic.finiteCoefficientBase l Ω)) _ _ _
      (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _
        (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.coefficientInclusion l Ω _ L h) W hW

/-- The common-stage left unitor has the canonical representative at every larger field.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Represent at the finite compositum. Apply
  the tensor-stage comparison, the coefficient-ring unit comparison, and the rational unitor. The
  scalar unit equations and scalar cocycles identify these arrows at all larger stages. Their
  inverses define an inverse class, and this representative condition determines the colimit hom
  uniquely. -/
theorem pullbackTensorCommonLeftUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj
        (((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)),M) ≅ M,
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (h : (commonStageTensorObject l Ω W ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)) M).stage
          ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W ((@pullbackTensorCommonUnit l _ Ω _ _ _ W
          hW)) M) M L h
          (((Padic.finiteCoefficientFields_properties l Ω).1 ((@pullbackTensorCommonUnit l _ Ω _ _ _
            W hW)).stage
          M.stage).2.trans h)
          ((commonStageTensorComparison l Ω W ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)) M L
            h).hom ≫
            ((@rationalDerivedTensor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)).map
              (Prod.mkHom ((@pullbackTensorCommonUnitStage l _ Ω _ _ _ W hW) L
                (((Padic.finiteCoefficientFields_properties l Ω).1 ((@pullbackTensorCommonUnit l _ Ω
                  _ _ _ W hW)).stage M.stage).1.trans h)).hom (𝟙 _)) ≫
            ((@pullbackTensorRationalLeftUnitor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
                ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage M.stage).2.trans h))).hom)) :=
                  by
  sorry

/-- The common-stage class of the canonical rational left unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorCommonLeftUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  ((@pullbackTensorCommonLeftUnitor_existsUnique l _ Ω _ _ _ W hW) M).exists.choose

/-- The common-stage right unitor has the canonical representative at every larger field.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Represent at the finite compositum. Apply
  the tensor-stage comparison, the coefficient-ring unit comparison, and the rational unitor. The
  scalar unit equations and scalar cocycles identify these arrows at all larger stages. Their
  inverses define an inverse class, and this representative condition determines the colimit hom
  uniquely. -/
theorem pullbackTensorCommonRightUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃! e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj
        (M,((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW))) ≅ M,
      ∀ (L : AlgebraicallyClosedCoefficients.Index l Ω)
        (h : (commonStageTensorObject l Ω W M ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW))).stage
          ≤ L),
        HEq e.hom (ofHom (commonStageTensorObject l Ω W M ((@pullbackTensorCommonUnit l _ Ω _ _ _ W
          hW))) M L h
          (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage ((@pullbackTensorCommonUnit l _
            Ω _ _ _ W hW)).stage).1.trans h)
          ((commonStageTensorComparison l Ω W M ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)) L
            h).hom ≫
            ((@rationalDerivedTensor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)).map
              (Prod.mkHom (𝟙 _) ((@pullbackTensorCommonUnitStage l _ Ω _ _ _ W hW) L
                (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage
                  ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage).2.trans h)).hom) ≫
            ((@pullbackTensorRationalRightUnitor l _
              (_root_.WeilConjectures.AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) _ _ _ W
              hW)
              (M.toStage (((Padic.finiteCoefficientFields_properties l Ω).1 M.stage
                ((@pullbackTensorCommonUnit l _ Ω _ _ _ W hW)).stage).1.trans h))).hom)) := by
  sorry

/-- The common-stage class of the canonical rational right unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def pullbackTensorCommonRightUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  ((@pullbackTensorCommonRightUnitor_existsUnique l _ Ω _ _ _ W hW) M).exists.choose

/-- Both unit equations for the actual canonical integral comparison.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalIntegralPullbackTensor_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∃! ε : ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj
    ((@pullbackTensorIntegralUnit l _ E _ _ _ Y hY)) ≅
      (@pullbackTensorIntegralUnit l _ E _ _ _ X hX),
    ∀ M : sfIntegralConstructibleCategory l E Y,
      (((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) ((@pullbackTensorIntegralUnit l _
        E _ _ _ Y hY)) M).hom ≫
        ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map (Prod.mkHom ε.hom (𝟙 _)) ≫
        ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ X hX) (((@constructibleIntegralPullback l _
          E _ _ _ X Y f hX hY)).obj M)).hom =
      ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
        ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ Y hY) M).hom) ∧
      (((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M ((@pullbackTensorIntegralUnit l
        _ E _ _ _ Y hY))).hom ≫
        ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map (Prod.mkHom (𝟙 _) ε.hom) ≫
        ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ X hX) (((@constructibleIntegralPullback l _
          E _ _ _ X Y f hX hY)).obj M)).hom
          =
      ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
        ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ Y hY) M).hom)

/-- Both unit equations for the actual canonical rational comparison.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalRationalPullbackTensor_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∃! ε : ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj ((@pullbackTensorRationalUnit l _
    E _ _ _ Y hY)) ≅
      (@pullbackTensorRationalUnit l _ E _ _ _ X hX),
    ∀ M : sfRationalConstructibleCategory l E Y,
      (((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) ((@pullbackTensorRationalUnit l _
        E _ _ _ Y hY)) M).hom ≫
        ((@rationalDerivedTensor l _ E _ _ _ X hX)).map (Prod.mkHom ε.hom (𝟙 _)) ≫
        ((@pullbackTensorRationalLeftUnitor l _ E _ _ _ X hX) (((@rationalDerivedPullback l _ E _ _
          _ X Y f hX hY)).obj M)).hom =
      ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).map ((@pullbackTensorRationalLeftUnitor l
        _ E _ _ _ Y hY) M).hom) ∧
      (((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M ((@pullbackTensorRationalUnit l
        _ E _ _ _ Y hY))).hom ≫
        ((@rationalDerivedTensor l _ E _ _ _ X hX)).map (Prod.mkHom (𝟙 _) ε.hom) ≫
        ((@pullbackTensorRationalRightUnitor l _ E _ _ _ X hX) (((@rationalDerivedPullback l _ E _ _
          _ X Y f hX hY)).obj M)).hom =
      ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).map ((@pullbackTensorRationalRightUnitor
        l _ E _ _ _ Y hY) M).hom)

/-- Both unit equations for the actual canonical commonstage comparison.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalCommonStagePullbackTensor_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∃! ε : ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj ((@pullbackTensorCommonUnit l _
    Ω _ _ _ Y hY)) ≅
      (@pullbackTensorCommonUnit l _ Ω _ _ _ X hX),
    ∀ M : generalAlgebraicallyClosedConstructibleCategory l Ω Y,
      (((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) ((@pullbackTensorCommonUnit l
        _ Ω _ _ _ Y hY)) M).hom ≫
        ((@commonStageDerivedTensor l _ Ω _ _ _ X hX)).map (Prod.mkHom ε.hom (𝟙 _)) ≫
        ((@pullbackTensorCommonLeftUnitor l _ Ω _ _ _ X hX) (((@commonStageDerivedPullback l _ Ω _ _
          _ X Y f hX hY)).obj M)).hom =
      ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).map ((@pullbackTensorCommonLeftUnitor
        l _ Ω _ _ _ Y hY) M).hom) ∧
      (((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M ((@pullbackTensorCommonUnit
        l _ Ω _ _ _ Y hY))).hom ≫
        ((@commonStageDerivedTensor l _ Ω _ _ _ X hX)).map (Prod.mkHom (𝟙 _) ε.hom) ≫
        ((@pullbackTensorCommonRightUnitor l _ Ω _ _ _ X hX) (((@commonStageDerivedPullback l _ Ω _
          _ _ X Y f hX hY)).obj M)).hom =
      ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).map ((@pullbackTensorCommonRightUnitor
        l _ Ω _ _ _ Y hY) M).hom)

/-- Coherence for the canonical integral comparison with the fixed associator.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalIntegralPullbackTensor_associative {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N P : sfIntegralConstructibleCategory l E Y),
    ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map
      ((@pullbackTensorIntegralAssociator l _ E _ _ _ Y hY) M N P).hom ≫
          ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M
            (((@constructibleIntegralTensor l _ E _ _ _ Y hY)).obj (N,P))).hom ≫
          ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map
            (Prod.mkHom (𝟙 _) ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) N P).hom)
              =
        ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY)
          (((@constructibleIntegralTensor l _ E _ _ _ Y hY)).obj (M,N)) P).hom ≫
          ((@constructibleIntegralTensor l _ E _ _ _ X hX)).map
            (Prod.mkHom ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom (𝟙 _))
              ≫
          ((@pullbackTensorIntegralAssociator l _ E _ _ _ X hX)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj N)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj P)).hom

/-- The normalized integral comparison obeys this coherence equation.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Apply coherent reduction to both routes.
  Insert the actual reduction square for the integral comparison and the defining normalized
  associator. The system comparison associativity equation makes the reduced routes equal. Full
  faithfulness on complete constructible objects gives the integral equation. Localization gives the
  rational equation; represent at a common finite field and use the prescribed transition
  comparisons for the algebraically closed equation. -/
theorem canonicalIntegralPullbackTensor_associative_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalIntegralPullbackTensor_associative l _ E _ _ _ X Y f hX hY) := by
  sorry

/-- Coherence for the canonical rational comparison with the fixed associator.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalRationalPullbackTensor_associative {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N P : sfRationalConstructibleCategory l E Y),
    ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).map ((@pullbackTensorRationalAssociator l _
      E _ _ _ Y hY) M N P).hom ≫
            ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M
              (((@rationalDerivedTensor l _ E _ _ _ Y hY)).obj (N,P))).hom ≫
            ((@rationalDerivedTensor l _ E _ _ _ X hX)).map
              (Prod.mkHom (𝟙 _) ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) N
                P).hom) =
          ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY)
            (((@rationalDerivedTensor l _ E _ _ _ Y hY)).obj (M,N)) P).hom ≫
            ((@rationalDerivedTensor l _ E _ _ _ X hX)).map
              (Prod.mkHom ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom (𝟙
                _)) ≫
            ((@pullbackTensorRationalAssociator l _ E _ _ _ X hX)
            (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj M)
            (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj N)
            (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj P)).hom

/-- The normalized rational comparison obeys this coherence equation.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Apply coherent reduction to both routes.
  Insert the actual reduction square for the integral comparison and the defining normalized
  associator. The system comparison associativity equation makes the reduced routes equal. Full
  faithfulness on complete constructible objects gives the integral equation. Localization gives the
  rational equation; represent at a common finite field and use the prescribed transition
  comparisons for the algebraically closed equation. -/
theorem canonicalRationalPullbackTensor_associative_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalRationalPullbackTensor_associative l _ E _ _ _ X Y f hX hY) := by
  sorry

/-- Coherence for the canonical commonstage comparison with the fixed associator.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalCommonStagePullbackTensor_associative {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω Y),
    ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).map ((@pullbackTensorCommonAssociator l
      _ Ω _ _ _ Y hY) M N P).hom ≫
            ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M
              (((@commonStageDerivedTensor l _ Ω _ _ _ Y hY)).obj (N,P))).hom ≫
            ((@commonStageDerivedTensor l _ Ω _ _ _ X hX)).map
              (Prod.mkHom (𝟙 _) ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) N
                P).hom) =
          ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY)
            (((@commonStageDerivedTensor l _ Ω _ _ _ Y hY)).obj (M,N)) P).hom ≫
            ((@commonStageDerivedTensor l _ Ω _ _ _ X hX)).map
              (Prod.mkHom ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M N).hom (𝟙
                _)) ≫
            ((@pullbackTensorCommonAssociator l _ Ω _ _ _ X hX)
            (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj M)
            (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj N)
            (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj P)).hom

/-- The normalized commonstage comparison obeys this coherence equation.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Apply coherent reduction to both routes.
  Insert the actual reduction square for the integral comparison and the defining normalized
  associator. The system comparison associativity equation makes the reduced routes equal. Full
  faithfulness on complete constructible objects gives the integral equation. Localization gives the
  rational equation; represent at a common finite field and use the prescribed transition
  comparisons for the algebraically closed equation. -/
theorem canonicalCommonStagePullbackTensor_associative_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalCommonStagePullbackTensor_associative l _ Ω _ _ _ X Y f hX hY) := by
  sorry

/-- Coherence for the canonical integral comparison with the fixed braiding.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalIntegralPullbackTensor_braiding {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N : sfIntegralConstructibleCategory l E Y),
    ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).map ((@pullbackTensorIntegralBraiding
      l _ E _ _ _ Y hY) M N).hom ≫
            ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) N M).hom =
          ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
            ((@pullbackTensorIntegralBraiding l _ E _ _ _ X hX)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)
            (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj N)).hom

/-- The normalized integral comparison obeys this coherence equation.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Apply coherent reduction to both routes.
  Insert the actual reduction square for the integral comparison and the defining normalized
  braiding. The system comparison signed symmetry equation makes the reduced routes equal. Full
  faithfulness on complete constructible objects gives the integral equation. Localization gives the
  rational equation; represent at a common finite field and use the prescribed transition
  comparisons for the algebraically closed equation. -/
theorem canonicalIntegralPullbackTensor_braiding_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalIntegralPullbackTensor_braiding l _ E _ _ _ X Y f hX hY) := by
  sorry

/-- Coherence for the canonical rational comparison with the fixed braiding.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalRationalPullbackTensor_braiding {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N : sfRationalConstructibleCategory l E Y),
    ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).map ((@pullbackTensorRationalBraiding l _ E
      _ _ _ Y hY) M N).hom ≫
            ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) N M).hom =
          ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
            ((@pullbackTensorRationalBraiding l _ E _ _ _ X hX)
            (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj M)
            (((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY)).obj N)).hom

/-- The normalized rational comparison obeys this coherence equation.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Apply coherent reduction to both routes.
  Insert the actual reduction square for the integral comparison and the defining normalized
  braiding. The system comparison signed symmetry equation makes the reduced routes equal. Full
  faithfulness on complete constructible objects gives the integral equation. Localization gives the
  rational equation; represent at a common finite field and use the prescribed transition
  comparisons for the algebraically closed equation. -/
theorem canonicalRationalPullbackTensor_braiding_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalRationalPullbackTensor_braiding l _ E _ _ _ X Y f hX hY) := by
  sorry

/-- Coherence for the canonical commonstage comparison with the fixed braiding.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). -/
def canonicalCommonStagePullbackTensor_braiding {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] : Prop :=
  ∀ (M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y),
    ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).map ((@pullbackTensorCommonBraiding l _
      Ω _ _ _ Y hY) M N).hom ≫
            ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) N M).hom =
          ((@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M N).hom ≫
            ((@pullbackTensorCommonBraiding l _ Ω _ _ _ X hX)
            (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj M)
            (((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY)).obj N)).hom

/-- The normalized commonstage comparison obeys this coherence equation.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-iso). Proof: Apply coherent reduction to both routes.
  Insert the actual reduction square for the integral comparison and the defining normalized
  braiding. The system comparison signed symmetry equation makes the reduced routes equal. Full
  faithfulness on complete constructible objects gives the integral equation. Localization gives the
  rational equation; represent at a common finite field and use the prescribed transition
  comparisons for the algebraically closed equation. -/
theorem canonicalCommonStagePullbackTensor_braiding_spec {X Y : Scheme.{u}}
    (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)] :
    (@canonicalCommonStagePullbackTensor_braiding l _ Ω _ _ _ X Y f hX hY) := by
  sorry

end HigherCoherence

/-- The canonical derived pullback/tensor comparison exists at every coefficient
level and is natural in both inputs.  At finite level this is the comparison for
the constant-coefficient morphism of ringed pro-etale topoi.  At integral level it
is the inverse-limit comparison on completed reductions; at rational level it is
its scalar localization; and at algebraically closed level it is the common-stage
comparison over a finite coefficient compositum.  The comparison is compatible
with the tensor unit, associativity, signed symmetry, coefficient reduction and
scalar extension, and with composition of pullbacks, as in the proof steps of
`lem-pur-derived-pullback-tensor-iso`.

Source: `literature/stacks-project/sites-cohomology.tex`, Lemma 21.18.4 (Tag 07A4,
label `lemma-pullback-tensor-product`), for the morphism of ringed topoi
(X_proet, (A_{E,n})_X) -> (Y_proet, (A_{E,n})_Y); the integral, rational and Qlbar
levels follow the level-by-level definitions of the operations in
def-weil-derived-pullback-tensor-hom.

Proof plan (the node's numbered steps):

1. At finite level choose compatible small representatives of the pro-etale sites as in [def-weil-
   proetale-inverse-image]. The inverse image and its constant-ring map make $f_n$ a morphism of
   ringed topoi. By [prop-weil-pbc-proetale-constant-exact], module pullback is exact and agrees
   with inverse image with the coefficient action transported through
   $f^{-1}(A_{E,n})_Y\cong(A_{E,n})_X$. Thus its derived functor is precisely the finite operation
   in [def-weil-derived-pullback-tensor-hom]. Apply [lem-weil-pbc-ringed-topoi-derived-tensor-
   pullback] with $R=(A_{E,n})_Y$ and $S=(A_{E,n})_X$. Its displayed isomorphism, natural in both
   arguments, is $\mu_{f;M,N}$. That theorem is unbounded, so it applies to all the finite-level
   inputs claimed here; no finite Tor dimension of $A_{E,n}$ is assumed.

2. Choose flat-term K-flat resolutions $P,Q$ by [lem-pc-kflat-resolution]. The closure assertion
   [lem-pur-kflat-total-tensor-model] shows that $\operatorname{Tot}(P\otimes Q)$ is K-flat with
   flat terms, so all iterated tensors below compute derived tensors. On these models the
   comparison is totalized from the module map of [lem-weil-pbc-ringed-topoi-module-pullback-
   tensor], with the signed differential from [def-pc-tensor-complex-sheaves].

3. Use the chain maps of [lem-pur-cochain-pullback-tensor-coherence]. Their pure-tensor formula
   and inverse are the ordinary comparison of [lem-weil-pbc-ringed-topoi-module-pullback-tensor],
   and the chain lemma supplies associativity, signed symmetry, units, composition and
   coefficient-change equations. By [lem-weil-pbc-site-derived-tensor-descent] these maps and
   equations descend from the K-flat resolving class to arbitrary finite-level derived inputs.

4. For integral $M,N$, choose flat-term K-flat representatives $P,Q$ by [lem-pc-kflat-resolution].
   Set $P_n=P\otimes_{R_Y}B_{Y,n}$ and $Q_n=Q\otimes_{R_Y}B_{Y,n}$, with actual quotient
   transitions. Put $T_n=\operatorname{Tot}(P_n\otimes Q_n)$, $U_n=f_n^*P_n$, $V_n=f_n^*Q_n$, and
   $W_n=\operatorname{Tot}(U_n\otimes V_n)$. The quotient and pullback models are flat-term K-flat
   by [lem-pur-kflat-change-of-rings, lem-weil-pbc-ringed-pullback-preserves-kflat], and the
   tensor totals by step 2. The normalization and coherent reduction assertions of [lem-pur-
   completed-operation-tower-substitution] and [lem-coef-normalized-dvr-effectivity] identify
   these systems with the reductions of the completed operations in [def-pur-integral-derived-
   operations]. Here $B_{Y,n}=(A_{E,n})_Y$ and $R_Y=\varprojlim B_{Y,n}$, as in the normalized
   tower convention [def-coef-normalized-dvr-tower].

5. The cochain maps of [lem-pur-cochain-pullback-tensor-coherence] give the strict tower
   isomorphism $f_n^*T_n\to W_n$ and its strict inverse. Apply [lem-pur-integral-tower-limit-
   comparison] to the $T,U,V$ of step 4. With the substitution identifications of [lem-pur-
   completed-operation-tower-substitution], its actual derived-limit map is the required
   comparison between completed pullback of $M\widehat\otimes^L N$ and completed tensor of
   $Lf^*M,Lf^*N$. The functor is [lem-weil-pbc-ringed-strict-tower-homotopy-limit]; its naturality
   and the resolution comparisons of [lem-pur-integral-operations-well-defined] give naturality in
   $M,N$ and independence of the chosen representatives.

6. By [lem-pur-integral-operations-preserve-constructible], $M\widehat\otimes^L N$ is
   constructible on $Y$ and its pullback is constructible on $X$. The same lemma first puts
   $Lf^*M,Lf^*N$ in $D^b_c(X,\mathcal O_E)$ and then puts their completed tensor there. This is a
   full subcategory of the ambient derived category [def-weil-derived-complete-integral-detailed],
   so the ambient comparison and its inverse are morphisms of that subcategory.

7. The finite associativity, signed symmetry, unit and pullback-composition equations from [lem-
   pur-cochain-pullback-tensor-coherence] are compatible with every quotient transition. The
   tower-level assertion [lem-pur-integral-coherence-tower] therefore identifies them as
   equalities of strict normalized systems and gives their integral images after applying [lem-
   pur-completed-operation-tower-substitution] and [lem-weil-pbc-ringed-strict-tower-homotopy-
   limit].

8. The coherent counit comparisons of [lem-coef-normalized-dvr-effectivity], applied to the source
   and target systems of the strict comparison, identify its reduction with the finite comparison.
   Their naturality applies to this actual map of systems, and [lem-pur-completed-operation-tower-
   substitution] carries the counits to the completed operations. No faithfulness assertion for
   individual finite-reduction functors is needed.

9. For $E\subset L$ put $B_m=\mathcal O_L/\varpi_L^m$. The strict quotient models of [def-weil-
   integral-scalar-extension] and the coherent reduction model [lem-pur-coefficient-extension-
   reduction-model] give the normalized $B_\bullet$-tower, including ramified extensions. The
   quotient K-flatness is [lem-pur-kflat-change-of-rings], and the scalar-association and
   transition equations are exactly [lem-pur-scalar-extension-tower-coherence].

10. Use the pullback and tensor scalar-extension isomorphisms of [lem-pur-integral-operations-
   scalar-extension] in their canonical quotient-model form. The tower coherence statement [lem-
   pur-scalar-extension-tower-coherence] says that both routes around the comparison square send
   $b\otimes(x\otimes y)$ to $(b\otimes x)\otimes(1\otimes y)$ and commute with every quotient and
   coefficient square. Applying [lem-weil-pbc-ringed-strict-tower-homotopy-limit] and [lem-pur-
   completed-operation-tower-substitution] gives the integral scalar-extension square.

11. By [def-weil-rationalization-karoubi], every rational object is an integral object and every
   morphism is a finite sum of $u\otimes a$, with $u$ integral and $a\in E$. Define $\mu^E$ to be
   the image $\mu^{\mathcal O_E}\otimes1$; its inverse is the image of the integral inverse. The
   operations on rational morphisms are the scalar extensions specified in [def-weil-derived-
   pullback-tensor-hom]. The integral naturality identity for $u,v$, multiplied by the
   corresponding scalars, gives rational naturality; add the resulting identities for sums. Every
   integral coherence equation remains an equality after tensoring Hom groups with $E$, so the
   rational associativity, symmetry, unit and composition equations follow. The scalar-extension
   square of the preceding scalar-extension steps likewise remains commutative, since the rational
   scalar-extension functor is the one induced from the integral scalar-extension functor.

12. For objects $(E,M),(E',N)$ at the algebraically closed level, choose a common finite
   coefficient field $L$ and form the rational comparison there, conjugated by the scalar-
   extension comparisons as prescribed in [def-weil-derived-pullback-tensor-hom]. Represent the
   inverse by the inverse rational comparison with the inverse conjugating comparisons. In [def-
   weil-algebraically-closed-coefficients], morphisms are classes over common finite fields, and
   two representatives agree if they agree after passage to a further common field. The scalar-
   extension calculation after rationalization says precisely that passing from $L$ to any larger
   field sends this comparison to the same comparison there; hence the class and its inverse are
   independent of $L$. Represent any finite naturality or coherence diagram over a single common
   finite field; the rational identity proved in the preceding rationalization step gives its
   equality in the colimit Hom group. This proves all the asserted compatibilities at $\Qlb$,
   including scalar extension into $\Qlb$.
(blueprint: lem-pur-derived-pullback-tensor-iso) -/
theorem derivedPullbackTensorIso
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E]
      [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (n : ℕ)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
      [IsAlgClosure (Padic l) Ω] :
    ((∃ eF : (finiteIntrinsicDerivedTensor l E Y n) ⋙ (finiteDerivedPullback l E n f) ≅
        ((finiteDerivedPullback l E n f).prod (finiteDerivedPullback l E n f)) ⋙
          (finiteIntrinsicDerivedTensor l E X n),
        ∀ (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (n + 1))),
          eF.app (M,N) = (@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY) M N) ∧
      (@canonicalFinitePullbackTensor_associativity_condition l _ E _ _ _ X Y f n hX hY) ∧
      (@canonicalFinitePullbackTensor_unit_condition l _ E _ _ _ X Y f n hX hY) ∧
      (∀ {Z : Scheme.{u}} (h : Z ⟶ X)
        [hZ : ∀ z : Z, Invertible (l : Z.residueField z)],
        (@canonicalFinitePullbackTensor_composition_condition l _ E _ _ _ X Y Z f h n hX hY hZ)) ∧
      (@canonicalFinitePullbackTensor_braiding_condition l _ E _ _ _ X Y f n hX hY) ∧
      (∃ eI : (@constructibleIntegralTensor l _ E _ _ _ Y hY) ⋙ (@constructibleIntegralPullback l _
        E _ _ _ X Y f hX hY) ≅
        ((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY).prod
          (@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)) ⋙ (@constructibleIntegralTensor
          l _ E _ _ _ X hX),
        ∀ (M N : sfIntegralConstructibleCategory l E Y),
          eI.app (M,N) = (@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N) ∧
      (∃ eR : (@rationalDerivedTensor l _ E _ _ _ Y hY) ⋙ (@rationalDerivedPullback l _ E _ _ _ X Y
        f hX hY) ≅
        ((@rationalDerivedPullback l _ E _ _ _ X Y f hX hY).prod (@rationalDerivedPullback l _ E _ _
          _ X Y f hX hY)) ⋙ (@rationalDerivedTensor l _ E _ _ _ X hX),
        ∀ (M N : sfRationalConstructibleCategory l E Y),
          eR.app (M,N) = (@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M N) ∧
      (∃ eC : (@commonStageDerivedTensor l _ Ω _ _ _ Y hY) ⋙ (@commonStageDerivedPullback l _ Ω _ _
        _ X Y f hX hY) ≅
        ((@commonStageDerivedPullback l _ Ω _ _ _ X Y f hX hY).prod (@commonStageDerivedPullback l _
          Ω _ _ _ X Y f hX hY)) ⋙ (@commonStageDerivedTensor l _ Ω _ _ _ X hX),
        ∀ (M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y),
          eC.app (M,N) = (@canonicalCommonStagePullbackTensor l _ Ω _ _ _ X Y f hX hY) M N) ∧
      (∀ M N : sfRationalConstructibleCategory l E Y,
        HEq ((@canonicalRationalPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom
          ((sfRationalConstructibleLocalization l E X).map
            ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M.obj N.obj).hom)) ∧
      (∀ {Z : Scheme.{u}} (h : Z ⟶ X)
        [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
        (M N : sfIntegralConstructibleCategory l E Y),
        (@canonicalIntegralPullbackTensor_composition l _ E _ _ _ X Y Z f h hX hY hZ) M N) ∧
      (∀ {Z : Scheme.{u}} (h : Z ⟶ X)
        [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
        (M N : sfRationalConstructibleCategory l E Y),
        (@canonicalRationalPullbackTensor_composition l _ E _ _ _ X Y Z f h hX hY hZ) M N) ∧
      (∀ {Z : Scheme.{u}} (h : Z ⟶ X)
        [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
        (M N : generalAlgebraicallyClosedConstructibleCategory l Ω Y),
        (@canonicalCommonStagePullbackTensor_composition l _ Ω _ _ _ X Y Z f h hX hY hZ) M N) ∧
      (∀ M N, (@canonicalIntegralPullbackTensor_reduction l _ E _ _ _ X Y f hX hY) M N) ∧
      (@canonicalIntegralPullbackTensor_associative l _ E _ _ _ X Y f hX hY) ∧
      (@canonicalRationalPullbackTensor_associative l _ E _ _ _ X Y f hX hY) ∧
      (@canonicalCommonStagePullbackTensor_associative l _ Ω _ _ _ X Y f hX hY) ∧
      (@canonicalIntegralPullbackTensor_braiding l _ E _ _ _ X Y f hX hY) ∧
      (@canonicalRationalPullbackTensor_braiding l _ E _ _ _ X Y f hX hY) ∧
      (@canonicalCommonStagePullbackTensor_braiding l _ Ω _ _ _ X Y f hX hY) ∧
      (@canonicalIntegralPullbackTensor_unit l _ E _ _ _ X Y f hX hY) ∧
      (@canonicalRationalPullbackTensor_unit l _ E _ _ _ X Y f hX hY) ∧
      (@canonicalCommonStagePullbackTensor_unit l _ Ω _ _ _ X Y f hX hY) ∧
      (∀ {m q : ℕ} (hq : q ≤ m)
        (M N : proEtaleDerivedCategory Y (finiteCoefficientRing l E (m + 1))),
        (canonicalFinitePullbackTensor_quotient_condition l E f (hX := hX) (hY := hY)
          (m := m) (n := q) hq M N)) ∧
      (∀ (L : Type u) [Field L] [Algebra (Padic l) L]
        [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L)
        (M N : sfIntegralConstructibleCategory l E Y),
        (canonicalIntegralPullbackTensor_scalar_condition l E L ι f
          (hX := hX) (hY := hY) M N)) ∧
      (∀ (L : Type u) [Field L] [Algebra (Padic l) L]
        [FiniteDimensional (Padic l) L] (ι : E →ₐ[Padic l] L)
        (M N : sfRationalConstructibleCategory l E Y),
        (canonicalRationalPullbackTensor_scalar_condition l E L ι f
          (hX := hX) (hY := hY) M N)) ∧
      (∀ (n : ℕ) (M N : coefficientSequenceDerived l E Y),
        (coefficientSequenceDerivedEvaluation l E X n).map
          ((pullbackTensorSystemComparison l E f).hom.app (M,N)) ≫
          ((pullbackTensorCalculus l E X).evaluationTensor n).hom.app
            ((pullbackTensorSequenceDerived l E f).obj M,
              (pullbackTensorSequenceDerived l E f).obj N) ≫
          (finiteIntrinsicDerivedTensor l E X n).map
            (Prod.mkHom ((pullbackTensorDerivedEvaluation l E f n).hom.app M)
              ((pullbackTensorDerivedEvaluation l E f n).hom.app N)) =
        (pullbackTensorDerivedEvaluation l E f n).hom.app
          ((pullbackTensorCalculus l E Y).systemClosed.tensor.obj (M,N)) ≫
          (finiteDerivedPullback l E n f).map
            (((pullbackTensorCalculus l E Y).evaluationTensor n).hom.app (M,N)) ≫
          ((@canonicalFinitePullbackTensor l _ E _ _ _ X Y f n hX hY)
            ((coefficientSequenceDerivedEvaluation l E Y n).obj M)
            ((coefficientSequenceDerivedEvaluation l E Y n).obj N)).hom)) := by
  sorry

end WeilConjectures
