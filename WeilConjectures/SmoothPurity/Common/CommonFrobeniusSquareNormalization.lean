/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.WeilIndSheafCategory
public import WeilConjectures.PoincareDuality.SemilinearFieldOperationLifts
import WeilConjectures.SmoothPurity.Common.CommonStageCompositorIntegralNormalization
import all Mathlib.Logic.Small.Defs

/-! # Agreement of the two normalized common-stage Frobenius squares

Source: purity/trace equivariance proof Step 1, canonical pullback compositors.
(blueprint: lem-pur-common-frobenius-square-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u v
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped TensorProduct
namespace WeilConjectures

-- Use the same cached category structures as the coefficient comparison APIs.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct
  GeneralAlgebraicallyClosedCoefficients.stageSystem
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] Functor.category StageSystem.instCategoryPairCategory
  ScalarLocalization.category ObjectProperty.FullSubcategory.category
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.transition
  StageSystem.ι sfRationalConstructibleLocalization ScalarLocalization.localization
  commonStagePullbackObject

attribute [local irreducible] HasDerivedCategory.standard integralCoefficientLinear
attribute [local irreducible] commonStageDerivedPullback rationalDerivedPullback
  constructibleIntegralPullback Scheme.residueField
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence
  sfRationalScalarExtension rationalPullbackScalarComparison sfRationalScalarComp

private theorem remove_transports {C : Type*} [Category* C]
    {A A' B B' M : C} (f : A ⟶ B) (g : A' ⟶ B')
    (p : A = A') (q : B = M) (r : M = B')
    (h : f ≫ eqToHom q ≫ eqToHom r = eqToHom p ≫ g) : HEq f g := by
  cases p
  cases q
  cases r
  simpa using h

private theorem zl_composition_integral (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Z) :
    HEq ((zlPullComp l Ω f g).hom.app P)
      ((GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) P.stage).map
        ((sfRationalConstructibleLocalization l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) X).map
          ((zlIntegralPullComp l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f g).hom.app
              P.obj.obj))) := by
  have hn := (zlPullComp_existsUnique l Ω f g).exists.choose_spec P.stage P.obj.obj
  change (zlPullComp l Ω f g).hom.app P ≫ _ = _ at hn
  apply remove_transports ((zlPullComp l Ω f g).hom.app P)
    ((GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) P.stage).map
      ((sfRationalConstructibleLocalization l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) X).map
        ((zlIntegralPullComp l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f g).hom.app P.obj.obj)))
    (zlStagePull_eq l Ω (f ≫ g) P.stage P.obj.obj)
    (congrArg (commonStageDerivedPullback l Ω f).obj
      (zlStagePull_eq l Ω g P.stage P.obj.obj))
    (zlStagePull_eq l Ω f P.stage
      ((constructibleIntegralPullback l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) g).obj P.obj.obj))
  simpa only [zlStagePullIso, eqToIso.hom, eqToHom_map, Category.assoc,
    Functor.comp_obj, StageSystem.instCategoryPairCategory] using hn

private theorem normalization_map_heq
    {C B : Type*} [Category* C] [Category* B] (F : C ⥤ B)
    {X Y X' Y' : C} (hx : X = X') (hy : Y = Y')
    {f : X ⟶ Y} {g : X' ⟶ Y'} (h : HEq f g) : HEq (F.map f) (F.map g) := by
  cases hx
  cases hy
  cases h
  rfl

private theorem common_composition_integral (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Z) :
    HEq (pullbackTensorCommonComposition l Ω g f P).hom
      ((GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) P.stage).map
        ((sfRationalConstructibleLocalization l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) X).map
          ((zlIntegralPullComp l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage) f g).hom.app
              P.obj.obj))) := by
  let E := AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω P.stage
  have hc := commonStageCompositor_integral l Ω f g P
  have hobj {V W : Scheme.{u}} (h : V ⟶ W)
      [∀ v : V, Invertible (l : V.residueField v)]
      [∀ w : W, Invertible (l : W.residueField w)] (K) :
      (rationalDerivedPullback l E h).obj K =
        (sfRationalConstructibleLocalization l E V).obj
          ((constructibleIntegralPullback l E h).obj K.obj) :=
    by simpa only [rationalDerivedPullback] using
      (rationalDerivedPullback_existsUnique l E h).exists.choose_spec.2.1 K
  have hb : (rationalDerivedPullback l E f).obj
      ((rationalDerivedPullback l E g).obj P.obj) =
      (sfRationalConstructibleLocalization l E X).obj
        ((constructibleIntegralPullback l E f).obj
          ((constructibleIntegralPullback l E g).obj P.obj.obj)) := by
    exact (hobj f ((rationalDerivedPullback l E g).obj P.obj)).trans
      (congrArg (fun K ↦ (sfRationalConstructibleLocalization l E X).obj
        ((constructibleIntegralPullback l E f).obj K.obj)) (hobj g P.obj))
  exact hc.trans ((normalization_map_heq
      (GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) P.stage)
      (hobj (f ≫ g) P.obj) hb
      (pullbackTensorRationalComposition_existsUnique l E g f P.obj).exists.choose_spec))
private theorem compositors_eq (l : ℕ) [Fact l.Prime]
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X Y Z : Scheme.{u}}
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    [∀ z : Z, Invertible (l : Z.residueField z)] (f : X ⟶ Y) (g : Y ⟶ Z)
    (P : generalAlgebraicallyClosedConstructibleCategory l Ω Z) :
    (zlPullComp l Ω f g).app P = pullbackTensorCommonComposition l Ω g f P := by
  apply Iso.ext
  exact eq_of_heq ((zl_composition_integral l Ω f g P).trans
    (common_composition_integral l Ω f g P).symm)

private theorem square_app
    {C B : Type*} [Category* C] [Category* B]
    {I : Sort*} (F : I → C ⥤ B) {x y : I} (w : x = y)
    {A D : C ⥤ B} (c₁ : F x ≅ A) (c₂ : F y ≅ D) (K : C) :
    ((c₁.symm ≪≫ eqToIso (congrArg F w) ≪≫ c₂).app K) =
      (c₁.app K).symm ≪≫
        eqToIso (congrArg (fun m ↦ (F m).obj K) w) ≪≫ c₂.app K := by
  cases w
  rfl

set_option allowUnsafeReducibility true in
attribute [local reducible] Aut FiniteFieldDatum.geometricFiber zlPull
  sfCommonStageWeilFrobeniusPullback

/-- The Weil pullback square uses the same normalized composition components as
pullback/tensor coherence.
Source: purity/trace equivariance proof Step 1 and the pullback composition conventions.
(blueprint: lem-pur-common-frobenius-square-normalization).
Proof: specialize the rational pullback/scalar tower equation to identity field
extensions. Naturality and cancellation give its coefficient-unit equation.
The rational compositor is natural by tensor induction from the integral one.
At the literal coefficient stage of K, the common-stage compositor formula has
three boundary comparisons. Their coefficient-unit equations and rational
naturality identify its representative with the stage transition of the rational
compositor. Its class is therefore the inclusion of that rational compositor,
which is the localization of integralPullbackComposition. The normalization of
zlPullComp identifies its component with exactly the same map, including the
object-equality transports. Rewrite both compositors of the Frobenius square.
The middle equality transports agree by eqToHom_app and proof irrelevance.
No smoothness, Tate line or purity map is involved. -/
theorem commonFrobeniusSquare_eq
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω]
    {X₀ Y₀ : Over (Spec (.of D.k₀))}
    [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀)
    (K : generalAlgebraicallyClosedConstructibleCategory l Ω (D.geometricFiber Y₀).left) :
    letI := fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
    letI := fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
    (zlFrobeniusSquare D l hl Ω f₀).app K =
      podCommonSquarePullbackComponent l Ω (zlFiberMap D f₀)
        (D.geometricFrobenius X₀).hom (D.geometricFrobenius Y₀).hom
        (zlFrobenius_naturality D f₀) K := by
  let : ∀ x : (D.geometricFiber X₀).left,
      Invertible (l : (D.geometricFiber X₀).left.residueField x) :=
    fun x ↦ sfWeilPrimeInvertible D l hl X₀ x
  let : ∀ y : (D.geometricFiber Y₀).left,
      Invertible (l : (D.geometricFiber Y₀).left.residueField y) :=
    fun y ↦ sfWeilPrimeInvertible D l hl Y₀ y
  unfold zlFrobeniusSquare
  rw [square_app (fun f ↦ commonStageDerivedPullback l Ω f)
    (zlFrobenius_naturality D f₀)
    (zlPullComp l Ω (D.geometricFrobenius X₀).hom (zlFiberMap D f₀))
    (zlPullComp l Ω (zlFiberMap D f₀) (D.geometricFrobenius Y₀).hom) K]
  rw [compositors_eq l Ω (D.geometricFrobenius X₀).hom (zlFiberMap D f₀) K,
    compositors_eq l Ω (zlFiberMap D f₀) (D.geometricFrobenius Y₀).hom K]
  rfl

end WeilConjectures
