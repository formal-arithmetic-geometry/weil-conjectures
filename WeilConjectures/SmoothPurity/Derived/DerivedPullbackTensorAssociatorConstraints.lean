/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints
import all WeilConjectures.PoincareDuality.Derived.DerivedPullbackTensorFiniteConstraints

import all WeilConjectures.SmoothPurity.Pullback.PullbackTensorReductionCalculus
import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
import WeilConjectures.SmoothPurity.CompletedOperations.NormalizedCompletedOperationModels
import all WeilConjectures.SmoothPurity.Rational.RationalTensorStageCoherence
import all WeilConjectures.CategoryTheory.BilinearCoefficientDescent.BilinearCoefficientDescent
import all Mathlib.Logic.Small.Defs
import WeilConjectures.CategoryTheory.BilinearCoefficientDescent.StageTensorAssociator
import WeilConjectures.SmoothPurity.Rational.RationalAssociatorScalarExtensionSquare

/-! # Common-stage normalized tensor associator

The common-stage associator and braiding constraints, using the finite
normalized constraints and the directed-stage representative calculation.
(blueprint: lem-pur-derived-pullback-tensor-constraints).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.privateModule false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u v r

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
open WeilConjectures
open WeilConjectures.GeneralAlgebraicallyClosedCoefficients

namespace WeilConjectures

-- Preserve the cached additive-group data while comparing stage Hom types.
set_option allowUnsafeReducibility true in
attribute [local irreducible] Preadditive.fullSubcategory
  StageSystem.PairCategory.categoryStruct

-- Match the category-wrapper proof context used by DerivedPullbackTensorHom.
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory

-- Residue fields only occur in hypotheses; avoid unfolding them during instance search.
attribute [local irreducible] Scheme.residueField Padic ScalarLocalization.composition
  integralCoefficientLinear integralScalarConstant sfIntegralCoefficientLinear
  sfIntegralConstructibleLinear
  HasDerivedCategory.standard CategoryTheory.Functor.leftAdjoint
  CategoryTheory.Functor.mapDerivedCategory
  completedIntegralCoefficientSheafUnrestricted scalarReductionExistence
  scalarReductionDerivedExistence
  commonStageTensorComparison commonStagePullbackComparison
  operationStageTransitionIso commonStageDerivedTensor commonStageDerivedPullback

section HigherCoherence
variable (l : ℕ) [Fact l.Prime]
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]

/-- The left nested tensor expressed at an arbitrary common finite stage.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
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
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
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

attribute [local irreducible] pullbackTensorCommonLeft pullbackTensorCommonRight

/-- Conjugating a scalar-compatible associator square by an isomorphism `e : F ≅ G` of
transition functors gives the square for the `e`-whiskered comparison. -/
private theorem associator_square_of_iso
    {C D : Type*} [Category* C] [Category* D]
    (U : C × C ⥤ C) (V : D × D ⥤ D) (F G : C ⥤ D) (e : F ≅ G)
    (c : U ⋙ G ≅ G.prod G ⋙ V)
    (α : ∀ A B P, U.obj (U.obj (A, B), P) ≅ U.obj (A, U.obj (B, P)))
    (γ : ∀ A B P, V.obj (V.obj (A, B), P) ≅ V.obj (A, V.obj (B, P)))
    (hn : ∀ {A A' B B' P P'} (f : A ⟶ A') (g : B ⟶ B') (h : P ⟶ P'),
      V.map (Prod.mkHom (V.map (Prod.mkHom f g)) h) ≫ (γ A' B' P').hom =
        (γ A B P).hom ≫ V.map (Prod.mkHom f (V.map (Prod.mkHom g h))))
    (hc : ∀ A B P, G.map (α A B P).hom ≫ c.hom.app (A, U.obj (B, P)) ≫
        V.map (Prod.mkHom (𝟙 _) (c.hom.app (B, P))) =
      c.hom.app (U.obj (A, B), P) ≫ V.map (Prod.mkHom (c.hom.app (A, B)) (𝟙 _)) ≫
        (γ (G.obj A) (G.obj B) (G.obj P)).hom)
    (A B P : C) :
    F.map (α A B P).hom ≫
        (Functor.isoWhiskerLeft U e ≪≫ c ≪≫
          Functor.isoWhiskerRight (NatIso.prod e.symm e.symm) V).hom.app (A, U.obj (B, P)) ≫
        V.map (Prod.mkHom (𝟙 _) ((Functor.isoWhiskerLeft U e ≪≫ c ≪≫
          Functor.isoWhiskerRight (NatIso.prod e.symm e.symm) V).hom.app (B, P))) =
      (Functor.isoWhiskerLeft U e ≪≫ c ≪≫
          Functor.isoWhiskerRight (NatIso.prod e.symm e.symm) V).hom.app (U.obj (A, B), P) ≫
        V.map (Prod.mkHom ((Functor.isoWhiskerLeft U e ≪≫ c ≪≫
          Functor.isoWhiskerRight (NatIso.prod e.symm e.symm) V).hom.app (A, B)) (𝟙 _)) ≫
        (γ (F.obj A) (F.obj B) (F.obj P)).hom := by
  dsimp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    NatIso.prod_hom, NatTrans.prod, Iso.symm_hom]
  have k₁ : V.map (Prod.mkHom (e.inv.app A)
      (c.hom.app (B, P) ≫ V.map (Prod.mkHom (e.inv.app B) (e.inv.app P)))) =
      V.map (Prod.mkHom (𝟙 _) (c.hom.app (B, P))) ≫
        V.map (Prod.mkHom (e.inv.app A) (V.map (Prod.mkHom (e.inv.app B) (e.inv.app P)))) := by
    rw [← V.map_comp]
    simp [Prod.mkHom]
  have k₂ : V.map (Prod.mkHom (c.hom.app (A, B) ≫ V.map (Prod.mkHom (e.inv.app A) (e.inv.app B)))
      (e.inv.app P)) =
      V.map (Prod.mkHom (c.hom.app (A, B)) (𝟙 _)) ≫
        V.map (Prod.mkHom (V.map (Prod.mkHom (e.inv.app A) (e.inv.app B))) (e.inv.app P)) := by
    rw [← V.map_comp]
    simp [Prod.mkHom]
  have h₁ := hn (e.inv.app A) (e.inv.app B) (e.inv.app P)
  have h₂ := hc A B P
  simp only [Prod.mkHom] at h₁ h₂ k₁ k₂
  simp only [Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc, Prod.mkHom, prod_comp,
    Category.comp_id, Iso.inv_hom_id_app_assoc]
  rw [k₁, k₂, Category.assoc, h₁, reassoc_of% (e.hom.naturality (α A B P).hom), ← reassoc_of% h₂]

section CommonAssociatorDescent
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageSystem
  GeneralAlgebraicallyClosedCoefficients.pairCategory CategoryTheory.uniformProd
attribute [local semireducible] operationStageTransitionIso
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] stageCategory._aux_1 stageCategory._aux_3 stageCategory._aux_5
attribute [local irreducible] rationalDerivedTensor sfRationalScalarExtension
  rationalTensorScalarComparison ObjectProperty.FullSubcategory.category ScalarLocalization.category
  pullbackTensorRationalAssociator

/-- Existence half of the normalized constraint; uniqueness is proved by the parent theorem.
Source: Stacks 06YS, 07A4, 0941.
(blueprint: lem-pur-derived-pullback-tensor-constraints-common-associator-existence). -/
theorem pullbackTensorCommonAssociator_exists (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W) :
    ∃ e : ((@commonStageDerivedTensor l _ Ω _ _ _ W hW)).obj (((@commonStageDerivedTensor l _ Ω _ _
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
  set_option backward.isDefEq.respectTransparency true in
  set_option backward.isDefEq.respectTransparency.types true in
    let S := stageSystem l Ω W
    let U : BilinearCoefficientDescent.Family S S S :=
      ⟨fun F ↦ rationalDerivedTensor l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) W,
        fun {_ _} h ↦ rationalTensorStageComparison l Ω W h,
        rationalTensorStageComparison_coherent l Ω W⟩
    let join := Padic.finiteCoefficientCompositum l Ω
    let left := fun F L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 F L).1
    let right := fun F L ↦ ((Padic.finiteCoefficientFields_properties l Ω).1 F L).2
    have hendpoint (A B : generalAlgebraicallyClosedConstructibleCategory l Ω W)
        (L : AlgebraicallyClosedCoefficients.Index l Ω) (h : join A.stage B.stage ≤ L) :
        BilinearCoefficientDescent.endpoint U join left right (A, B) h =
          commonStageTensorComparison l Ω W A B L h := by
      unfold BilinearCoefficientDescent.endpoint
      change ((rationalTensorStageComparison l Ω W h).app
        (A.toStage (left A.stage B.stage), B.toStage (right A.stage B.stage)) ≪≫
        (rationalDerivedTensor l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) W).mapIso
          (Iso.prod ((S.assoc (left A.stage B.stage) h).app A.obj)
            ((S.assoc (right A.stage B.stage) h).app B.obj))) = _
      delta rationalTensorStageComparison commonStageTensorComparison operationStageTransitionIso
      exact tensorStageComparison_endpoint _ _ _ _ _ _ _ _
    let α := fun F ↦ pullbackTensorRationalAssociator l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) W
    have hn : ∀ F {A A' B B' C C'} (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C'),
        (U.U F).map (Prod.mkHom ((U.U F).map (Prod.mkHom a b)) c) ≫ (α F A' B' C').hom =
          (α F A B C).hom ≫ (U.U F).map (Prod.mkHom a ((U.U F).map (Prod.mkHom b c))) := by
      intro F A A' B B' C C' a b c
      exact rationalAssociator_natural l
        (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) W a b c
    have hc : ∀ {F L} (h : F ≤ L) A B C,
        (S.T h).map (α F A B C).hom ≫ (U.comparison h).hom.app (A, (U.U F).obj (B, C)) ≫
            (U.U L).map (Prod.mkHom (𝟙 _) ((U.comparison h).hom.app (B, C))) =
          (U.comparison h).hom.app ((U.U F).obj (A, B), C) ≫
            (U.U L).map (Prod.mkHom ((U.comparison h).hom.app (A, B)) (𝟙 _)) ≫
            (α L ((S.T h).obj A) ((S.T h).obj B) ((S.T h).obj C)).hom := by
      intro F L h A B C
      dsimp only [U, S, BilinearCoefficientDescent.Family.U,
        BilinearCoefficientDescent.Family.comparison, rationalTensorStageComparison]
      exact associator_square_of_iso
        (C := Stage l Ω W F) (D := Stage l Ω W L)
        (U.U F) (U.U L) (S.T h) _
        (eqToIso ((stageSystem_existsUnique l Ω W).exists.choose_spec.1 F L h))
        (rationalTensorScalarComparison l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω F L h) W)
        (α F) (α L)
        (fun {A A' B B' C C'} a b c ↦ rationalAssociator_natural l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L) W a b c)
        (rationalAssociatorScalarExtensionSquare l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F)
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω L)
          (AlgebraicallyClosedCoefficients.coefficientInclusion l Ω F L h) W) A B C
    obtain ⟨e, he⟩ :=
      BilinearCoefficientDescent.associator_exists S U join left right α hn hc M N P
    change commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P ≅
      commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P) at e
    have h₁ := (commonStageDerivedTensor_existsUnique l Ω W).exists.choose_spec.1
    have hM : (commonStageDerivedTensor l Ω W).obj
        ((commonStageDerivedTensor l Ω W).obj (M, N), P) =
        commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P := by
      simp only [commonStageDerivedTensor]
      rw [h₁ M N, h₁]
    have hN : (commonStageDerivedTensor l Ω W).obj
        (M, (commonStageDerivedTensor l Ω W).obj (N, P)) =
        commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P) := by
      simp only [commonStageDerivedTensor]
      rw [h₁ N P, h₁]
    obtain ⟨d, hd, -⟩ := existsUnique_iso_of_eq hM hN e
    refine ⟨d, ?_⟩
    intro L hS hT
    refine hd.trans (heq_of_eq ?_)
    have he' := he L hS hT
    change e.hom = ofHom (commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P)
      (commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)) L hS hT
      ((BilinearCoefficientDescent.endpoint U join left right
            (commonStageTensorObject l Ω W M N, P) hS ≪≫
          (U.U L).mapIso (Iso.prod (BilinearCoefficientDescent.endpoint U join left right (M, N)
            ((left _ _).trans hS)) (Iso.refl _))).hom ≫
        (α L (M.toStage ((left _ _).trans ((left _ _).trans hS)))
          (N.toStage ((right _ _).trans ((left _ _).trans hS)))
          (P.toStage ((right _ _).trans hS))).hom ≫
        (BilinearCoefficientDescent.endpoint U join left right
            (M, commonStageTensorObject l Ω W N P) hT ≪≫
          (U.U L).mapIso (Iso.prod (Iso.refl _) (BilinearCoefficientDescent.endpoint U join left
            right (N, P) ((right _ _).trans hT)))).inv) at he'
    have hL : BilinearCoefficientDescent.endpoint U join left right
          (commonStageTensorObject l Ω W M N, P) hS ≪≫
        (U.U L).mapIso (Iso.prod (BilinearCoefficientDescent.endpoint U join left right (M, N)
          ((left _ _).trans hS)) (Iso.refl _)) = pullbackTensorCommonLeft l Ω W M N P L hS := by
      unfold pullbackTensorCommonLeft
      exact congrArg₂ (fun a b ↦ a ≪≫ (U.U L).mapIso (Iso.prod b (Iso.refl _)))
        (hendpoint (commonStageTensorObject l Ω W M N) P L hS)
        (hendpoint M N L ((left _ _).trans hS))
    have hR : BilinearCoefficientDescent.endpoint U join left right
          (M, commonStageTensorObject l Ω W N P) hT ≪≫
        (U.U L).mapIso (Iso.prod (Iso.refl _) (BilinearCoefficientDescent.endpoint U join left
          right (N, P) ((right _ _).trans hT))) = pullbackTensorCommonRight l Ω W M N P L hT := by
      unfold pullbackTensorCommonRight
      exact congrArg₂ (fun a b ↦ a ≪≫ (U.U L).mapIso (Iso.prod (Iso.refl _) b))
        (hendpoint M (commonStageTensorObject l Ω W N P) L hT)
        (hendpoint N P L ((right _ _).trans hT))
    apply he'.trans
    apply congrArg
    exact congrArg₂
      (fun a b ↦ a ≫ (α L (M.toStage ((left _ _).trans ((left _ _).trans hS)))
          (N.toStage ((right _ _).trans ((left _ _).trans hS)))
          (P.toStage ((right _ _).trans hS))).hom ≫ b)
      (congrArg Iso.hom hL) (congrArg Iso.inv hR)

end CommonAssociatorDescent


set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The common-stage associator has its prescribed representative at every larger field.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Conjugate the rational associator
by the
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
  obtain ⟨e, he⟩ := pullbackTensorCommonAssociator_exists l Ω W M N P
  refine ⟨e, he, ?_⟩
  intro d hd
  apply Iso.ext
  let S := commonStageTensorObject l Ω W (commonStageTensorObject l Ω W M N) P
  let T := commonStageTensorObject l Ω W M (commonStageTensorObject l Ω W N P)
  let L := Padic.finiteCoefficientCompositum l Ω S.stage T.stage
  let hS := ((Padic.finiteCoefficientFields_properties l Ω).1 S.stage T.stage).1
  let hT := ((Padic.finiteCoefficientFields_properties l Ω).1 S.stage T.stage).2
  exact eq_of_heq ((hd L hS hT).trans (he L hS hT).symm)

/-- The stage-independent rational associator class.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorCommonAssociator (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M N P : generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  ((@pullbackTensorCommonAssociator_existsUnique l _ Ω _ _ _ W hW) M N P).exists.choose

attribute [local irreducible] pullbackTensorCommonAssociator

end HigherCoherence

end WeilConjectures
