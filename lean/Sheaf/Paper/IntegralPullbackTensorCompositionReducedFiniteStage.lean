/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralSystemReductionFullyFaithful
public import Sheaf.Paper.DerivedPullbackTensorConstraints
import all Sheaf.Paper.DerivedPullbackTensorConstraints
import Sheaf.Paper.IntegralPullbackFiniteReductionComposition
import Sheaf.Paper.FinitePullbackTensorComparison

/-! Finite coefficient stages of the reduced integral pullback/tensor equation.

Source: Stacks 07A4 and 0941; pure tensor calculation on each positive quotient
of the normalized coefficient tower.
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced-finite-stage)

The proof is intentionally split from the tower-level statement.  At one
quotient, choose flat-term K-flat representatives.  Both composites send a
pure tensor to the same pulled-back pair, and the formula commutes with the
transition maps.  The resulting equality descends through localization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall

universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

private theorem tensor_map_comp {C D : Type*} [Category* C] [Category* D]
    (T : C × C ⥤ D) {A B C₀ A' B' C₀' : C}
    (a : A ⟶ B) (b : B ⟶ C₀) (a' : A' ⟶ B') (b' : B' ⟶ C₀') :
    T.map (Prod.mkHom (a ≫ b) (a' ≫ b')) =
      T.map (Prod.mkHom a a') ≫ T.map (Prod.mkHom b b') := by
  rw [← T.map_comp]
  rfl

private theorem evaluated_tensor_square
    {C D S T S' T' : Type*}
    [Category* C] [Category* D] [Category* S] [Category* T]
    [Category* S'] [Category* T']
    (R : C ⥤ S) (Q : D ⥤ T) (F : C ⥤ D) (H : S ⥤ T)
    (E : S ⥤ S') (L : T ⥤ T') (U : S' ⥤ T')
    (A : C × C ⥤ C) (B : D × D ⥤ D)
    (J : S × S ⥤ S) (I : T × T ⥤ T)
    (J' : S' × S' ⥤ S') (I' : T' × T' ⥤ T')
    (a : A ⋙ R ≅ (R.prod R) ⋙ J)
    (b : B ⋙ Q ≅ (Q.prod Q) ⋙ I) (c : F ⋙ Q ≅ R ⋙ H)
    (α : J ⋙ E ≅ (E.prod E) ⋙ J') (β : I ⋙ L ≅ (L.prod L) ⋙ I')
    (γ : H ⋙ L ≅ E ⋙ U)
    (ν : ∀ M N, F.obj (A.obj (M, N)) ≅ B.obj (F.obj M, F.obj N))
    (μ : J ⋙ H ≅ (H.prod H) ⋙ I) (ω : J' ⋙ U ≅ (U.prod U) ⋙ I')
    (hν : ∀ M N, Q.map (ν M N).hom ≫ b.hom.app (F.obj M, F.obj N) ≫
      I.map (Prod.mkHom (c.hom.app M) (c.hom.app N)) =
      c.hom.app (A.obj (M, N)) ≫ H.map (a.hom.app (M, N)) ≫
        μ.hom.app (R.obj M, R.obj N))
    (hμ : ∀ M N, L.map (μ.hom.app (M, N)) ≫
      β.hom.app (H.obj M, H.obj N) ≫
      I'.map (Prod.mkHom (γ.hom.app M) (γ.hom.app N)) =
      γ.hom.app (J.obj (M, N)) ≫ U.map (α.hom.app (M, N)) ≫
        ω.hom.app (E.obj M, E.obj N)) (M N : C) :
    L.map (Q.map (ν M N).hom) ≫
        (L.map (b.hom.app (F.obj M, F.obj N)) ≫
          β.hom.app (Q.obj (F.obj M), Q.obj (F.obj N))) ≫
        I'.map (Prod.mkHom (L.map (c.hom.app M) ≫ γ.hom.app (R.obj M))
          (L.map (c.hom.app N) ≫ γ.hom.app (R.obj N))) =
      (L.map (c.hom.app (A.obj (M, N))) ≫ γ.hom.app (R.obj (A.obj (M, N)))) ≫
        U.map (E.map (a.hom.app (M, N)) ≫ α.hom.app (R.obj M, R.obj N)) ≫
        ω.hom.app (E.obj (R.obj M), E.obj (R.obj N)) := by
  simp only [tensor_map_comp, Functor.map_comp, Category.assoc]
  have hb := β.hom.naturality (Prod.mkHom (c.hom.app M) (c.hom.app N))
  change L.map (I.map (Prod.mkHom (c.hom.app M) (c.hom.app N))) ≫
      β.hom.app (H.obj (R.obj M), H.obj (R.obj N)) =
    β.hom.app (Q.obj (F.obj M), Q.obj (F.obj N)) ≫
      I'.map (Prod.mkHom (L.map (c.hom.app M)) (L.map (c.hom.app N))) at hb
  rw [← reassoc_of% hb]
  have hn := congrArg L.map (hν M N)
  simp only [Functor.map_comp] at hn
  rw [reassoc_of% hn]
  rw [hμ]
  have hc := γ.hom.naturality (a.hom.app (M, N))
  change L.map (H.map (a.hom.app (M, N))) ≫
      γ.hom.app (J.obj (R.obj M, R.obj N)) =
    γ.hom.app (R.obj (A.obj (M, N))) ≫ U.map (E.map (a.hom.app (M, N))) at hc
  rw [reassoc_of% hc]

private theorem reduced_tensor_composition
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category* C₀] [Category* C₁] [Category* C₂]
    [Category* D₀] [Category* D₁] [Category* D₂]
    (R₀ : C₀ ⥤ D₀) (R₁ : C₁ ⥤ D₁) (R₂ : C₂ ⥤ D₂)
    (T₀ : C₀ × C₀ ⥤ C₀) (T₁ : C₁ × C₁ ⥤ C₁) (T₂ : C₂ × C₂ ⥤ C₂)
    (S₀ : D₀ × D₀ ⥤ D₀) (S₁ : D₁ × D₁ ⥤ D₁) (S₂ : D₂ × D₂ ⥤ D₂)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (J : C₀ ⥤ C₂)
    (U : D₀ ⥤ D₁) (V : D₁ ⥤ D₂) (W : D₀ ⥤ D₂)
    (a₀ : T₀ ⋙ R₀ ≅ (R₀.prod R₀) ⋙ S₀)
    (a₁ : T₁ ⋙ R₁ ≅ (R₁.prod R₁) ⋙ S₁)
    (a₂ : T₂ ⋙ R₂ ≅ (R₂.prod R₂) ⋙ S₂)
    (bF : F ⋙ R₁ ≅ R₀ ⋙ U) (bG : G ⋙ R₂ ≅ R₁ ⋙ V)
    (bJ : J ⋙ R₂ ≅ R₀ ⋙ W)
    (νF : ∀ M N, F.obj (T₀.obj (M, N)) ≅ T₁.obj (F.obj M, F.obj N))
    (νG : ∀ M N, G.obj (T₁.obj (M, N)) ≅ T₂.obj (G.obj M, G.obj N))
    (νJ : ∀ M N, J.obj (T₀.obj (M, N)) ≅ T₂.obj (J.obj M, J.obj N))
    (μF : S₀ ⋙ U ≅ (U.prod U) ⋙ S₁)
    (μG : S₁ ⋙ V ≅ (V.prod V) ⋙ S₂)
    (μJ : S₀ ⋙ W ≅ (W.prod W) ⋙ S₂)
    (c : J ≅ F ⋙ G) (d : W ≅ U ⋙ V)
    (hF : ∀ M N, R₁.map (νF M N).hom ≫ a₁.hom.app (F.obj M, F.obj N) ≫
      S₁.map (Prod.mkHom (bF.hom.app M) (bF.hom.app N)) =
      bF.hom.app (T₀.obj (M, N)) ≫ U.map (a₀.hom.app (M, N)) ≫
        μF.hom.app (R₀.obj M, R₀.obj N))
    (hG : ∀ M N, R₂.map (νG M N).hom ≫ a₂.hom.app (G.obj M, G.obj N) ≫
      S₂.map (Prod.mkHom (bG.hom.app M) (bG.hom.app N)) =
      bG.hom.app (T₁.obj (M, N)) ≫ V.map (a₁.hom.app (M, N)) ≫
        μG.hom.app (R₁.obj M, R₁.obj N))
    (hJ : ∀ M N, R₂.map (νJ M N).hom ≫ a₂.hom.app (J.obj M, J.obj N) ≫
      S₂.map (Prod.mkHom (bJ.hom.app M) (bJ.hom.app N)) =
      bJ.hom.app (T₀.obj (M, N)) ≫ W.map (a₀.hom.app (M, N)) ≫
        μJ.hom.app (R₀.obj M, R₀.obj N))
    (hc : ∀ K, R₂.map (c.hom.app K) ≫ bG.hom.app (F.obj K) ≫
      V.map (bF.hom.app K) = bJ.hom.app K ≫ d.hom.app (R₀.obj K))
    (hd : ∀ M N, μJ.hom.app (M, N) ≫
      S₂.map (Prod.mkHom (d.hom.app M) (d.hom.app N)) =
      d.hom.app (S₀.obj (M, N)) ≫ V.map (μF.hom.app (M, N)) ≫
        μG.hom.app (U.obj M, U.obj N)) (M N : C₀) :
    R₂.map ((νJ M N).hom ≫ T₂.map (Prod.mkHom (c.hom.app M) (c.hom.app N))) =
      R₂.map (c.hom.app (T₀.obj (M, N)) ≫ G.map (νF M N).hom ≫
        (νG (F.obj M) (F.obj N)).hom) := by
  apply (cancel_mono (a₂.hom.app (G.obj (F.obj M), G.obj (F.obj N)))).1
  apply (cancel_mono (S₂.mapIso
    (Iso.prod (bG.app (F.obj M)) (bG.app (F.obj N)))).hom).1
  apply (cancel_mono (S₂.mapIso
    (Iso.prod (V.mapIso (bF.app M)) (V.mapIso (bF.app N)))).hom).1
  simp only [Functor.mapIso_hom, Iso.prod_hom, Iso.app_hom]
  simp only [Functor.map_comp, Category.assoc]
  have ha := a₂.hom.naturality (Prod.mkHom (c.hom.app M) (c.hom.app N))
  change R₂.map (T₂.map (Prod.mkHom (c.hom.app M) (c.hom.app N))) ≫
      a₂.hom.app (G.obj (F.obj M), G.obj (F.obj N)) =
    a₂.hom.app (J.obj M, J.obj N) ≫
      S₂.map (Prod.mkHom (R₂.map (c.hom.app M)) (R₂.map (c.hom.app N))) at ha
  rw [reassoc_of% ha]
  simp only [← tensor_map_comp]
  rw [hc M, hc N]
  simp only [tensor_map_comp]
  rw [reassoc_of% (hJ M N), hd]
  have hn := d.hom.naturality (a₀.hom.app (M, N))
  change W.map (a₀.hom.app (M, N)) ≫
      d.hom.app (S₀.obj (R₀.obj M, R₀.obj N)) =
    d.hom.app (R₀.obj (T₀.obj (M, N))) ≫ V.map (U.map (a₀.hom.app (M, N))) at hn
  rw [reassoc_of% hn, reassoc_of% (hG (F.obj M) (F.obj N))]
  have hg := μG.hom.naturality (Prod.mkHom (bF.hom.app M) (bF.hom.app N))
  change V.map (S₁.map (Prod.mkHom (bF.hom.app M) (bF.hom.app N))) ≫
      μG.hom.app (U.obj (R₀.obj M), U.obj (R₀.obj N)) =
    μG.hom.app (R₁.obj (F.obj M), R₁.obj (F.obj N)) ≫
      S₂.map (Prod.mkHom (V.map (bF.hom.app M)) (V.map (bF.hom.app N))) at hg
  rw [← hg]
  have hb := bG.hom.naturality (νF M N).hom
  change R₂.map (G.map (νF M N).hom) ≫
      bG.hom.app (T₁.obj (F.obj M, F.obj N)) =
    bG.hom.app (F.obj (T₀.obj (M, N))) ≫ V.map (R₁.map (νF M N).hom) at hb
  rw [reassoc_of% hb]
  have hf := congrArg V.map (hF M N)
  simp only [Functor.map_comp] at hf
  rw [reassoc_of% hf]
  rw [reassoc_of% (hc (T₀.obj (M, N)))]

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E]
  [FiniteDimensional (Padic l) E]

private def finiteReduction (W : Scheme.{u}) (n : ℕ) :=
  coherentReduction l E W ⋙ coefficientSequenceDerivedEvaluation l E W n

private def finiteTensorReduction (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] (n : ℕ) :
    constructibleIntegralTensor l E W ⋙ finiteReduction l E W n ≅
      ((finiteReduction l E W n).prod (finiteReduction l E W n)) ⋙
        finiteIntrinsicDerivedTensor l E W n :=
  Functor.isoWhiskerRight (reduction_tensor l E W)
      (coefficientSequenceDerivedEvaluation l E W n) ≪≫
    Functor.isoWhiskerLeft ((coherentReduction l E W).prod (coherentReduction l E W))
      ((pullbackTensorCalculus l E W).evaluationTensor n)

private def finitePullbackReduction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] (n : ℕ) :
    constructibleIntegralPullback l E f ⋙ finiteReduction l E X n ≅
      finiteReduction l E Y n ⋙ finiteDerivedPullback l E n f :=
  Functor.isoWhiskerRight (reduction_pullback l E f)
      (coefficientSequenceDerivedEvaluation l E X n) ≪≫
    Functor.isoWhiskerLeft (coherentReduction l E Y)
      (pullbackTensorDerivedEvaluation l E f n)

private theorem finitePullbackReduction_hom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (n : ℕ) (K : sfIntegralConstructibleCategory l E Y) :
    (finitePullbackReduction l E f n).hom.app K =
      (coefficientSequenceDerivedEvaluation l E X n).map
          (pullbackTensorIntegralReductionPullback l E f K).hom ≫
        (pullbackTensorDerivedEvaluation l E f n).hom.app
          ((pullbackTensorCalculus l E Y).reduction.obj K.obj) := by
  with_unfolding_all rfl

private theorem finiteComparison_square {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (n : ℕ) (M N : sfIntegralConstructibleCategory l E Y) :
    (finiteReduction l E X n).map (canonicalIntegralPullbackTensor l E f M N).hom ≫
      (finiteTensorReduction l E X n).hom.app
        ((constructibleIntegralPullback l E f).obj M,
          (constructibleIntegralPullback l E f).obj N) ≫
      (finiteIntrinsicDerivedTensor l E X n).map
        (Prod.mkHom ((finitePullbackReduction l E f n).hom.app M)
          ((finitePullbackReduction l E f n).hom.app N)) =
    (finitePullbackReduction l E f n).hom.app
        ((constructibleIntegralTensor l E Y).obj (M, N)) ≫
      (finiteDerivedPullback l E n f).map ((finiteTensorReduction l E Y n).hom.app (M, N)) ≫
      (canonicalFinitePullbackTensor l E f n
        ((finiteReduction l E Y n).obj M) ((finiteReduction l E Y n).obj N)).hom := by
  have hh := evaluated_tensor_square
    (coherentReduction l E Y) (coherentReduction l E X)
    (constructibleIntegralPullback l E f) (pullbackTensorSequenceDerived l E f)
    (coefficientSequenceDerivedEvaluation l E Y n)
    (coefficientSequenceDerivedEvaluation l E X n) (finiteDerivedPullback l E n f)
    (constructibleIntegralTensor l E Y) (constructibleIntegralTensor l E X)
    (pullbackTensorCalculus l E Y).systemClosed.tensor
    (pullbackTensorCalculus l E X).systemClosed.tensor
    (finiteIntrinsicDerivedTensor l E Y n) (finiteIntrinsicDerivedTensor l E X n)
    (reduction_tensor l E Y) (reduction_tensor l E X) (reduction_pullback l E f)
    ((pullbackTensorCalculus l E Y).evaluationTensor n)
    ((pullbackTensorCalculus l E X).evaluationTensor n)
    (pullbackTensorDerivedEvaluation l E f n) (canonicalIntegralPullbackTensor l E f)
    (pullbackTensorSystemComparison l E f) (finitePullbackTensorConstructionIso l E f n)
    (integralComparison_reduction l E f) (pullbackTensorSystemComparison_evaluation l E f n)
    M N
  with_unfolding_all exact hh

/-- The reduced pullback/tensor composites agree after every finite evaluation.

Source: Stacks 07A4 and 0941, quotient-stage pure-tensor calculation.
(blueprint: lem-pur-pullback-tensor-integral-composition-reduced-finite-stage)

At a positive coefficient quotient, the two displayed maps are represented by
identical pure-tensor formulas on flat-term K-flat representatives.  These
formulas commute with quotient transitions, so localization gives the stated
morphism equality.  This is the finite-stage part of the quotient-tower
argument; the tower extensionality step is recorded separately.
-/
theorem integralPullbackTensorCompositionReduced_finiteStage
    {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (h : Z ⟶ X)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    [hZ : ∀ z : Z, Invertible (l : Z.residueField z)]
    (M N : sfIntegralConstructibleCategory l E Y) (n : ℕ) :
    (finiteSystemDerivedEvaluation (integralSystemRings l E)
        (integralSystemTransition l E) Z n).map
        ((integralSystemReduction l E Z).map
          (((@canonicalIntegralPullbackTensor l _ E _ _ _ Z Y (h ≫ f) hZ hY) M N).hom ≫
            ((@constructibleIntegralTensor l _ E _ _ _ Z hZ)).map (Prod.mkHom
              (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app M)
              (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app N)))) =
      (finiteSystemDerivedEvaluation (integralSystemRings l E)
        (integralSystemTransition l E) Z n).map
        ((integralSystemReduction l E Z).map
          (((@pullbackTensorIntegralComposition l _ E _ _ _ X Y Z f h hX hY hZ)).hom.app
            (((@constructibleIntegralTensor l _ E _ _ _ Y hY)).obj (M, N)) ≫
            ((@constructibleIntegralPullback l _ E _ _ _ Z X h hZ hX)).map
              ((@canonicalIntegralPullbackTensor l _ E _ _ _ X Y f hX hY) M N).hom ≫
            ((@canonicalIntegralPullbackTensor l _ E _ _ _ Z X h hZ hX)
              (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj M)
              (((@constructibleIntegralPullback l _ E _ _ _ X Y f hX hY)).obj N)).hom)) := by
  change (finiteReduction l E Z n).map _ = (finiteReduction l E Z n).map _
  apply reduced_tensor_composition
    (finiteReduction l E Y n) (finiteReduction l E X n) (finiteReduction l E Z n)
    (constructibleIntegralTensor l E Y) (constructibleIntegralTensor l E X)
    (constructibleIntegralTensor l E Z)
    (finiteIntrinsicDerivedTensor l E Y n) (finiteIntrinsicDerivedTensor l E X n)
    (finiteIntrinsicDerivedTensor l E Z n)
    (constructibleIntegralPullback l E f) (constructibleIntegralPullback l E h)
    (constructibleIntegralPullback l E (h ≫ f))
    (finiteDerivedPullback l E n f) (finiteDerivedPullback l E n h)
    (finiteDerivedPullback l E n (h ≫ f))
    (finiteTensorReduction l E Y n) (finiteTensorReduction l E X n)
    (finiteTensorReduction l E Z n)
    (finitePullbackReduction l E f n) (finitePullbackReduction l E h n)
    (finitePullbackReduction l E (h ≫ f) n)
    (canonicalIntegralPullbackTensor l E f) (canonicalIntegralPullbackTensor l E h)
    (canonicalIntegralPullbackTensor l E (h ≫ f))
    (finitePullbackTensorConstructionIso l E f n) (finitePullbackTensorConstructionIso l E h n)
    (finitePullbackTensorConstructionIso l E (h ≫ f) n)
    (pullbackTensorIntegralComposition l E f h)
    (sfIntrinsicDerivedPullbackComp (finiteCoefficientRing l E (n + 1)) h f)
    (finiteComparison_square l E f n) (finiteComparison_square l E h n)
    (finiteComparison_square l E (h ≫ f) n) ?_
    (canonicalFinitePullbackTensor_composition l E f h n) M N
  intro K
  rw [finitePullbackReduction_hom, finitePullbackReduction_hom,
    finitePullbackReduction_hom]
  refine (congrArg
    (fun a ↦ (finiteReduction l E Z n).map
      ((pullbackTensorIntegralComposition l E f h).hom.app K) ≫ a)
    (Category.assoc _ _ _)).trans ?_
  with_unfolding_all exact integralPullback_finiteReduction_composition l E f h K n

end WeilConjectures
