/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.Integral.AdicIntegralTensorCoordinates
import WeilConjectures.SixFunctors.Common.CommonProjectionPullbackTensorModels

/-! # Integral-stage coordinates for the canonical common-stage tensor comparison

Source: the representative clauses of the canonical rational and common-stage
pullback/tensor comparisons, and the raw coefficient localization convention.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option cleanup.letToHave false
attribute [local irreducible] HasDerivedCategory.standard

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

universe u
open CategoryTheory AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures.AdicQbarRealization
variable (l : ℕ) [Fact l.Prime]

attribute [local irreducible] commonStageDerivedPullback canonicalRationalPullbackTensor
  commonStagePullbackComparison commonStageTensorComparison operationStageTransitionIso
  ScalarLocalization.category

set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageCategory
  sfRationalConstructibleLocalization ScalarLocalization.localization
  GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.pairCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
  StageSystem.instCategoryPairCategory Functor.category

attribute [local irreducible] StageSystem.PairCategory.categoryStruct

private theorem inclusion_tensor_formula
    (W : Scheme.{u}) [∀ x : W, Invertible (l : W.residueField x)]
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (M N : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) W) :
    (commonInclusionTensorComparison l (PadicAlgCl l) W E).app (M, N) =
      (commonInclusionTensorModel l (PadicAlgCl l) W E M N ≪≫
        (GeneralAlgebraicallyClosedCoefficients.inclusion
          (l := l) (Ω := PadicAlgCl l) (Y := W) E).mapIso
          ((rationalDerivedTensor l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) W).mapIso
            (Iso.prod
              ((operationStageTransitionIso l (PadicAlgCl l) W E E le_rfl ≪≫
                GeneralAlgebraicallyClosedCoefficients.unitor l (PadicAlgCl l) W E).app M)
              ((operationStageTransitionIso l (PadicAlgCl l) W E E le_rfl ≪≫
                GeneralAlgebraicallyClosedCoefficients.unitor l (PadicAlgCl l) W E).app
                  N)))).symm := by
  unfold commonInclusionTensorComparison
  rfl

private theorem inclusion_tensor_eq
    (W : Scheme.{u}) [∀ x : W, Invertible (l : W.residueField x)]
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (M N : sfRationalConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) W) :
    (commonInclusionTensorComparison l (PadicAlgCl l) W E).app (M, N) =
      stageTensor l W (PadicAlgCl l) E M N := by
  rw [inclusion_tensor_formula]
  apply (stageTensor_existsUnique l W (PadicAlgCl l) E M N).unique
  · unfold stageTensorFormula
    refine heq_of_eq ?_
    unfold commonInclusionTensorModel
    simp only [Functor.mapIso_trans, Iso.trans_assoc]
    dsimp only [Functor.id_obj, Functor.comp_obj, Functor.prod_obj]
    unfold commonStageDerivedTensor
    rfl
  · unfold stageTensor
    exact (stageTensor_existsUnique l W (PadicAlgCl l) E M N).exists.choose_spec

private theorem chosen_spec {A : Sort*} {p : A → Prop} (h : ∃! a, p a)
    (a : A) (ha : a = h.exists.choose) : p a :=
  ha.symm ▸ h.exists.choose_spec

private theorem transported_square
    {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) (T : D × D ⥤ D)
    {A A' : C} {B B' U U' V V' : D}
    (a : A = A') (b : F.obj A' = B) (u : U = U') (v : V = V')
    (t : T.obj (U', V') = B') (f : F.obj A ⟶ T.obj (U, V)) (g : B ⟶ B')
    (h : HEq f g) :
    F.map (eqToIso a).inv ≫ f ≫
        T.map (Prod.mkHom (eqToIso u).hom (eqToIso v).hom) ≫ (eqToIso t).hom =
      (eqToIso b).hom ≫ g := by
  subst A' B U' V' B'
  simpa using eq_of_heq h

private def tensor_hom_transport
    {A B : Type*} [Category* A] [Category* B] {G H : A ⥤ B}
    (T : B × B ⥤ B) (e : G = H) {K M N : A}
    (μ : G.obj K ⟶ T.obj (G.obj M, G.obj N)) :
    H.obj K ⟶ T.obj (H.obj M, H.obj N) := e ▸ μ

private theorem tensor_hom_transport_heq
    {A B : Type*} [Category* A] [Category* B] {G H : A ⥤ B}
    (T : B × B ⥤ B) (e : G = H) {K M N : A}
    (μ : G.obj K ⟶ T.obj (G.obj M, G.obj N)) :
    HEq (tensor_hom_transport T e μ) μ := by
  subst H
  rfl

private theorem change_functor_square
    {A B : Type*} [Category* A] [Category* B] {G H : A ⥤ B}
    (T : B × B ⥤ B) (e : G = H) {K K' M N : A} {M' N' : B}
    (a : K ⟶ K') (μ : G.obj K' ⟶ T.obj (G.obj M, G.obj N))
    (ν : H.obj K' ⟶ T.obj (H.obj M, H.obj N)) (hμ : HEq μ ν)
    (b : H.obj M ⟶ M') (c : H.obj N ⟶ N') :
    G.map a ≫ μ ≫ T.map
        (Prod.mkHom ((eqToIso (congrArg (fun F ↦ F.obj M) e)).hom ≫ b)
          ((eqToIso (congrArg (fun F ↦ F.obj N) e)).hom ≫ c)) =
      (eqToIso (congrArg (fun F ↦ F.obj K) e)).hom ≫ H.map a ≫ ν ≫
        T.map (Prod.mkHom b c) := by
  subst H
  rw [eq_of_heq hμ]
  simp

private theorem combine_squares
    {A B : Type*} [Category* A] [Category* B] (I : A ⥤ B)
    {A0 A1 A2 A3 A4 A5 : A} {B1 B2 B3 : B}
    (a : A0 ⟶ A1) (b : A1 ⟶ A2) (c : A2 ⟶ A3) (e : A3 ≅ A5)
    (p : A0 ⟶ A4) (q : A4 ⟶ A5)
    (y : I.obj A1 ⟶ B1) (μ : B1 ⟶ B2) (z : B2 ⟶ B3)
    (c0 : I.obj A2 ⟶ B2) (c1 : I.obj A3 ⟶ B3)
    (hs : I.map b ≫ c0 = y ≫ μ) (hn : I.map c ≫ c1 = c0 ≫ z)
    (hrat : a ≫ b ≫ c ≫ e.hom = p ≫ q) :
    (I.map a ≫ y) ≫ μ ≫ z = I.map p ≫ I.map q ≫ I.map e.inv ≫ c1 := by
  have h : a ≫ b ≫ c = p ≫ q ≫ e.inv := by
    apply (cancel_mono e.hom).1
    simpa only [Category.assoc, Iso.inv_hom_id, Category.comp_id] using hrat
  calc
    (I.map a ≫ y) ≫ μ ≫ z = I.map a ≫ (y ≫ μ) ≫ z := by
      simp only [Category.assoc]
    _ = I.map a ≫ (I.map b ≫ c0) ≫ z := by rw [hs]
    _ = I.map a ≫ I.map b ≫ (c0 ≫ z) := by simp only [Category.assoc]
    _ = I.map a ≫ I.map b ≫ (I.map c ≫ c1) := by rw [hn]
    _ = I.map (a ≫ b ≫ c) ≫ c1 := by simp only [Functor.map_comp, Category.assoc]
    _ = I.map (p ≫ q ≫ e.inv) ≫ c1 := by rw [h]
    _ = _ := by simp only [Functor.map_comp, Category.assoc]

/-- `integralStageTensorIso` with its stage tensor replaced by the inclusion comparison. -/
private theorem integralStageTensorIso_eq
    (W : Scheme.{u}) [∀ x : W, Invertible (l : W.residueField x)]
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) W) :
    integralStageTensorIso l W E K L =
      (GeneralAlgebraicallyClosedCoefficients.inclusion
        (l := l) (Ω := PadicAlgCl l) (Y := W) E).mapIso
          (tensorIntegralObjectIso l W E K L).symm ≪≫
      (commonInclusionTensorComparison l (PadicAlgCl l) W E).app
        ((sfRationalConstructibleLocalization l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) W).obj K,
        (sfRationalConstructibleLocalization l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) W).obj L) := by
  unfold integralStageTensorIso
  rw [inclusion_tensor_eq l W E]
  rfl

attribute [local irreducible] rationalDerivedPullback rationalDerivedTensor
  commonStageDerivedTensor

set_option maxHeartbeats 2000000 in
-- Literal coordinate transports compare large stage-category instances during elaboration.
/-- The canonical common-stage tensor comparison in integral-stage coordinates.
This equation is solely about the existing coefficient operations; it contains no
ordinary realization, scalar-extension tensorator or reindexing comparison.
Source: Stacks 07A4; the representative clauses of
canonicalRationalPullbackTensor_existsUnique and canonicalCommonStagePullbackTensor_existsUnique.
(blueprint: lem-sf-adic-integral-stage-pull-tensor).

Proof: use the representative clause of the common-stage comparison at E, which
contains the compositum of the two identical input stages. Expand integralStageTensorIso
using stageTensorFormula. Its two normalized identity scalar-extension unitors cancel
the transition comparisons on the two inputs. The remaining representative is the
inclusion at E of the canonical rational pullback/tensor comparison. Its representative
clause identifies it with localization of the canonical integral comparison. The literal
object equations for rational tensor and pullback are precisely tensorIntegralObjectIso
and the second factor of integralStagePullIso. Functoriality of localization and stage
inclusion therefore gives the displayed equality after these transports. All transports
are isomorphisms, so they can be cancelled. This argument uses no enlargement of K or L,
no ordinary realization, and is valid also for the zero pair. -/
theorem integral_stage_pull_tensor
    {X Y : Scheme.{u}} (g : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (E : AlgebraicallyClosedCoefficients.Index l (PadicAlgCl l))
    (K L : sfIntegralConstructibleCategory l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y) :
    let P := constructibleIntegralPullback l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g
    let TY := constructibleIntegralTensor l
      (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) Y
    let JY := tensorStage l Y E
    let JX := tensorStage l X E
    let G := commonStageDerivedPullback l (PadicAlgCl l) g
    let TX := commonStageDerivedTensor l (PadicAlgCl l) X
    G.map (integralStageTensorIso l Y E K L).hom ≫
        (canonicalCommonStagePullbackTensor l (PadicAlgCl l) g (JY.obj K) (JY.obj L)).hom ≫
        TX.map (Prod.mkHom (integralStagePullIso l g E K).hom
          (integralStagePullIso l g E L).hom) =
      (integralStagePullIso l g E (TY.obj (K, L))).hom ≫
        JX.map (canonicalIntegralPullbackTensor l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E) g K L).hom ≫
        (integralStageTensorIso l X E (P.obj K) (P.obj L)).hom := by
  let F := AlgebraicallyClosedCoefficients.Coefficient.{u} l (PadicAlgCl l) E
  let QY := sfRationalConstructibleLocalization l F Y
  let QX := sfRationalConstructibleLocalization l F X
  let P := constructibleIntegralPullback l F g
  let R := rationalDerivedPullback l F g
  let TY := constructibleIntegralTensor l F Y
  let RX := rationalDerivedTensor l F X
  let IY := GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := Y) E
  let IX := GeneralAlgebraicallyClosedCoefficients.inclusion
    (l := l) (Ω := PadicAlgCl l) (Y := X) E
  let C := commonInclusionTensorComparison l (PadicAlgCl l) X E
  let CY := commonInclusionTensorComparison l (PadicAlgCl l) Y E
  have hp (M : sfIntegralConstructibleCategory l F Y) :
      R.obj (QY.obj M) = QX.obj (P.obj M) := by
    exact (chosen_spec (rationalDerivedPullback_existsUnique l F g) R
      (by unfold R rationalDerivedPullback; rfl)).2.1 (QY.obj M)
  have ht (W : Scheme.{u}) [∀ x : W, Invertible (l : W.residueField x)]
      (M N : sfIntegralConstructibleCategory l F W) :
      (rationalDerivedTensor l F W).obj
          ((sfRationalConstructibleLocalization l F W).obj M,
            (sfRationalConstructibleLocalization l F W).obj N) =
        (sfRationalConstructibleLocalization l F W).obj
          ((constructibleIntegralTensor l F W).obj (M, N)) := by
    exact (chosen_spec (rationalDerivedTensor_existsUnique l F W)
      (rationalDerivedTensor l F W) (by unfold rationalDerivedTensor; rfl)).1 _
  let p (M : sfIntegralConstructibleCategory l F Y) := eqToIso (hp M)
  have hr : HEq (canonicalRationalPullbackTensor l F g (QY.obj K) (QY.obj L)).hom
      (QX.map (canonicalIntegralPullbackTensor l F g K L).hom) := by
    simpa only [canonicalRationalPullbackTensor, pullbackTensorUniqueChoice] using
      (canonicalRationalPullbackTensor_existsUnique l F g
        (QY.obj K) (QY.obj L)).exists.choose_spec
  have hrat := transported_square R RX (ht Y K L) (hp (TY.obj (K, L)))
    (hp K) (hp L) (ht X (P.obj K) (P.obj L)) _ _ hr
  obtain ⟨hc, he⟩ := commonStagePullbackNormalizedDescent l (PadicAlgCl l) g
  let D := commonProjectionPullbackStages l (PadicAlgCl l) g hc
  have he' : commonStageDerivedPullback l (PadicAlgCl l) g = D.functor := he
  have hm := (canonicalCommonStagePullbackTensor_existsUnique l (PadicAlgCl l) g
    (IY.obj (QY.obj K)) (IY.obj (QY.obj L))).exists.choose_spec E
    (by change E.val ⊔ E.val ≤ E.val; exact sup_le le_rfl le_rfl)
  change HEq (canonicalCommonStagePullbackTensor l (PadicAlgCl l) g
    (IY.obj (QY.obj K)) (IY.obj (QY.obj L))).hom _ at hm
  have hs := commonProjectionInclusionPullbackTensorSquare l (PadicAlgCl l) g hc E
    (QY.obj K) (QY.obj L)
  let μ := tensor_hom_transport (commonStageDerivedTensor l (PadicAlgCl l) X) he'
    (canonicalCommonStagePullbackTensor l (PadicAlgCl l) g
      (IY.obj (QY.obj K)) (IY.obj (QY.obj L))).hom
  have hμ := tensor_hom_transport_heq (commonStageDerivedTensor l (PadicAlgCl l) X) he'
    (canonicalCommonStagePullbackTensor l (PadicAlgCl l) g
      (IY.obj (QY.obj K)) (IY.obj (QY.obj L))).hom
  have hs' := hs μ (hμ.trans hm)
  have hn := C.hom.naturality (Prod.mkHom (p K).hom (p L).hom)
  change IX.map (RX.map (Prod.mkHom (p K).hom (p L).hom)) ≫
      C.hom.app (QX.obj (P.obj K), QX.obj (P.obj L)) =
    C.hom.app (R.obj (QY.obj K), R.obj (QY.obj L)) ≫
      (commonStageDerivedTensor l (PadicAlgCl l) X).map
        (Prod.mkHom (IX.map (p K).hom) (IX.map (p L).hom)) at hn
  dsimp only
  simp only [integralStageTensorIso_eq l Y E, integralStageTensorIso_eq l X E]
  unfold integralStagePullIso
  dsimp only [Iso.trans, Functor.mapIso, Iso.symm, Iso.app, tensorStage,
    Functor.comp_obj, Functor.comp_map]
  simp only [Category.assoc]
  have hchange := change_functor_square
    (commonStageDerivedTensor l (PadicAlgCl l) X) he'
    (IY.map (tensorIntegralObjectIso l Y E K L).inv ≫ CY.hom.app (QY.obj K, QY.obj L))
    (canonicalCommonStagePullbackTensor l (PadicAlgCl l) g
      (IY.obj (QY.obj K)) (IY.obj (QY.obj L))).hom μ hμ.symm
    (IX.map (p K).hom) (IX.map (p L).hom)
  refine hchange.trans ?_
  apply (cancel_epi
    (eqToIso (congrArg (fun H ↦ H.obj (IY.obj (QY.obj (TY.obj (K, L))))) he')).hom).2
  rw [Functor.map_comp, D.functor_map_ι]
  exact combine_squares IX
    (R.map (tensorIntegralObjectIso l Y E K L).inv)
    (canonicalRationalPullbackTensor l F g (QY.obj K) (QY.obj L)).hom
    (RX.map (Prod.mkHom (p K).hom (p L).hom))
    (tensorIntegralObjectIso l X E (P.obj K) (P.obj L))
    (p (TY.obj (K, L))).hom
    (QX.map (canonicalIntegralPullbackTensor l F g K L).hom)
    (D.functor.map (CY.hom.app (QY.obj K, QY.obj L))) μ
    ((commonStageDerivedTensor l (PadicAlgCl l) X).map
      (Prod.mkHom (IX.map (p K).hom) (IX.map (p L).hom)))
    (C.hom.app (R.obj (QY.obj K), R.obj (QY.obj L)))
    (C.hom.app (QX.obj (P.obj K), QX.obj (P.obj L))) hs' hn hrat

end WeilConjectures.AdicQbarRealization
