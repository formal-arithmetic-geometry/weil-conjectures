/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.AdicQbarRealization.CommonStageInclusionTensorComparison
public import WeilConjectures.SixFunctors.Supporting.DerivedAutomorphismHomEvaluationContinuationA
import all WeilConjectures.SixFunctors.GeneralAlgebraicallyClosedCoefficients.GeneralAlgebraicallyClosedCoefficientStages

/-! # Finite-stage normalization of common-stage evaluation

Source: Bhatt--Scholze, Lemma 3.4.11 and Proposition 6.8.14; the finite-stage
square in step 7 of lem-sf-adic-ambient-hom-evaluation-comparison.
The module also proves the generic adjunction, symmetry, and transition calculations
used to realize that square and assemble the coherence laws.
(blueprint: lem-sf-common-stage-evaluation-finite-square).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] HasDerivedCategory.standard

universe u v
open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme

namespace WeilConjectures

/-- The chosen common-stage internal Hom has its prescribed literal object.
This is the object clause of its defining unique-existence theorem.
Source: the common-stage Hom construction in def-weil-derived-pullback-tensor-hom. -/
theorem commonStageDerivedInternalHom_obj_eq
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (P : (commonStageHomPairs l Ω X).FullSubcategory) :
    (commonStageDerivedInternalHom l Ω X).obj P = commonStageHomObject l Ω X P := by
  unfold commonStageDerivedInternalHom
  exact (commonStageDerivedInternalHom_existsUnique l Ω X).exists.choose_spec.1 P

attribute [local irreducible] commonStageDerivedInternalHom

section FiniteSquareProof
universe w
set_option Elab.async false
set_option cleanup.letToHave false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] commonStageTensorComparison commonStageHomComparison
  podRationalClosed rationalDerivedTensor rationalDerivedInternalHom
set_option linter.auxLemma false in
set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.Stage
  GeneralAlgebraicallyClosedCoefficients.stageCategory
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_1
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_3
  GeneralAlgebraicallyClosedCoefficients.stageCategory._aux_5
  commonStageHomPairAtStage

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.pairCategory
  CategoryTheory.uniformProd ObjectProperty.FullSubcategory.category
attribute [local implicit_reducible] catToReflQuiver
attribute [local irreducible] ScalarLocalization.category
attribute [local instance 2000] GeneralAlgebraicallyClosedCoefficients.pairCategory
  GeneralAlgebraicallyClosedCoefficients.preadditive

open GeneralAlgebraicallyClosedCoefficients
open AlgebraicallyClosedCoefficients (Index Coefficient coefficientInclusion
  coefficientInclusion_laws)
attribute [local irreducible] sfRationalScalarExtension sfRationalScalarComp sfRationalScalarUnit
  GeneralAlgebraicallyClosedCoefficients.scalarAssociator
private theorem partial_uncurry
    {C : Type*} [Category C] [Preadditive C]
    {T : C × C ⥤ C} {J : ObjectProperty (Cᵒᵖ × C)} {H : J.FullSubcategory ⥤ C}
    (S : PodPartialClosed T J H) (L : C) (P : J.FullSubcategory) (f : L ⟶ H.obj P) :
    (S.transpose L P).symm f = T.map (Prod.mkHom f (𝟙 _)) ≫ S.evaluation P := by
  apply (S.transpose L P).injective
  rw [S.parameter_naturality]
  simp only [PodPartialClosed.evaluation, AddEquiv.apply_symm_apply, Category.comp_id]

private theorem evaluation_transport
    {C : Type*} [Category C] [Preadditive C]
    {T : C × C ⥤ C} {J : ObjectProperty (Cᵒᵖ × C)} {H : J.FullSubcategory ⥤ C}
    (S : PodPartialClosed T J H) (P : J.FullSubcategory) (B : C) (h : H.obj P = B) :
    HEq (S.evaluation P) ((S.transpose B P).symm (eqToHom h.symm)) := by
  subst B
  rfl

private theorem identity_transport {C : Type*} [Category C]
    {A B : C} (h : A = B) : HEq (eqToHom h.symm) (𝟙 B) := by
  subst B
  rfl

private theorem tensor_precomp {C : Type*} [Category C] (T : C × C ⥤ C)
    {H H' M K L : C} (f : H ⟶ H') (a : H' ⟶ K) (b : M ⟶ L) :
    T.map (Prod.mkHom (f ≫ a) b) =
      T.map (Prod.mkHom f (𝟙 M)) ≫ T.map (Prod.mkHom a b) := by
  rw [← T.map_comp]
  simp only [CategoryTheory.prod_comp, Category.id_comp]

private theorem transported_arrow {C : Type*} [Category C] (T : C × C ⥤ C)
    {A A' M B N : C} (hA : A = A') (hB : T.obj (A', M) = B)
    (f : T.obj (A, M) ⟶ N) (g : B ⟶ N) (h : HEq f g) :
    T.map (Prod.mkHom (eqToHom hA) (𝟙 M)) ≫ eqToHom hB ≫ g = f := by
  subst A'
  subst B
  simpa using (eq_of_heq h).symm

private theorem scalar_coherence_right
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L) (X : Scheme.{u})
    (K : sfRationalConstructibleCategory l E X) :
    (sfRationalScalarComp l E L i X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L (AlgHom.id _ _)).hom.app K =
    (sfRationalScalarUnit l L X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app
      ((sfRationalScalarExtension l E X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i).obj K) :=
  (sfRationalScalar_coherence l E L i X 0
    (Nat.Prime.ne_zero (Fact.out : l.Prime)) L (AlgHom.id _ _)).2.1 K

private theorem scalar_initial_unit
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L)
    (h : (AlgHom.id (Padic l) L).comp i = i) (X : Scheme.{u})
    (K : sfRationalConstructibleCategory l E X) :
    (scalarAssociator l E L L i (AlgHom.id _ _) i h X).hom.app K =
      (sfRationalScalarUnit l L X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app
          ((sfRationalScalarExtension l E X 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i).obj K) := by
  unfold scalarAssociator
  have he : (eqToIso (congrArg (sfRationalScalarExtension l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) L) h)).hom.app K = 𝟙 _ := by rfl
  dsimp only [Iso.trans_hom, NatTrans.comp_app]
  rw [he]
  exact (Category.comp_id _).trans (scalar_coherence_right l E L i X K)

private theorem at_reflexive {α : Sort*} (a : α)
    (P : ∀ b : α, b = a → Prop) (hp : P a rfl) (b : α) (hb : b = a) : P b hb := by
  subst b
  exact hp

set_option maxHeartbeats 600000 in
-- Allow the concrete coefficient-category transports to be checked.
private theorem scalar_right_unit
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] L) (hj : j = AlgHom.id _ _)
    (h : j.comp i = i) (X : Scheme.{u})
    (K : sfRationalConstructibleCategory l E X) :
    (scalarAssociator l E L L i j i h X).hom.app K =
      (eqToIso (congrArg (sfRationalScalarExtension l L X 0
        (Nat.Prime.ne_zero (Fact.out : l.Prime)) L) hj) ≪≫
        sfRationalScalarUnit l L X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app
          ((sfRationalScalarExtension l E X 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i).obj K) := by
  refine at_reflexive (AlgHom.id (Padic l) L)
    (fun j hj ↦ ∀ h : j.comp i = i,
      (scalarAssociator l E L L i j i h X).hom.app K =
        (eqToIso (congrArg (sfRationalScalarExtension l L X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L) hj) ≪≫
          sfRationalScalarUnit l L X 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime))).hom.app
              ((sfRationalScalarExtension l E X 0
                (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i).obj K)) ?_ j hj h
  intro h
  simpa only [Iso.trans_hom, NatTrans.comp_app, eqToIso.hom, eqToHom_refl,
    NatTrans.id_app, Category.id_comp] using scalar_initial_unit l E L i h X K

private theorem scalar_unit_iso
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] L) (hj : j = AlgHom.id _ _)
    (h : j.comp i = i) (X : Scheme.{u}) :
    scalarAssociator l E L L i j i h X =
      Functor.isoWhiskerLeft
        (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i)
        (eqToIso (congrArg (sfRationalScalarExtension l L X 0
          (Nat.Prime.ne_zero (Fact.out : l.Prime)) L) hj) ≪≫
          sfRationalScalarUnit l L X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime))) ≪≫
        Functor.rightUnitor
          (sfRationalScalarExtension l E X 0 (Nat.Prime.ne_zero (Fact.out : l.Prime)) L i) := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  exact (scalar_right_unit l E L i j hj h X K).trans (Category.comp_id _).symm

private theorem transition_unit_iso
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (X : Scheme.{u})
    (E F : Index l Ω) (h : E ≤ F) :
    associator l Ω X E F F h le_rfl =
      Functor.isoWhiskerLeft (transition l Ω X E F h) (unitor l Ω X F) ≪≫
        Functor.rightUnitor (transition l Ω X E F h) := by
  rw [GeneralAlgebraicallyClosedCoefficients.associator_formula]
  exact scalar_unit_iso l (Coefficient.{u} l Ω E) (Coefficient.{u} l Ω F)
    (coefficientInclusion l Ω E F h) (coefficientInclusion l Ω F F le_rfl)
    ((coefficientInclusion_laws l Ω).1 F)
    ((coefficientInclusion_laws l Ω).2 E F F h le_rfl) X

private theorem right_unit_component
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ D) (a : F ⋙ G ≅ F) (unit : G ≅ 𝟭 D)
    (h : a = Functor.isoWhiskerLeft F unit ≪≫ Functor.rightUnitor F) (K : C) :
    a.hom.app K = unit.hom.app (F.obj K) := by
  rw [h]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  exact Category.comp_id _

private theorem transition_right_unit
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (X : Scheme.{u})
    (E F : Index l Ω) (h : E ≤ F) (K : Stage l Ω X E) :
    (associator l Ω X E F F h le_rfl).hom.app K =
      (unitor l Ω X F).hom.app ((transition l Ω X E F h).obj K) := by
  exact right_unit_component _ _ _ _
    (transition_unit_iso l Ω X E F h) K

private theorem functor_unit_transport
    {C D : Type*} [Category C] [Category D]
    (F F₀ : C ⥤ D) (G G₀ : D ⥤ D) (hF : F = F₀) (hG : G = G₀)
    (a : F ⋙ G ≅ F) (a₀ : F₀ ⋙ G₀ ≅ F₀) (ha : HEq a a₀)
    (unit : G₀ ≅ 𝟭 D) (K : C)
    (hu : a₀.hom.app K = unit.hom.app (F₀.obj K)) :
    a.hom.app K = (eqToIso hG ≪≫ unit).hom.app (F.obj K) := by
  subst F₀
  subst G₀
  rw [eq_of_heq ha]
  simpa using hu

private theorem stage_right_unit
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (X : Scheme.{u})
    (E F : Index l Ω) (h : E ≤ F) (K : Stage l Ω X E) :
    ((stageSystem l Ω X).assoc h le_rfl).hom.app K =
      (operationStageTransitionIso l Ω X F F le_rfl ≪≫ unitor l Ω X F).hom.app
        (((stageSystem l Ω X).T h).obj K) := by
  have hs := (stageSystem_existsUnique l Ω X).exists.choose_spec
  exact functor_unit_transport
    ((stageSystem l Ω X).T h) (transition l Ω X E F h)
    ((stageSystem l Ω X).T (i := F) (j := F) (le_refl F)) (transition l Ω X F F le_rfl)
    (hs.1 E F h) (hs.1 F F le_rfl)
    ((stageSystem l Ω X).assoc h le_rfl) (associator l Ω X E F F h le_rfl)
    (hs.2 E F F h le_rfl) (unitor l Ω X F) K
    (transition_right_unit l Ω X E F h K)

attribute [local irreducible] sfIntegralConstructible ScalarLocalization.linear
  ScalarLocalization.preadditive Linear.homModule Preadditive.homGroup Preadditive.fullSubcategory
  Linear.fullSubcategory sfIntegralConstructibleLinear sfIntegralScalarComp sfIntegralScalarUnit
attribute [local irreducible] operationStageTransitionIso sfConstructibleIntegralScalarExtension
set_option allowUnsafeReducibility true in
attribute [local irreducible] stageSystem

private theorem tensor_spec
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)] :
    (∀ P Q, (commonStageDerivedTensor l Ω X).obj (P, Q) = commonStageTensorObject l Ω X P Q) ∧
      (∀ (P Q P' Q' : generalAlgebraicallyClosedConstructibleCategory l Ω X)
        (L : Index l Ω)
        (h : (commonStageTensorObject l Ω X P Q).stage ≤ L)
        (h' : (commonStageTensorObject l Ω X P' Q').stage ≤ L)
        (a : P.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1.trans h) ⟶
          P'.toStage
            (((Padic.finiteCoefficientFields_properties l Ω).1 P'.stage Q'.stage).1.trans h'))
        (b : Q.toStage
          (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2.trans h) ⟶
          Q'.toStage
            (((Padic.finiteCoefficientFields_properties l Ω).1 P'.stage Q'.stage).2.trans h')),
        HEq ((commonStageDerivedTensor l Ω X).map (X := (P, Q)) (Y := (P', Q')) (Prod.mkHom
          (ofHom P P' L
            (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).1.trans h)
            (((Padic.finiteCoefficientFields_properties l Ω).1 P'.stage Q'.stage).1.trans h') a)
          (ofHom Q Q' L
            (((Padic.finiteCoefficientFields_properties l Ω).1 P.stage Q.stage).2.trans h)
            (((Padic.finiteCoefficientFields_properties l Ω).1 P'.stage Q'.stage).2.trans h') b)))
          (ofHom (commonStageTensorObject l Ω X P Q)
            (commonStageTensorObject l Ω X P' Q') L h h'
            ((commonStageTensorComparison l Ω X P Q L h).hom ≫
              (rationalDerivedTensor l (Coefficient.{u} l Ω L) X).map (Prod.mkHom a b) ≫
              (commonStageTensorComparison l Ω X P' Q' L h').inv))) := by
  unfold commonStageDerivedTensor
  exact (commonStageDerivedTensor_existsUnique l Ω X).exists.choose_spec

attribute [local irreducible] commonStageDerivedTensor

private theorem iso_cast_heq
    {C : Type*} [Category C] {A B N P : C}
    (hA : A = N) (hB : B = N) (e : N ≅ P) :
    HEq (eqToIso hA ≪≫ e).symm (eqToIso hB ≪≫ e).symm := by
  subst A
  subst B
  rfl

private theorem stage_tensor_formula
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (F : Index l Ω) (K L : Stage l Ω X F) :
    HEq (AdicQbarRealization.stageTensor l X Ω F K L) (
      let I := inclusion (l := l) (Ω := Ω) (Y := X) F
      let P := I.obj K
      let Q := I.obj L
      let h : (commonStageTensorObject l Ω X P Q).stage ≤ F := by
        change F.val ⊔ F.val ≤ F.val
        exact sup_le le_rfl le_rfl
      let e := operationStageTransitionIso l Ω X F F le_rfl ≪≫ unitor l Ω X F
      (eqToIso ((tensor_spec l Ω X).1 P Q) ≪≫
        (stageSystem l Ω X).isoToStage (commonStageTensorObject l Ω X P Q) h ≪≫
        I.mapIso (commonStageTensorComparison l Ω X P Q F h ≪≫
          (rationalDerivedTensor l (Coefficient.{u} l Ω F) X).mapIso
            (Iso.prod (e.app K) (e.app L)))).symm) := by
  have ht : AdicQbarRealization.stageTensorFormula l X Ω F K L
      (AdicQbarRealization.stageTensor l X Ω F K L) := by
    unfold AdicQbarRealization.stageTensor
    exact (AdicQbarRealization.stageTensor_existsUnique l X Ω F K L).exists.choose_spec
  unfold AdicQbarRealization.stageTensorFormula at ht
  let I := inclusion (l := l) (Ω := Ω) (Y := X) F
  let h : (commonStageTensorObject l Ω X (I.obj K) (I.obj L)).stage ≤ F := by
    change F.val ⊔ F.val ≤ F.val
    exact sup_le le_rfl le_rfl
  let e := operationStageTransitionIso l Ω X F F le_rfl ≪≫ unitor l Ω X F
  exact ht.trans (iso_cast_heq
    ((commonStageDerivedTensor_existsUnique l Ω X).exists.choose_spec.1 (I.obj K) (I.obj L))
    ((tensor_spec l Ω X).1 (I.obj K) (I.obj L))
    ((stageSystem l Ω X).isoToStage (commonStageTensorObject l Ω X (I.obj K) (I.obj L)) h ≪≫
      I.mapIso (commonStageTensorComparison l Ω X (I.obj K) (I.obj L) F h ≪≫
        (rationalDerivedTensor l (Coefficient.{u} l Ω F) X).mapIso
          (Iso.prod (e.app K) (e.app L)))))

private theorem substitute_heq {α : Sort*} {β γ : Sort w} (f : α → β)
    {x y : α} (h : x = y) {z : γ} (hy : HEq (f y) z) : HEq (f x) z := by
  subst x
  exact hy

private theorem model_square
    {A B : Type*} [Category* A] [Category* B] (I : A ⥤ B)
    {M N M' N' : B} (hM : M = M') (hN : N = N')
    {P Q P' Q' : A} (a : M' ≅ I.obj P) (b : N' ≅ I.obj Q)
    (c : P ≅ P') (d : Q ≅ Q') (f : M ⟶ N) (g : P' ⟶ Q')
    (h : HEq f (a.hom ≫ I.map (c.hom ≫ g ≫ d.inv) ≫ b.inv)) :
    f ≫ (eqToIso hN ≪≫ b ≪≫ I.mapIso d).hom =
      (eqToIso hM ≪≫ a ≪≫ I.mapIso c).hom ≫ I.map g := by
  subst M'
  subst N'
  rw [eq_of_heq h]
  simp [Functor.map_comp, Category.assoc]

private theorem correction_square
    {C D : Type*} [Category C] [Category D] (I : C ⥤ D)
    {M N M' N' : D} (hM : M = M') (hN : N = N')
    {P Q P' Q' V : C} (s : M' ≅ I.obj P) (t : N' ≅ I.obj Q)
    (c : P ≅ P') (d : Q ≅ Q') (u : Q' ≅ V)
    (f : M ⟶ N) (a : P' ⟶ Q') (b : P' ⟶ V)
    (ha : a ≫ u.hom = b)
    (hf : f ≫ (eqToIso hN ≪≫ t ≪≫ I.mapIso d).hom =
      (eqToIso hM ≪≫ s ≪≫ I.mapIso c).hom ≫ I.map a)
    (α : I.obj V ≅ N)
    (hα : HEq α (eqToIso hN ≪≫ t ≪≫ I.mapIso (d ≪≫ u)).symm) :
    f ≫ α.inv = (eqToIso hM ≪≫ s ≪≫ I.mapIso c).hom ≫ I.map b := by
  rw [eq_of_heq hα]
  have hb : I.map a ≫ I.map u.hom = I.map b := by rw [← I.map_comp, ha]
  have h := congrArg (fun x ↦ x ≫ I.map u.hom) hf
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc] at h
  rw [hb] at h
  simpa only [Iso.symm_inv, Iso.trans_hom, Functor.mapIso_hom, Functor.map_comp,
    Category.assoc] using h

private theorem iso_comp_inclusion
    {J : Type*} [Preorder J] [IsDirectedOrder J] {C : J → Type*} [∀ j, Category (C j)]
    (S : StageSystem C) (A : S.PairCategory) (F : J) (h : A.stage ≤ F)
    (K : C F) (a : A.toStage h ⟶ K) :
    (S.isoToStage A h).hom ≫ (S.ι F).map a =
      StageSystem.PairCategory.mkHom (X := A) (Y := ⟨F, K⟩) F h (le_refl F)
        ((S.assoc h (le_refl F)).inv.app A.obj ≫
          (S.T (i := F) (j := F) (le_refl F)).map a) := by
  exact StageSystem.PairCategory.mkHom_comp_mkHom (S := S)
    (X := A) (Y := ⟨F, A.toStage h⟩) (Z := ⟨F, K⟩)
    (n := F) (hX := h) (hY := le_refl F) (hZ := le_refl F) _ _

private theorem assoc_unit_cancel
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : D ⥤ D) (a : F ⋙ G ≅ F) (e : G ≅ 𝟭 D)
    (hu : ∀ K, a.hom.app K = e.hom.app (F.obj K))
    (K : C) (L : D) (f : F.obj K ⟶ L) :
    a.inv.app K ≫ G.map f ≫ e.hom.app L = f := by
  rw [e.hom.naturality, ← Category.assoc, ← hu K]
  simpa only [Category.assoc, Functor.id_map] using Iso.inv_hom_id_app_assoc a K f

private theorem generic_tensor_to_stage
    {J : Type*} [Preorder J] [IsDirectedOrder J]
    {C : J → Type*} [∀ j, Category (C j)] (S : StageSystem C)
    (T : S.PairCategory × S.PairCategory ⥤ S.PairCategory)
    (A B M N : S.PairCategory) (F : J)
    (hA : A.stage ≤ F) (hB : B.stage ≤ F)
    (hM : M.stage ≤ F) (hN : N.stage ≤ F)
    (K L : C F) (a : A.toStage hA ⟶ K) (b : B.toStage hB ⟶ L)
    (R : C F × C F ⥤ C F)
    (c : M.toStage hM ≅ R.obj (A.toStage hA, B.toStage hB))
    (d : N.toStage hN ≅ R.obj
      ((S.T (i := F) (j := F) le_rfl).obj K,
        (S.T (i := F) (j := F) le_rfl).obj L))
    (e : S.T (i := F) (j := F) le_rfl ≅ 𝟭 (C F))
    (hm : T.obj (A, B) = M) (hn : T.obj (⟨F, K⟩, ⟨F, L⟩) = N)
    (ht : ∀ (a' : A.toStage hA ⟶ (S.T (i := F) (j := F) le_rfl).obj K)
      (b' : B.toStage hB ⟶ (S.T (i := F) (j := F) le_rfl).obj L),
      HEq (T.map (X := (A, B)) (Y := (⟨F, K⟩, ⟨F, L⟩))
        (Prod.mkHom (StageSystem.PairCategory.mkHom F hA le_rfl a')
          (StageSystem.PairCategory.mkHom F hB le_rfl b')))
        (StageSystem.PairCategory.mkHom (X := M) (Y := N) F hM hN
          (c.hom ≫ R.map (Prod.mkHom a' b') ≫ d.inv)))
    (hu : ∀ (E : J) (h : E ≤ F) (V : C E),
      (S.assoc h le_rfl).hom.app V = e.hom.app ((S.T h).obj V))
    (α : (S.ι F).obj (R.obj (K, L)) ≅ T.obj (⟨F, K⟩, ⟨F, L⟩))
    (hα : HEq α (eqToIso hn ≪≫ S.isoToStage N hN ≪≫
      (S.ι F).mapIso (d ≪≫ R.mapIso (Iso.prod (e.app K) (e.app L)))).symm) :
    T.map (Prod.mkHom ((S.isoToStage A hA).hom ≫ (S.ι F).map a)
      ((S.isoToStage B hB).hom ≫ (S.ι F).map b)) ≫ α.inv =
      (eqToIso hm ≪≫ S.isoToStage M hM ≪≫ (S.ι F).mapIso c).hom ≫
        (S.ι F).map (R.map (Prod.mkHom a b)) := by
  let I := S.ι F
  let a' := (S.assoc hA le_rfl).inv.app A.obj ≫ (S.T le_rfl).map a
  let b' := (S.assoc hB le_rfl).inv.app B.obj ≫ (S.T le_rfl).map b
  have ha := iso_comp_inclusion S A F hA K a
  have hb := iso_comp_inclusion S B F hB L b
  have hj := StageSystem.mkHom_eq_isoToStage hM hN
    (c.hom ≫ R.map (Prod.mkHom a' b') ≫ d.inv)
  have hm' := substitute_heq
    (fun q ↦ T.map (X := (A, B)) (Y := (⟨F, K⟩, ⟨F, L⟩)) q)
    (congrArg₂ (fun f g ↦ Prod.mkHom f g) ha hb) (ht a' b')
  have hsquare := model_square I hm hn (S.isoToStage M hM) (S.isoToStage N hN)
    c d _ _ (hm'.trans (heq_of_eq hj))
  have hunitA : a' ≫ e.hom.app K = a := by
    simpa only [a', Category.assoc] using
      assoc_unit_cancel (S.T hA) (S.T le_rfl) (S.assoc hA le_rfl) e
        (hu A.stage hA) A.obj K a
  have hunitB : b' ≫ e.hom.app L = b := by
    simpa only [b', Category.assoc] using
      assoc_unit_cancel (S.T hB) (S.T le_rfl) (S.assoc hB le_rfl) e
        (hu B.stage hB) B.obj L b
  have huMap : R.map (Prod.mkHom a' b') ≫
      R.map (Prod.mkHom (e.hom.app K) (e.hom.app L)) = R.map (Prod.mkHom a b) := by
    rw [← R.map_comp]
    simp only [CategoryTheory.prod_comp, hunitA, hunitB]
  exact correction_square I hm hn (S.isoToStage M hM) (S.isoToStage N hN)
    c d (R.mapIso (Iso.prod (e.app K) (e.app L))) _ _ _ huMap hsquare α hα

private theorem tensor_to_stage
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (A B : Pair l Ω X) (F : Index l Ω)
    (h : (commonStageTensorObject l Ω X A B).stage ≤ F)
    (K L : Stage l Ω X F)
    (a : A.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
      A.stage B.stage).1.trans h) ⟶ K)
    (b : B.toStage (((Padic.finiteCoefficientFields_properties l Ω).1
      A.stage B.stage).2.trans h) ⟶ L)
    (hu : ∀ (E : Index l Ω) (h : E ≤ F) (K : Stage l Ω X E),
      ((stageSystem l Ω X).assoc h le_rfl).hom.app K =
        (operationStageTransitionIso l Ω X F F le_rfl ≪≫ unitor l Ω X F).hom.app
          (((stageSystem l Ω X).T h).obj K)) :
    let I := inclusion (l := l) (Ω := Ω) (Y := X) F
    let hA := (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).1.trans h)
    let hB := (((Padic.finiteCoefficientFields_properties l Ω).1 A.stage B.stage).2.trans h)
    (commonStageDerivedTensor l Ω X).map (Prod.mkHom
      (((stageSystem l Ω X).isoToStage A hA).hom ≫ I.map a)
      (((stageSystem l Ω X).isoToStage B hB).hom ≫ I.map b)) ≫
        (AdicQbarRealization.stageTensor l X Ω F K L).inv =
      (eqToIso ((tensor_spec l Ω X).1 A B) ≪≫
        (stageSystem l Ω X).isoToStage (commonStageTensorObject l Ω X A B) h ≪≫
        I.mapIso (commonStageTensorComparison l Ω X A B F h)).hom ≫
          I.map ((rationalDerivedTensor l (Coefficient.{u} l Ω F) X).map
            (Prod.mkHom a b)) := by
  intro I hA hB
  let h' : (commonStageTensorObject l Ω X (I.obj K) (I.obj L)).stage ≤ F := by
    change F.val ⊔ F.val ≤ F.val
    exact sup_le le_rfl le_rfl
  exact generic_tensor_to_stage (stageSystem l Ω X) (commonStageDerivedTensor l Ω X)
    A B (commonStageTensorObject l Ω X A B)
    (commonStageTensorObject l Ω X (I.obj K) (I.obj L)) F hA hB h h' K L a b
    (rationalDerivedTensor l (Coefficient.{u} l Ω F) X)
    (commonStageTensorComparison l Ω X A B F h)
    (commonStageTensorComparison l Ω X (I.obj K) (I.obj L) F h')
    (operationStageTransitionIso l Ω X F F le_rfl ≪≫ unitor l Ω X F)
    ((tensor_spec l Ω X).1 A B) ((tensor_spec l Ω X).1 (I.obj K) (I.obj L))
    (fun a' b' ↦ (tensor_spec l Ω X).2 A B (I.obj K) (I.obj L) F h h' a' b')
    hu (AdicQbarRealization.stageTensor l X Ω F K L) (stage_tensor_formula l Ω X F K L)

set_option allowUnsafeReducibility true in
attribute [local reducible] GeneralAlgebraicallyClosedCoefficients.stageSystem

set_option allowUnsafeReducibility true in
attribute [local reducible] commonStageHomObject commonStageTensorObject

set_option maxHeartbeats 1000000 in
-- The final calculation elaborates the prescribed finite-stage identifications.
/-- The common-stage evaluation is the included rational evaluation under the
specified Hom, input, and output scalar identifications.

Source: BS Lemma 3.4.11 and Proposition 6.8.14; step 7 of the ambient comparison.
(blueprint: lem-sf-common-stage-evaluation-finite-square).

Proof: evaluation is inverse transposition of the identity of the common Hom.
Transport along the recorded literal Hom-object equality and represent that
identity at F. The Hom stage is the compositum of the entry stages, so F also
contains both entries and the tensor of the Hom with the first
entry. Apply PodCommonTransposeNormalization at F.
The inverse rational transpose of the identity is rational evaluation; its
naturality in the test object moves the specified rational Hom comparison to
the first tensor input. The normalization of stageTensor identifies the tensor
comparison with the inverse inclusion tensorator, including the normalized
reflexive scalar units in stageTensorFormula. Cancel adjacent inverse comparison
factors only after inserting those units. The isoToStage maps give the other
two entry identifications. Functoriality of the common-stage tensor,
using its representative formula at F, identifies the resulting representative
with the left side of the square. Thus the two arrows have equal representatives
at F; no faithfulness of the finite-stage inclusion is assumed. Identity
extensions, zero objects, and empty schemes use the same normalization. -/
theorem commonStageEvaluation_finiteSquare
    (l : ℕ) [Fact l.Prime] (Ω : Type v) [Field Ω]
    [Algebra (Padic l) Ω] [IsAlgClosure (Padic l) Ω] (X : Scheme.{u})
    [∀ x : X, Invertible (l : X.residueField x)]
    (S : PodPartialClosed (commonStageDerivedTensor l Ω X)
      (commonStageHomPairs l Ω X) (commonStageDerivedInternalHom l Ω X))
    (hS : PodCommonTransposeNormalization l Ω X S)
    (P : (commonStageHomPairs l Ω X).FullSubcategory)
    (F : AlgebraicallyClosedCoefficients.Index l Ω)
    (h : (commonStageHomObject l Ω X P).stage ≤ F) :
    let I := GeneralAlgebraicallyClosedCoefficients.inclusion (l := l) (Ω := Ω) (Y := X) F
    let Q := commonStageHomPairAtStage l Ω X P F h
    let γH := eqToIso (commonStageDerivedInternalHom_obj_eq l Ω X P)
      ≪≫ (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).isoToStage
        (commonStageHomObject l Ω X P) h ≪≫
      I.mapIso (commonStageHomComparison l Ω X P F h)
    let γM := (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).isoToStage
      P.obj.1.unop (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1.trans h)
    let γN := (GeneralAlgebraicallyClosedCoefficients.stageSystem l Ω X).isoToStage
      P.obj.2 (((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).2.trans h)
    (commonStageDerivedTensor l Ω X).map (Prod.mkHom γH.hom γM.hom) ≫
        (AdicQbarRealization.stageTensor l X Ω F
          ((rationalDerivedInternalHom l
            (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) X).obj Q)
          Q.obj.1.unop).inv ≫
        I.map ((podRationalClosed l
          (AlgebraicallyClosedCoefficients.Coefficient.{u} l Ω F) X).evaluation Q) =
      S.evaluation P ≫ γN.hom := by
  dsimp only
  let H := commonStageHomObject l Ω X P
  let hH : H.stage ≤ F := h
  have hT : (commonStageTensorObject l Ω X H P.obj.1.unop).stage ≤ F := by
    change H.stage.val ⊔ P.obj.1.unop.stage.val ≤ F.val
    apply sup_le
    · exact h
    · exact ((Padic.finiteCoefficientFields_properties l Ω).1
        P.obj.1.unop.stage P.obj.2.stage).1.trans h
  have hN : P.obj.2.stage ≤ F :=
    ((Padic.finiteCoefficientFields_properties l Ω).1
      P.obj.1.unop.stage P.obj.2.stage).2.trans h
  have hx := commonStageDerivedInternalHom_obj_eq l Ω X P
  have hi := (identity_transport hx).trans
    (heq_of_eq (StageSystem.PairCategory.id_eq_mkHom H hH))
  have he := (evaluation_transport S P H hx).trans
    (hS H P F hH hH hT hN (𝟙 _) (eqToHom hx.symm) hi)
  rw [Category.id_comp, partial_uncurry] at he
  let I := inclusion (l := l) (Ω := Ω) (Y := X) F
  let Q := commonStageHomPairAtStage l Ω X P F h
  let R := rationalDerivedTensor l (Coefficient.{u} l Ω F) X
  let cH := commonStageHomComparison l Ω X P F h
  let β := eqToIso ((tensor_spec l Ω X).1
      H P.obj.1.unop) ≪≫
    (stageSystem l Ω X).isoToStage (commonStageTensorObject l Ω X H P.obj.1.unop) hT ≪≫
    I.mapIso (commonStageTensorComparison l Ω X H P.obj.1.unop F hT)
  have htensor := tensor_to_stage l Ω X H P.obj.1.unop F hT
    ((rationalDerivedInternalHom l (Coefficient.{u} l Ω F) X).obj Q) Q.obj.1.unop
    cH.hom (𝟙 _) (fun E h K ↦ stage_right_unit l Ω X E F h K)
  dsimp only at htensor
  rw [I.map_id, Category.comp_id] at htensor
  have hv := transported_arrow (commonStageDerivedTensor l Ω X) hx
    ((tensor_spec l Ω X).1 H P.obj.1.unop)
    (S.evaluation P) _ he
  unfold GeneralAlgebraicallyClosedCoefficients.ofHom at hv
  rw [StageSystem.mkHom_eq_isoToStage hT hN] at hv
  have hev := congrArg
    (fun f ↦ f ≫ ((stageSystem l Ω X).isoToStage P.obj.2 hN).hom) hv
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hev
  have hcalc := congrArg
    (fun f ↦ (commonStageDerivedTensor l Ω X).map
      (Prod.mkHom (eqToHom hx) (𝟙 P.obj.1.unop)) ≫ f ≫
      I.map ((podRationalClosed l (Coefficient.{u} l Ω F) X).evaluation Q)) htensor
  trans (commonStageDerivedTensor l Ω X).map
      (Prod.mkHom (eqToHom hx) (𝟙 P.obj.1.unop)) ≫ β.hom ≫
    I.map (R.map (Prod.mkHom cH.hom (𝟙 _))) ≫
    I.map ((podRationalClosed l (Coefficient.{u} l Ω F) X).evaluation Q)
  · simpa only [β, I, R, cH, H, Q, Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom,
      Category.assoc, tensor_precomp, Functor.map_id, Category.comp_id] using hcalc
  · simpa only [β, Iso.trans_hom, eqToIso.hom, Functor.mapIso_hom,
      Category.assoc, ← I.map_comp] using hev

end FiniteSquareProof

namespace AdicQbarRealization.AmbientHomEvaluation.CoherenceCalculus

/-- Inverse transposition is tensoring with the map followed by evaluation. -/
lemma uncurry
    {C : Type*} [Category C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (X K M : C)
    (f : X ⟶ H.obj (op K, M)) :
    (S.transpose X K M).symm f =
      S.tensor.map (Prod.mkHom f (𝟙 K)) ≫ S.evaluation K M := by
  let := S.monoidal
  change ((S.adjunction K).homEquiv X M).symm f = _
  simp only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
    MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id]
  rfl

/-- Inverse transposition is natural in the test object. -/
lemma uncurry_precomp
    {C : Type*} [Category C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (X X' K M : C) (a : X' ⟶ X)
    (f : X ⟶ H.obj (op K, M)) :
    (S.transpose X' K M).symm (a ≫ f) =
      S.tensor.map (Prod.mkHom a (𝟙 K)) ≫ (S.transpose X K M).symm f := by
  rw [uncurry, uncurry]
  simp only [← Category.assoc, ← S.tensor.map_comp, CategoryTheory.prod_comp,
    Category.comp_id]

/-- Evaluation is natural in its contravariant and covariant entries. -/
lemma evaluation_pair
    {C : Type*} [Category C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (M M' N N' : C) (f : M' ⟶ M) (g : N ⟶ N') :
    S.tensor.map (Prod.mkHom (H.map (Prod.mkHom f.op g)) (𝟙 M')) ≫
        S.evaluation M' N' =
      S.tensor.map (Prod.mkHom (𝟙 (H.obj (op M, N))) f) ≫ S.evaluation M N ≫ g := by
  let := S.monoidal
  have hf := S.evaluation_naturality M M' N f
  have hg := (S.adjunction M').counit.naturality g
  have hp : H.map (Prod.mkHom f.op g) =
      H.map (Prod.mkHom f.op (𝟙 N)) ≫ H.map (Prod.mkHom (𝟙 (op M')) g) := by
    rw [← H.map_comp]
    simp only [CategoryTheory.prod_comp, Category.comp_id, Category.id_comp]
  rw [hp]
  simp only [CoefficientClosedStructure.tensor, CoefficientClosedStructure.evaluation,
    MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_tensorHom] at *
  rw [MonoidalCategory.comp_whiskerRight, Category.assoc]
  change MonoidalCategoryStruct.whiskerRight
    (H.map (Prod.mkHom (𝟙 (op M')) g)) M' ≫ (S.adjunction M').counit.app N' =
      (S.adjunction M').counit.app N ≫ g at hg
  change MonoidalCategoryStruct.whiskerRight
    (H.map (Prod.mkHom f.op (𝟙 N))) M' ≫ (S.adjunction M').counit.app N =
      MonoidalCategoryStruct.whiskerLeft (H.obj (op M, N)) f ≫
        (S.adjunction M).counit.app N at hf
  rw [hg, ← Category.assoc, hf, Category.assoc]

/-- Inverse transposition is natural in both entries of internal Hom. -/
lemma uncurry_postcomp
    {C : Type*} [Category C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (X M M' N N' : C)
    (a : X ⟶ H.obj (op M, N)) (f : M' ⟶ M) (g : N ⟶ N') :
    (S.transpose X M' N').symm (a ≫ H.map (Prod.mkHom f.op g)) =
      S.tensor.map (Prod.mkHom (𝟙 X) f) ≫ (S.transpose X M N).symm a ≫ g := by
  rw [uncurry, uncurry]
  have h := congrArg (fun k ↦ S.tensor.map (Prod.mkHom a (𝟙 M')) ≫ k)
    (evaluation_pair S M M' N N' f g)
  simpa only [← Functor.map_comp_assoc, ← Functor.map_comp, CategoryTheory.prod_comp,
    Category.comp_id, Category.id_comp, Category.assoc] using h

/-- Tensorator naturality carries a source evaluation square to its realization. -/
lemma realized_evaluation_square
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (T : C × C ⥤ C) (U : D × D ⥤ D)
    (μ : (F.prod F) ⋙ U ≅ T ⋙ F)
    {K M N K' M' N' V : C} (gK : K ≅ K') (gM : M ≅ M') (gN : N ≅ N')
    (e : T.obj (K, M) ⟶ N) (a : T.obj (K', M') ⟶ V) (b : V ⟶ N')
    (he : T.map (Prod.mkHom gK.hom gM.hom) ≫ a ≫ b = e ≫ gN.hom) :
    U.map (Prod.mkHom (F.mapIso gK).hom (F.mapIso gM).hom) ≫
        μ.hom.app (K', M') ≫ F.map a ≫ F.map b =
      (μ.hom.app (K, M) ≫ F.map e) ≫ (F.mapIso gN).hom := by
  have hn := μ.hom.naturality (Prod.mkHom gK.hom gM.hom)
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  simp only [Functor.mapIso_hom, Category.assoc]
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp, ← F.map_comp,
    he, F.map_comp]

/-- A tensorator symmetry equation remains valid after evaluation. -/
lemma realized_braiding_evaluation
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {A B N : C} {U V : D} (d : U ⟶ V) (μ : V ⟶ F.obj A) (ν : U ⟶ F.obj B)
    (b : B ⟶ A) (e : A ⟶ N) (h : d ≫ μ = ν ≫ F.map b) :
    d ≫ (μ ≫ F.map e) = ν ≫ F.map (b ≫ e) := by
  rw [← Category.assoc, h, Category.assoc, ← F.map_comp]

/-- An evaluation square gives the corresponding square between its transposes. -/
lemma comparison_square
    {C : Type*} [Category C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (U M N U' M' N' : C)
    (v : S.tensor.obj (U, M) ⟶ N) (v' : S.tensor.obj (U', M') ⟶ N')
    (gU : U ≅ U') (gM : M ≅ M') (gN : N ≅ N')
    (hv : S.tensor.map (Prod.mkHom gU.hom gM.hom) ≫ v' = v ≫ gN.hom) :
    gU.hom ≫ S.transpose _ _ _ v' =
      S.transpose _ _ _ v ≫ H.map (Prod.mkHom gM.inv.op gN.hom) := by
  apply (S.transpose _ _ _).symm.injective
  rw [uncurry_precomp, uncurry_postcomp,
    Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  have he := congrArg (fun k ↦ S.tensor.map (Prod.mkHom (𝟙 U) gM.inv) ≫ k) hv
  simpa only [← Functor.map_comp_assoc, CategoryTheory.prod_comp,
    Category.id_comp, Iso.inv_hom_id, Functor.map_id, Category.assoc] using he

/-- Braiding naturality converts right evaluation into left evaluation. -/
lemma braiding_evaluation
    {C : Type*} [Category C] {H : Cᵒᵖ × C ⥤ C}
    (S : CoefficientClosedStructure H) (B : @SymmetricCategory C _ S.monoidal)
    (K M N : C) (a : K ⟶ H.obj (op M, N)) (v : S.tensor.obj (K, M) ⟶ N)
    (hv : S.tensor.map (Prod.mkHom a (𝟙 M)) ≫ S.evaluation M N = v) :
    S.tensor.map (Prod.mkHom (𝟙 M) a) ≫ (B.braiding M (H.obj (op M, N))).hom ≫
        S.evaluation M N = (B.braiding M K).hom ≫ v := by
  let := S.monoidal
  let := B
  have hb : S.tensor.map (Prod.mkHom (𝟙 M) a) ≫
        (B.braiding M (H.obj (op M, N))).hom =
      (B.braiding M K).hom ≫ S.tensor.map (Prod.mkHom a (𝟙 M)) :=
    BraidedCategory.braiding_naturality (𝟙 M) a
  rw [← Category.assoc, hb, Category.assoc, hv]

/-- Two comparison squares give compatibility with conjugated transitions. -/
lemma comparison_extension
    {C : Type*} [Category C] (H : Cᵒᵖ × C ⥤ C)
    {U M N UF MF NF UG MG NG : C}
    (uF : U ≅ UF) (mF : M ≅ MF) (nF : N ≅ NF)
    (uG : U ≅ UG) (mG : M ≅ MG) (nG : N ≅ NG)
    (c : U ⟶ H.obj (op M, N)) (cF : UF ⟶ H.obj (op MF, NF))
    (cG : UG ⟶ H.obj (op MG, NG))
    (hF : uF.hom ≫ cF = c ≫ H.map (Prod.mkHom mF.inv.op nF.hom))
    (hG : uG.hom ≫ cG = c ≫ H.map (Prod.mkHom mG.inv.op nG.hom)) :
    (uF.inv ≫ uG.hom) ≫ cG =
      cF ≫ H.map (Prod.mkHom (mG.inv ≫ mF.hom).op (nF.inv ≫ nG.hom)) := by
  apply (cancel_epi uF.hom).mp
  simp only [Iso.hom_inv_id_assoc, Category.assoc]
  rw [hG, ← Category.assoc, hF, Category.assoc]
  congr 1
  simp only [← Functor.map_comp, CategoryTheory.prod_comp, ← op_comp, Category.assoc,
    Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]

/-- Bifunctoriality and inverse cancellation give the ambient transition tower. -/
lemma ambient_transition_tower
    {C : Type*} [Category C] (H : Cᵒᵖ × C ⥤ C)
    {M N MF NF MG NG MK NK : C}
    (mF : M ≅ MF) (nF : N ≅ NF) (mG : M ≅ MG) (nG : N ≅ NG)
    (mK : M ≅ MK) (nK : N ≅ NK) :
    H.map (Prod.mkHom (mG.inv ≫ mF.hom).op (nF.inv ≫ nG.hom)) ≫
        H.map (Prod.mkHom (mK.inv ≫ mG.hom).op (nG.inv ≫ nK.hom)) =
      H.map (Prod.mkHom (mK.inv ≫ mF.hom).op (nF.inv ≫ nK.hom)) := by
  simp only [← Functor.map_comp, CategoryTheory.prod_comp, ← op_comp, Category.assoc,
    Iso.hom_inv_id_assoc]

end AdicQbarRealization.AmbientHomEvaluation.CoherenceCalculus

end WeilConjectures
