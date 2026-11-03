/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedPullbackTensorComparison
public import WeilConjectures.TraceFormula.Integral.IntegralPullbackComposition
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorConstraintCore

import all WeilConjectures.SmoothPurity.Pullback.PullbackTensorReductionCalculus
import WeilConjectures.SmoothPurity.Integral.IntegralSystemReductionFullyFaithful
import WeilConjectures.SmoothPurity.CompletedOperations.NormalizedCompletedOperationModels
import WeilConjectures.SmoothPurity.Pur.PurNormalizedReconstructionAdjunctionCalculus
import WeilConjectures.SmoothPurity.Supporting.Coefficient.ConstantCoefficientObjectsConstructible
import WeilConjectures.SmoothPurity.Sf.SfDerivedCompleteLegacyComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Bounded.ProEtaleBoundedConstructibleTriangulated
import all WeilConjectures.SmoothPurity.Rational.RationalTensorStageCoherence
import WeilConjectures.CategoryTheory.StageSystem.IsoOfTransport
import WeilConjectures.SmoothPurity.Integral.IntegralUnitScalarExtension

/-! # Normalized higher pullback tensor constraints

The unchanged constructions and structural predicates from the parent module.
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

private theorem coefficientPrime_isUnit (l : ℕ) (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] : IsUnit (l : Γ(W, ⊤)) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply RingedSpace.isUnit_of_isUnit_germ W.toSheafedSpace ⊤
    intro x hx
    apply (IsLocalRing.residue_ne_zero_iff_isUnit _).mp
    simpa only [map_natCast] using
      (isUnit_of_invertible (l : W.residueField x)).ne_zero

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

private theorem existsUnique_iso_of_eq {C : Type*} [Category* C]
    {A B A' B' : C} (hA : A = A') (hB : B = B') (e : A' ≅ B') :
    ∃! d : A ≅ B, HEq d.hom e.hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    subst A'
    subst B'
    exact ⟨e, HEq.rfl, fun d hd ↦ Iso.ext (eq_of_heq hd)⟩

private theorem existsUnique_iso_of_map {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {A B : C} (e : F.obj A ≅ F.obj B) :
    ∃! d : A ≅ B, F.map d.hom = e.hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    refine ⟨F.preimageIso e, F.map_preimage _, ?_⟩
    intro d hd
    exact Iso.ext (F.map_injective (hd.trans (F.map_preimage e.hom).symm))

private theorem existsUnique_iso_of_map_comp {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) [F.Full] [F.Faithful] {A B : C} {T : D}
    (a : F.obj A ≅ T) (b : F.obj B ≅ T) :
    ∃! d : A ≅ B, F.map d.hom ≫ b.hom = a.hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    obtain ⟨d, hd, hu⟩ := existsUnique_iso_of_map F (a ≪≫ b.symm)
    refine ⟨d, ?_, ?_⟩
    · change F.map d.hom ≫ b.hom = a.hom
      rw [hd]
      simp
    · intro e he
      apply hu
      exact (Iso.eq_comp_inv b).mpr he

private theorem existsUnique_iso_of_map_constraints {C D : Type*} [Category* C]
    [Category* D] (F : C ⥤ D) [F.Full] [F.Faithful]
    {A B : C} {U V W T : D}
    (a₁ : F.obj A ≅ U) (a₂ : U ≅ V) (a₃ : V ≅ T)
    (b₁ : F.obj B ≅ W) (b₂ : W ≅ T) :
    ∃! d : A ≅ B, F.map d.hom ≫ b₁.hom ≫ b₂.hom =
      a₁.hom ≫ a₂.hom ≫ a₃.hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    simpa only [Iso.trans_hom, Category.assoc] using
      existsUnique_iso_of_map_comp F (a₁ ≪≫ a₂ ≪≫ a₃) (b₁ ≪≫ b₂)

private theorem existsUnique_iso_of_map_constraint {C D : Type*} [Category* C]
    [Category* D] (F : C ⥤ D) [F.Full] [F.Faithful]
    {A B : C} {U T : D} (a₁ : F.obj A ≅ U) (a₂ : U ≅ T) (b : F.obj B ≅ T) :
    ∃! d : A ≅ B, F.map d.hom ≫ b.hom = a₁.hom ≫ a₂.hom := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    exact existsUnique_iso_of_map_comp F (a₁ ≪≫ a₂) b

private def closedTensorUnitIso {D : Type*} [Category* D]
    {H : Dᵒᵖ × D ⥤ D} (S T : CoefficientClosedStructure H) :
    S.monoidal.tensorUnit ≅ T.monoidal.tensorUnit :=
  (T.monoidal.rightUnitor S.monoidal.tensorUnit).symm ≪≫
    ((T.adjunction T.monoidal.tensorUnit).leftAdjointUniq
      (S.adjunction T.monoidal.tensorUnit)).app S.monoidal.tensorUnit ≪≫
    S.monoidal.leftUnitor T.monoidal.tensorUnit

private theorem map_localized_heq
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    (F : C ⥤ D) (F' : C' ⥤ D') (Q : C ⥤ C') (R : D ⥤ D')
    (hF : ∀ {A B : C} (f : A ⟶ B), HEq (F'.map (Q.map f)) (R.map (F.map f)))
    {A B : C'} {A' B' : C} (hA : A = Q.obj A') (hB : B = Q.obj B')
    (f : A ⟶ B) (g : A' ⟶ B') (hfg : HEq f (Q.map g)) :
    HEq (F'.map f) (R.map (F.map g)) := by
  subst A B
  cases hfg
  exact hF g

section CoherentReductionCache
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def coherentReduction (W : Scheme.{u}) :
    sfIntegralConstructibleCategory l E W ⥤ coefficientSequenceDerived l E W :=
  (sfIntegralConstructible l E W).ι ⋙ (pullbackTensorCalculus l E W).reduction
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coherentReduction_fullyFaithful (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    (coherentReduction l E W).Full ∧ (coherentReduction l E W).Faithful := by
  simpa only [coherentReduction, integralSystemReduction, pullbackTensorCalculus] using
    integralSystemReduction_fullyFaithful l E W
end CoherentReductionCache

section HigherCoherence
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
variable (Ω : Type v) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem integralComparison_reduction {X Y : Scheme.{u}} (f : X ⟶ Y)
    [hX : ∀ x : X, Invertible (l : X.residueField x)]
    [hY : ∀ y : Y, Invertible (l : Y.residueField y)]
    (M N : sfIntegralConstructibleCategory l E Y) :
    canonicalIntegralPullbackTensor_reduction l E f M N := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let := ((pullbackTensorComparisonCounits l E f) M N).1
    let := ((pullbackTensorComparisonCounits l E f) M N).2.1
    let := ((pullbackTensorComparisonCounits l E f) M N).2.2
    have hh := reduction_comparison
      (pullbackTensorCalculus l E X).reduction (coefficientSequenceLimit l E X)
      (pullbackTensorCalculus l E X).adjunction
      (pullbackTensorCalculus l E Y).reduction (coefficientSequenceLimit l E Y)
      (pullbackTensorCalculus l E Y).adjunction
      (integralDerivedPullback l E f) (pullbackTensorSequenceDerived l E f)
      (integralCompletedTensor l E Y) (integralCompletedTensor l E X)
      (pullbackTensorCalculus l E Y).systemClosed.tensor
      (pullbackTensorCalculus l E X).systemClosed.tensor
      (pullbackTensorIntegralPullbackModel l E f)
      (pullbackTensorIntegralTensorModel l E Y)
      (pullbackTensorIntegralTensorModel l E X)
      (pullbackTensorSystemComparison l E f) M.obj N.obj
    unfold canonicalIntegralPullbackTensor_reduction
    dsimp only [canonicalIntegralPullbackTensor, ObjectProperty.isoMk,
      ObjectProperty.homMk, pullbackTensorIntegralReductionTensor,
      pullbackTensorIntegralReductionPullback, pullbackTensorReferenceComparison,
      Iso.trans_hom, Functor.mapIso_hom, asIso_hom, asIso_inv, Iso.symm_hom,
      Iso.app_hom, Iso.app_inv, Iso.prod_hom, Functor.prod_map, Functor.comp_map,
      pullbackTensorReferencePullback, pullbackTensorReferenceTensor,
      constructibleIntegralPullback, constructibleIntegralTensor,
      ObjectProperty.lift, ObjectProperty.ι_obj, Functor.comp_obj, Functor.prod_obj,
      Functor.id_obj]
    simpa only [Functor.map_comp, Category.assoc, Iso.prod_hom, Iso.symm_hom,
      Iso.app_inv, asIso_inv, Functor.comp_map, Functor.prod_map, Functor.id_obj] using hh

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def reduction_tensor (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    constructibleIntegralTensor l E W ⋙ coherentReduction l E W ≅
      (coherentReduction l E W).prod (coherentReduction l E W) ⋙
        (pullbackTensorCalculus l E W).systemClosed.tensor :=
  NatIso.ofComponents (fun MN ↦ pullbackTensorIntegralReductionTensor l E W MN.1 MN.2) (by
    intro MN PQ k
    dsimp only [pullbackTensorIntegralReductionTensor, Iso.trans_hom,
      Functor.mapIso_hom, asIso_hom]
    simpa only [Category.assoc, Iso.app_hom, coherentReduction,
      constructibleIntegralTensor, ObjectProperty.lift, Functor.comp_map,
      Functor.comp_obj, Functor.id_obj, ObjectProperty.ι_obj, ObjectProperty.ι_map,
      ObjectProperty.homMk, Functor.prod_map, Functor.prod_obj, pullbackTensorCalculus] using
      counit_model_naturality
        (pullbackTensorCalculus l E W).reduction (coefficientSequenceLimit l E W)
        (pullbackTensorCalculus l E W).adjunction (integralCompletedTensor l E W)
        (((pullbackTensorCalculus l E W).reduction.prod
          (pullbackTensorCalculus l E W).reduction) ⋙
          (pullbackTensorCalculus l E W).systemClosed.tensor)
        (pullbackTensorIntegralTensorModel l E W) (Prod.mkHom k.1.hom k.2.hom))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private def reduction_pullback {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)] :
    constructibleIntegralPullback l E f ⋙ coherentReduction l E X ≅
      coherentReduction l E Y ⋙ pullbackTensorSequenceDerived l E f :=
  NatIso.ofComponents (pullbackTensorIntegralReductionPullback l E f) (by
    intro M N k
    dsimp only [pullbackTensorIntegralReductionPullback, Iso.trans_hom,
      Functor.mapIso_hom, asIso_hom]
    simpa only [Category.assoc, Iso.app_hom, coherentReduction,
      constructibleIntegralPullback, ObjectProperty.lift, Functor.comp_map,
      Functor.comp_obj, Functor.id_obj, ObjectProperty.ι_obj, ObjectProperty.ι_map,
      ObjectProperty.homMk, pullbackTensorCalculus] using counit_model_naturality
      (pullbackTensorCalculus l E X).reduction (coefficientSequenceLimit l E X)
      (pullbackTensorCalculus l E X).adjunction (integralDerivedPullback l E f)
      ((pullbackTensorCalculus l E Y).reduction ⋙ pullbackTensorSequenceDerived l E f)
      (pullbackTensorIntegralPullbackModel l E f) k.hom)

private theorem reducedBraiding_natural
    {C D : Type*} [Category* C] [Category* D] (Q : C ⥤ D) [Q.Faithful]
    (T : C × C ⥤ C) (S : D × D ⥤ D)
    (b : T ⋙ Q ≅ (Q.prod Q) ⋙ S)
    (β : ∀ A B, S.obj (A, B) ⟶ S.obj (B, A))
    (hβ : ∀ A A' B B' (f : A ⟶ A') (g : B ⟶ B'),
      S.map (Prod.mkHom f g) ≫ β A' B' = β A B ≫ S.map (Prod.mkHom g f))
    (bi : ∀ A B, T.obj (A, B) ⟶ T.obj (B, A))
    (hb : ∀ A B, Q.map (bi A B) ≫ b.hom.app (B, A) =
      b.hom.app (A, B) ≫ β (Q.obj A) (Q.obj B))
    (M M' N N' : C) (f : M ⟶ M') (g : N ⟶ N') :
    T.map (Prod.mkHom f g) ≫ bi M' N' = bi M N ≫ T.map (Prod.mkHom g f) := by
  have hn := b.hom.naturality (Prod.mkHom f g)
  have hn' := b.hom.naturality (Prod.mkHom g f)
  change Q.map (T.map (Prod.mkHom f g)) ≫ b.hom.app (M', N') =
    b.hom.app (M, N) ≫ S.map (Prod.mkHom (Q.map f) (Q.map g)) at hn
  change Q.map (T.map (Prod.mkHom g f)) ≫ b.hom.app (N', M') =
    b.hom.app (N, M) ≫ S.map (Prod.mkHom (Q.map g) (Q.map f)) at hn'
  apply Q.map_injective
  apply (cancel_mono (b.hom.app (N', M'))).1
  simp only [Functor.map_comp, Category.assoc]
  rw [hb, ← Category.assoc, hn]
  simp only [Category.assoc]
  rw [hβ, hn']
  simpa only [Category.assoc] using congrArg
    (fun z ↦ z ≫ S.map (Prod.mkHom (Q.map g) (Q.map f))) (hb M N).symm

private theorem representative_braiding
    {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) (T : C × C ⥤ C) (S : D × D ⥤ D)
    (β : ∀ M N, T.obj (M, N) ≅ T.obj (N, M))
    (γ : ∀ P Q, S.obj (P, Q) ≅ S.obj (Q, P))
    (μ : ∀ M N, F.obj (T.obj (M, N)) ≅ S.obj (F.obj M, F.obj N))
    (hc : ∀ M N, F.map (β M N).hom ≫ (μ N M).hom =
      (μ M N).hom ≫ (γ (F.obj M) (F.obj N)).hom)
    (hn : ∀ P P' Q Q' (f : P ⟶ P') (g : Q ⟶ Q'),
      S.map (Prod.mkHom f g) ≫ (γ P' Q').hom =
        (γ P Q).hom ≫ S.map (Prod.mkHom g f))
    (M N : C) {A B : C} {U V P Q X Y : D}
    (a : A ≅ T.obj (M, N)) (b : B ≅ T.obj (N, M))
    (u : U ≅ F.obj A) (v : V ≅ F.obj B)
    (p : P ≅ F.obj M) (q : Q ≅ F.obj N)
    (x : X ≅ S.obj (P, Q)) (y : Y ≅ S.obj (Q, P)) :
    (u.hom ≫ F.map (a.hom ≫ (β M N).hom ≫ b.inv) ≫ v.inv) ≫
      (v.hom ≫ F.map b.hom ≫ (μ N M).hom ≫
        S.map (Prod.mkHom q.inv p.inv) ≫ y.inv) =
    (u.hom ≫ F.map a.hom ≫ (μ M N).hom ≫
      S.map (Prod.mkHom p.inv q.inv) ≫ x.inv) ≫
      (x.hom ≫ (γ P Q).hom ≫ y.inv) := by
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc,
    Iso.map_inv_hom_id_assoc]
  rw [reassoc_of% (hc M N), ← reassoc_of% (hn _ _ _ _ p.inv q.inv)]

private theorem localizedBraiding_natural
    {R : Type*} [CommRing R] {A : Type*} [Category* A] [Preadditive A] [Linear R A]
    (p : R) (T : A × A ⥤ A) (bi : ∀ M N, T.obj (M, N) ≅ T.obj (N, M))
    (hn : ∀ M M' N N' (f : M ⟶ M') (g : N ⟶ N'),
      T.map (Prod.mkHom f g) ≫ (bi M' N').hom =
        (bi M N).hom ≫ T.map (Prod.mkHom g f))
    (F : ScalarLocalization R A p × ScalarLocalization R A p ⥤ ScalarLocalization R A p)
    (br : ∀ M N, F.obj (M, N) ≅ F.obj (N, M))
    (ho : ∀ MN, F.obj MN = ⟨T.obj (MN.1.obj, MN.2.obj)⟩)
    (hm : ∀ M M' N N', ∃ b : (M ⟶ M') →ₗ[Localization.Away p]
        (N ⟶ N') →ₗ[Localization.Away p] (F.obj (M, N) ⟶ F.obj (M', N')),
      (∀ f g, F.map (Prod.mkHom f g) = b f g) ∧
      ∀ (f : M.obj ⟶ M'.obj) (g : N.obj ⟶ N'.obj) (a b' : Localization.Away p),
        HEq (b (a ⊗ₜ[R] f) (b' ⊗ₜ[R] g))
          ((a * b') ⊗ₜ[R] T.map (Prod.mkHom f g)))
    (hb : ∀ M N, HEq (br M N).hom
      ((ScalarLocalization.localization R A p).map (bi M.obj N.obj).hom)) :
    ∀ M M' N N' (f : M ⟶ M') (g : N ⟶ N'),
      F.map (Prod.mkHom f g) ≫ (br M' N').hom =
        (br M N).hom ≫ F.map (Prod.mkHom g f) := by
  intro M M' N N' f g
  obtain ⟨b, he, hp⟩ := hm M M' N N'
  obtain ⟨b', he', hp'⟩ := hm N N' M M'
  rw [he, he']
  have ht (a : Localization.Away p) (f : M.obj ⟶ M'.obj)
      (c : Localization.Away p) (g : N.obj ⟶ N'.obj) :
      b (a ⊗ₜ[R] f) (c ⊗ₜ[R] g) ≫ (br M' N').hom =
        (br M N).hom ≫ b' (c ⊗ₜ[R] g) (a ⊗ₜ[R] f) := by
    have hl := heq_comp (ho (M, N)) (ho (M', N')) (ho (N', M'))
      (hp f g a c) (hb M' N')
    have hr := heq_comp (ho (M, N)) (ho (N, M)) (ho (N', M'))
      (hb M N) (hp' g f c a)
    apply eq_of_heq
    refine hl.trans ((heq_of_eq ?_).trans hr.symm)
    change ScalarLocalization.composition R A p _ _ _
        (1 ⊗ₜ[R] (bi M'.obj N'.obj).hom)
        ((a * c) ⊗ₜ[R] T.map (Prod.mkHom f g)) =
      ScalarLocalization.composition R A p _ _ _
        ((c * a) ⊗ₜ[R] T.map (Prod.mkHom g f))
        (1 ⊗ₜ[R] (bi M.obj N.obj).hom)
    rw [ScalarLocalization.composition_tmul, ScalarLocalization.composition_tmul,
      one_mul, mul_one, mul_comm c a, hn]
  induction f using TensorProduct.induction_on with
  | zero => simp only [map_zero, LinearMap.zero_apply, Limits.zero_comp,
      Limits.comp_zero]
  | tmul a f =>
    induction g using TensorProduct.induction_on with
    | zero => simp only [map_zero, LinearMap.zero_apply, Limits.zero_comp,
        Limits.comp_zero]
    | tmul c g => exact ht a f c g
    | add g g' hg hg' =>
      simp only [map_add, LinearMap.add_apply, Preadditive.add_comp,
        Preadditive.comp_add, hg, hg']
  | add f f' hf hf' =>
    simp only [map_add, LinearMap.add_apply, Preadditive.add_comp,
      Preadditive.comp_add, hf, hf']

attribute [local irreducible] pullbackTensorIntegralComposition
  pullbackTensorIntegralReductionTensor pullbackTensorIntegralReductionPullback
  pullbackTensorCommonLeft pullbackTensorCommonRight pullbackTensorCommonAssociator

private theorem normalizedCoefficientSequence_of_iso (W : Scheme.{u})
    {A B : coefficientSequenceDerived l E W} (e : B ≅ A)
    (hA : IsNormalizedCoefficientSequence l E W A) :
    IsNormalizedCoefficientSequence l E W B := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    intro m n h P
    let en := (coefficientSequenceDerivedEvaluation l E W n).mapIso e
    let em := (coefficientSequenceDerivedEvaluation l E W m).mapIso e
    let R := normalizedDVRRes l E W h
    have ht := (coefficientSequenceDerivedTransition l E W h).naturality e.hom
    change em.hom ≫ _ = _ ≫ R.map en.hom at ht
    have hti := (coefficientSequenceDerivedTransition l E W h).naturality e.inv
    change em.inv ≫ _ = _ ≫ R.map en.inv at hti
    constructor
    · intro f g hfg
      apply (cancel_epi en.inv).mp
      apply (hA h P).injective
      change _ ≫ R.map (en.inv ≫ f) = _ ≫ R.map (en.inv ≫ g)
      have hh (k : (coefficientSequenceDerivedEvaluation l E W n).obj B ⟶ P) :
          (coefficientSequenceDerivedTransition l E W h).app A ≫ R.map (en.inv ≫ k) =
            em.inv ≫ (coefficientSequenceDerivedTransition l E W h).app B ≫ R.map k := by
        rw [Functor.map_comp, ← Category.assoc, ← hti, Category.assoc]
      rw [hh, hh]
      exact congrArg (fun k ↦ em.inv ≫ k) hfg
    · intro a
      obtain ⟨b, hb⟩ := (hA h P).surjective (em.inv ≫ a)
      refine ⟨en.hom ≫ b, ?_⟩
      change _ ≫ R.map (en.hom ≫ b) = a
      change _ ≫ R.map b = em.inv ≫ a at hb
      rw [Functor.map_comp, ← Category.assoc, ← ht, Category.assoc, hb]
      simp

private theorem pullbackTensorSystemUnit_normalized (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] :
    IsNormalizedCoefficientSequence l E W
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    obtain ⟨M, hM⟩ := CompletedOperations.normalizedCompletedOperationModels l E
      (fun _ : Unit ↦ W) (fun _ x ↦ isUnit_of_invertible (l : W.residueField x))
    let e : (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit ≅
        CompletedOperations.unit l E (W := fun _ : Unit ↦ W) () :=
      closedTensorUnitIso
        ((coefficientDerivedSystemEvaluationCalculus l E W).choose).systemClosed
        (M.system ()).closed ≪≫
        (M.system ()).unitIso
    intro m n h P
    exact normalizedCoefficientSequence_of_iso l E W e
      (fun {m n} h P ↦ hM.unit () h P) h P

private def pushUnitIso {C D : Type*} [Category* C] [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    (F : C ⥤ D) [F.IsContinuous J K] (R : Sheaf K RingCat.{r})
    {S : Sheaf J RingCat.{r}}
    (h : (F.sheafPushforwardContinuous RingCat.{r} J K).obj R = S) :
    (SheafOfModules.pushforward (F := F) (eqToHom h.symm)).obj
      (SheafOfModules.unit R) ≅ SheafOfModules.unit S := by
  subst S
  exact Iso.refl _

private def evaluationUnitIso (W : Scheme.{u}) (n : ℕ) :
    (coefficientSequenceEvaluation l E W n).obj
      (SheafOfModules.unit
        ((sheafCompose (coefficientSequenceTopology (Scheme.ProEt.topology W))
          (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            (coefficientSequenceCommRingSheaf l E W))) ≅
      SheafOfModules.unit (integralCoefficientSheaf l E W n) :=
  pushUnitIso (Prod.sectR n W.ProEt) _ (coefficientSequenceEvaluationRing_eq l E W n)

private theorem systemUnitEvaluationIso (W : Scheme.{u})
    [∀ w : W, Invertible (l : W.residueField w)] (n : ℕ) :
    Nonempty ((coefficientSequenceDerivedEvaluation l E W n).obj
      ((coefficientDerivedSystemEvaluationCalculus l E W).choose).systemClosed.monoidal.tensorUnit ≅
      finiteConstantCoefficientObject l E W n) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    obtain ⟨M, hM⟩ := CompletedOperations.normalizedCompletedOperationModels l E
      (fun _ : Unit ↦ W) (fun _ x ↦ isUnit_of_invertible (l : W.residueField x))
    let e := closedTensorUnitIso
      ((coefficientDerivedSystemEvaluationCalculus l E W).choose).systemClosed
      (M.system ()).closed ≪≫ (M.system ()).unitIso
    exact ⟨(coefficientSequenceDerivedEvaluation l E W n).mapIso e ≪≫
      ((coefficientSequenceEvaluation l E W n).mapDerivedCategorySingleFunctor 0).app _ ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso (evaluationUnitIso l E W n)⟩

/-- The limit of the coherent ring unit is constructible and complete.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: The coherent ring unit is the
constant
  rank-one finite coefficient tower. Its quotient transitions are normalized. Normalized DVR
  effectivity computes its limit as the completed rank-one coefficient module, whose reductions are
  the finite constructible ring units; these have uniform amplitude zero. -/
theorem pullbackTensorIntegralUnit_constructible (W : Scheme.{u})
    [_hW : ∀ w : W, Invertible (l : W.residueField w)] :
    sfIntegralConstructible l E W ((coefficientSequenceLimit l E W).obj
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    let S := (coefficientDerivedSystemEvaluationCalculus l E W).choose
    let U := S.systemClosed.monoidal.tensorUnit
    let K := (coefficientSequenceLimit l E W).obj U
    have hl := coefficientPrime_isUnit l W
    have hn : IsNormalizedCoefficientSequence l E W U :=
      fun {m n} h P ↦ pullbackTensorSystemUnit_normalized l E W h P
    obtain ⟨hcomplete, hcounit⟩ := (purNormalizedReconstruction l E W hl S).1 U hn
    obtain ⟨D, hlp, hD⟩ := hcomplete
    refine ⟨(sfDerivedComplete_iff_legacy l E W D hlp K).mpr hD,
      0, 0, le_refl _, ?_⟩
    intro n
    let := hcounit
    obtain ⟨en⟩ := systemUnitEvaluationIso l E W n
    let e : (scalarReductionDerivedExtension l E W n).obj K ≅
        finiteConstantCoefficientObject l E W n :=
      (S.reductionEvaluation n).symm.app K ≪≫
        (coefficientSequenceDerivedEvaluation l E W n).mapIso
          (asIso (S.adjunction.counit.app U)) ≪≫ en
    let := Padic.finite_coefficientExtensionRing l E (n + 1) (Nat.succ_pos n)
    have : ObjectProperty.IsClosedUnderIsomorphisms
        (intrinsicFiniteTorsionConstructible l E (n + 1)
          (Nat.succ_le_succ (Nat.zero_le n)) W) :=
      (AlgebraicGeometry.Scheme.proEtale_bounded_constructible_isTriangulated W
        (Padic.coefficientExtensionRing l E (n + 1))).1
    refine ⟨ObjectProperty.prop_of_iso _ e.symm
      (finiteConstantCoefficient_constructible l E W n).1, ?_⟩
    intro i hi
    have hi' : i ∈ proEtaleCohomologicalSupport
        (finiteConstantCoefficientObject l E W n) := by
      intro hz
      exact hi (((DerivedCategory.homologyFunctor _ i).mapIso e).isZero_iff.mpr hz)
    have he : i = 0 := by
      by_contra h
      apply hi'
      unfold finiteConstantCoefficientObject
      rcases lt_or_gt_of_ne h with h | h
      · exact DerivedCategory.isZero_of_isGE _ 0 i h
      · exact DerivedCategory.isZero_of_isLE _ 0 i h
    simp [he]

/-- The actual derived limit of the coherent coefficient-ring unit.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorIntegralUnit (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] : sfIntegralConstructibleCategory l E W :=
  ⟨_, @pullbackTensorIntegralUnit_constructible l _ E _ _ _ W hW⟩

/-- The reduction counit of the normalized coefficient-ring unit is invertible.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: The finite ring units and their
quotient
  tensor comparisons form a normalized system. Apply normalized DVR effectivity to this system. The
  reconstruction isomorphism is precisely the reduction/limit adjunction counit. -/
theorem pullbackTensorIntegralUnit_counit (W : Scheme.{u})
    [_hW : ∀ w : W, Invertible (l : W.residueField w)] : IsIso ((pullbackTensorCalculus l E
      W).adjunction.counit.app
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have hl := coefficientPrime_isUnit l W
    exact ((purNormalizedReconstruction l E W hl
      (coefficientDerivedSystemEvaluationCalculus l E W).choose).1 _
        (fun {m n} h P ↦ pullbackTensorSystemUnit_normalized l E W h P)).2

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The fixed identification of the reduced integral unit with the coherent ring unit.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorIntegralUnitReduction (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :
    (pullbackTensorCalculus l E W).reduction.obj ((@pullbackTensorIntegralUnit l _ E _ _ _ W
      hW)).obj ≅
      (pullbackTensorCalculus l E W).systemClosed.monoidal.tensorUnit :=
  letI := (@pullbackTensorIntegralUnit_counit l _ E _ _ _ W hW)
  asIso ((pullbackTensorCalculus l E W).adjunction.counit.app _)

/-- The rational unit is the localization of the completed coefficient-ring unit.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorRationalUnit (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :=
  (sfRationalConstructibleLocalization l E W).obj ((@pullbackTensorIntegralUnit l _ E _ _ _ W hW))

attribute [local irreducible] pullbackTensorIntegralUnitReduction

-- Keep the category instances folded after constructing the unit evaluation map.
set_option allowUnsafeReducibility true in
attribute [local irreducible] instCategoryDerivedCategory DerivedCategory.instPreadditive
  SheafOfModules.instAbelian SheafOfModules.instCategory

/-- The integral left unitor is fixed by coherent reduction.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Conjugate the coherent unitor by
the actual
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
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have := (coherentReduction_fullyFaithful l E W).1
    have := (coherentReduction_fullyFaithful l E W).2
    let target : (coherentReduction l E W).obj
        ((constructibleIntegralTensor l E W).obj (pullbackTensorIntegralUnit l E W,M)) ≅
        (coherentReduction l E W).obj M :=
      pullbackTensorIntegralReductionTensor l E W (pullbackTensorIntegralUnit l E W) M ≪≫
        (pullbackTensorCalculus l E W).systemClosed.tensor.mapIso
          (Iso.prod (pullbackTensorIntegralUnitReduction l E W) (Iso.refl _)) ≪≫
        (pullbackTensorCalculus l E W).systemClosed.monoidal.leftUnitor _
    obtain ⟨d, hd, hu⟩ := existsUnique_iso_of_map (coherentReduction l E W) target
    refine ⟨d, ?_, ?_⟩
    · change (coherentReduction l E W).map
        d.hom = _
      rw [hd]
      rfl
    · intro d' hd'
      apply hu
      exact hd'

/-- The normalized completed left unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorIntegralLeftUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W) :=
  ((@pullbackTensorIntegralLeftUnitor_existsUnique l _ E _ _ _ W hW) M).exists.choose

/-- The rational left unitor is the localized completed one.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Use the prescribed rational
tensor object
  equality and localize the integral unitor and its inverse. The displayed hom equality uniquely
  determines the iso. -/
theorem pullbackTensorRationalLeftUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj ((@pullbackTensorRationalUnit l _ E _ _ _
      W hW),M) ≅ M,
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralLeftUnitor l _ E _ _ _ W hW) M.obj).hom) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply existsUnique_iso_of_eq
      ((rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1
        (pullbackTensorRationalUnit l E W,M)) rfl
      ((sfRationalConstructibleLocalization l E W).mapIso
        (pullbackTensorIntegralLeftUnitor l E W M.obj))

/-- The localized completed left unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorRationalLeftUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :=
  ((@pullbackTensorRationalLeftUnitor_existsUnique l _ E _ _ _ W hW) M).exists.choose

/-- The integral right unitor is fixed by coherent reduction.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Conjugate the coherent unitor by
the actual
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
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have := (coherentReduction_fullyFaithful l E W).1
    have := (coherentReduction_fullyFaithful l E W).2
    let target : (coherentReduction l E W).obj
        ((constructibleIntegralTensor l E W).obj (M,pullbackTensorIntegralUnit l E W)) ≅
        (coherentReduction l E W).obj M :=
      pullbackTensorIntegralReductionTensor l E W M (pullbackTensorIntegralUnit l E W) ≪≫
        (pullbackTensorCalculus l E W).systemClosed.tensor.mapIso
          (Iso.prod (Iso.refl _) (pullbackTensorIntegralUnitReduction l E W)) ≪≫
        (pullbackTensorCalculus l E W).systemClosed.monoidal.rightUnitor _
    obtain ⟨d, hd, hu⟩ := existsUnique_iso_of_map (coherentReduction l E W) target
    refine ⟨d, ?_, ?_⟩
    · change (coherentReduction l E W).map
        d.hom = _
      rw [hd]
      rfl
    · intro d' hd'
      apply hu
      exact hd'

/-- The normalized completed right unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorIntegralRightUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfIntegralConstructibleCategory l E W) :=
  ((@pullbackTensorIntegralRightUnitor_existsUnique l _ E _ _ _ W hW) M).exists.choose

/-- The rational right unitor is the localized completed one.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Use the prescribed rational
tensor object
  equality and localize the integral unitor and its inverse. The displayed hom equality uniquely
  determines the iso. -/
theorem pullbackTensorRationalRightUnitor_existsUnique (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :
    ∃! e : ((@rationalDerivedTensor l _ E _ _ _ W hW)).obj (M,(@pullbackTensorRationalUnit l _ E _ _
      _ W hW)) ≅ M,
      HEq e.hom ((sfRationalConstructibleLocalization l E W).map
        ((@pullbackTensorIntegralRightUnitor l _ E _ _ _ W hW) M.obj).hom) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    apply existsUnique_iso_of_eq
      ((rationalDerivedTensor_existsUnique l E W).exists.choose_spec.1
        (M,pullbackTensorRationalUnit l E W)) rfl
      ((sfRationalConstructibleLocalization l E W).mapIso
        (pullbackTensorIntegralRightUnitor l E W M.obj))

/-- The localized completed right unitor.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorRationalRightUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : sfRationalConstructibleCategory l E W) :=
  ((@pullbackTensorRationalRightUnitor_existsUnique l _ E _ _ _ W hW) M).exists.choose

attribute [local irreducible] pullbackTensorIntegralUnit pullbackTensorRationalUnit
  pullbackTensorIntegralLeftUnitor pullbackTensorIntegralRightUnitor
  pullbackTensorRationalLeftUnitor pullbackTensorRationalRightUnitor

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Scalar extension preserves the canonical rational coefficient-ring unit.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: For integral coefficients, scalar
extension
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
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorRationalScalarUnit
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)] :=
  (@pullbackTensorRationalScalarUnit_existsUnique l _ E _ _ _ L _ _ _ ι W hW).exists.choose

/-- The common-stage unit represented over the least finite coefficient field.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
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
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
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

attribute [local irreducible] pullbackTensorCommonUnitStage pullbackTensorCommonUnit

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The common-stage left unitor has the canonical representative at every larger field.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Represent at the finite
compositum. Apply
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
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorCommonLeftUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  ((@pullbackTensorCommonLeftUnitor_existsUnique l _ Ω _ _ _ W hW) M).exists.choose

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The common-stage right unitor has the canonical representative at every larger field.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Represent at the finite
compositum. Apply
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
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
def pullbackTensorCommonRightUnitor (W : Scheme.{u})
    [hW : ∀ w : W, Invertible (l : W.residueField w)]
    (M : generalAlgebraicallyClosedConstructibleCategory l Ω W) :=
  ((@pullbackTensorCommonRightUnitor_existsUnique l _ Ω _ _ _ W hW) M).exists.choose

/-- Both unit equations for the actual canonical integral comparison.
Source: Stacks 03EL, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
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
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
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
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
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
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
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
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Apply coherent reduction to both
routes.
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
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have := (coherentReduction_fullyFaithful l E X).2
    apply reduced_associativity
      (coherentReduction l E Y) (coherentReduction l E X)
      (constructibleIntegralPullback l E f) (pullbackTensorSequenceDerived l E f)
      (constructibleIntegralTensor l E Y) (constructibleIntegralTensor l E X)
      (pullbackTensorCalculus l E Y).systemClosed.tensor
      (pullbackTensorCalculus l E X).systemClosed.tensor
      (reduction_tensor l E Y) (reduction_tensor l E X) (reduction_pullback l E f)
      (pullbackTensorSystemComparison l E f) (canonicalIntegralPullbackTensor l E f)
      (pullbackTensorIntegralAssociator l E Y) (pullbackTensorIntegralAssociator l E X)
      (pullbackTensorCalculus l E Y).systemClosed.monoidal.associator
      (pullbackTensorCalculus l E X).systemClosed.monoidal.associator
    · intro M N P M' N' P' a b c
      exact @MonoidalCategory.associator_naturality _ _
        (pullbackTensorCalculus l E X).systemClosed.monoidal _ _ _ _ _ _ a b c
    · intro M N P
      exact (pullbackTensorIntegralAssociator_existsUnique l E Y M N P).exists.choose_spec
    · intro M N P
      exact (pullbackTensorIntegralAssociator_existsUnique l E X M N P).exists.choose_spec
    · exact integralComparison_reduction l E f
    · exact pullbackTensorSystemComparison_associativity l E f

/-- Coherence for the canonical rational comparison with the fixed associator.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
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

attribute [local irreducible] pullbackTensorIntegralAssociator
  pullbackTensorRationalAssociator canonicalIntegralPullbackTensor

section RationalCoherenceElaboration
attribute [local irreducible] sfIntegralConstructible Linear.homModule Preadditive.homGroup

/-- The normalized rational comparison obeys this coherence equation.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Apply coherent reduction to both
routes.
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
  intro M N P
  let F := rationalDerivedPullback l E f
  let I := constructibleIntegralPullback l E f
  let Q := sfRationalConstructibleLocalization l E X
  have hF (K) : F.obj K =
      (sfRationalConstructibleLocalization l E X).obj (I.obj K.obj) :=
    (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K
  have hTY (MN) : (rationalDerivedTensor l E Y).obj MN =
      (sfRationalConstructibleLocalization l E Y).obj
        ((constructibleIntegralTensor l E Y).obj (MN.1.obj,MN.2.obj)) :=
    (rationalDerivedTensor_existsUnique l E Y).exists.choose_spec.1 MN
  have hTX (MN) : (rationalDerivedTensor l E X).obj MN =
      Q.obj ((constructibleIntegralTensor l E X).obj (MN.1.obj,MN.2.obj)) :=
    (rationalDerivedTensor_existsUnique l E X).exists.choose_spec.1 MN
  have hmap {A B : sfRationalConstructibleCategory l E Y}
      {A' B' : sfIntegralConstructibleCategory l E Y}
      (hA : A = (sfRationalConstructibleLocalization l E Y).obj A')
      (hB : B = (sfRationalConstructibleLocalization l E Y).obj B')
      (a : A ⟶ B) (b : A' ⟶ B')
      (hab : HEq a ((sfRationalConstructibleLocalization l E Y).map b)) :
      HEq (F.map a) (Q.map (I.map b)) := by
    exact map_localized_heq I F (sfRationalConstructibleLocalization l E Y) Q
      (fun {K L} c ↦
        (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.2 K L c 1)
      hA hB a b hab
  have hbase (K) : (F.obj K).obj = I.obj K.obj := by rw [hF]; rfl
  have hty (A B : sfRationalConstructibleCategory l E Y) :
      ((rationalDerivedTensor l E Y).obj (A,B)).obj =
        (constructibleIntegralTensor l E Y).obj (A.obj,B.obj) := by rw [hTY]; rfl
  have htx (A B : sfRationalConstructibleCategory l E X) :
      ((rationalDerivedTensor l E X).obj (A,B)).obj =
        (constructibleIntegralTensor l E X).obj (A.obj,B.obj) := by rw [hTX]; rfl
  have htmap {A B C D : sfRationalConstructibleCategory l E X}
      {A' B' C' D' : sfIntegralConstructibleCategory l E X}
      (hA : A = Q.obj A') (hB : B = Q.obj B')
      (hC : C = Q.obj C') (hD : D = Q.obj D')
      (a : A ⟶ B) (b : C ⟶ D) (a' : A' ⟶ B') (b' : C' ⟶ D')
      (ha : HEq a (Q.map a')) (hb : HEq b (Q.map b')) :
      HEq ((rationalDerivedTensor l E X).map (Prod.mkHom a b))
        (Q.map ((constructibleIntegralTensor l E X).map (Prod.mkHom a' b'))) := by
    subst A B C D
    have ha' := eq_of_heq ha
    have hb' := eq_of_heq hb
    subst a b
    obtain ⟨bil, hbil, hbil'⟩ :=
      (rationalDerivedTensor_existsUnique l E X).exists.choose_spec.2
        (Q.obj A') (Q.obj B') (Q.obj C') (Q.obj D')
    change HEq ((rationalDerivedTensor_existsUnique l E X).exists.choose.map
      (Prod.mkHom (Q.map a') (Q.map b'))) _
    rw [hbil]
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
      simpa only [one_mul, Q, sfRationalConstructibleLocalization,
        ScalarLocalization.localization] using hbil' a' b' 1 1
  have hc (A B B' : sfIntegralConstructibleCategory l E Y) (h : B = B') :
      HEq (Q.map (canonicalIntegralPullbackTensor l E f A B).hom)
        (Q.map (canonicalIntegralPullbackTensor l E f A B').hom) := by
    subst B'
    rfl
  have ha := (pullbackTensorRationalAssociator_existsUnique l E Y M N P).exists.choose_spec
  have ha' := hmap (by rw [hTY, hTY]; rfl) (by rw [hTY, hTY]; rfl) _ _ ha
  have hmid := (canonicalRationalPullbackTensor_existsUnique l E f M
    ((rationalDerivedTensor l E Y).obj (N,P))).exists.choose_spec
  have hmid' : HEq ((canonicalRationalPullbackTensor l E f M
      ((rationalDerivedTensor l E Y).obj (N,P))).hom)
      (Q.map (canonicalIntegralPullbackTensor l E f M.obj
        ((constructibleIntegralTensor l E Y).obj (N.obj,P.obj))).hom) :=
    hmid.trans (hc M.obj _ _ (hty N P))
  have hnp := (canonicalRationalPullbackTensor_existsUnique l E f N P).exists.choose_spec
  have hid : HEq (𝟙 (F.obj M)) (Q.map (𝟙 (I.obj M.obj))) := by
    have hh {A : sfRationalConstructibleCategory l E X}
        {B : sfIntegralConstructibleCategory l E X} (h : A = Q.obj B) :
        HEq (𝟙 A) (Q.map (𝟙 B)) := by subst A; simp
    exact hh (hF M)
  have hnp' := htmap (hF M) (hF M) (by rw [hF, hTY]; rfl)
    (by rw [hTX, hF, hF]; rfl) (𝟙 (F.obj M)) _ _ _ hid hnp
  have hleft₁ := heq_comp (by rw [hF, hTY, hTY]; rfl)
    (by rw [hF, hTY, hTY]; rfl) (by rw [hTX, hF, hF, hTY]; rfl) ha' hmid'
  have hleft := heq_comp (by rw [hF, hTY, hTY]; rfl)
    (by rw [hTX, hF, hF, hTY]; rfl)
    (by rw [hTX, hTX, hF, hF, hF]; rfl) hleft₁ hnp'
  have hmn := (canonicalRationalPullbackTensor_existsUnique l E f M N).exists.choose_spec
  have hrmid := (canonicalRationalPullbackTensor_existsUnique l E f
    ((rationalDerivedTensor l E Y).obj (M,N)) P).exists.choose_spec
  have hc' (A A' B : sfIntegralConstructibleCategory l E Y) (h : A = A') :
      HEq (Q.map (canonicalIntegralPullbackTensor l E f A B).hom)
        (Q.map (canonicalIntegralPullbackTensor l E f A' B).hom) := by
    subst A'
    rfl
  have hrmid' := hrmid.trans (hc' _ _ P.obj (hty M N))
  have hid' : HEq (𝟙 (F.obj P)) (Q.map (𝟙 (I.obj P.obj))) := by
    have hh {A : sfRationalConstructibleCategory l E X}
        {B : sfIntegralConstructibleCategory l E X} (h : A = Q.obj B) :
        HEq (𝟙 A) (Q.map (𝟙 B)) := by subst A; simp
    exact hh (hF P)
  have hmn' := htmap (by rw [hF, hTY]; rfl)
    (by rw [hTX, hF, hF]; rfl) (hF P) (hF P) _ (𝟙 (F.obj P)) _ _ hmn hid'
  have hrassoc := (pullbackTensorRationalAssociator_existsUnique l E X
    (F.obj M) (F.obj N) (F.obj P)).exists.choose_spec
  have has {A B C A' B' C' : sfIntegralConstructibleCategory l E X}
      (hA : A = A') (hB : B = B') (hC : C = C') :
      HEq (Q.map (pullbackTensorIntegralAssociator l E X A B C).hom)
        (Q.map (pullbackTensorIntegralAssociator l E X A' B' C').hom) := by
    subst A' B' C'
    rfl
  have hrassoc' := hrassoc.trans (has (hbase M) (hbase N) (hbase P))
  have hright₁ := heq_comp (by rw [hF, hTY, hTY]; rfl)
    (by rw [hTX, hF, hTY, hF]; rfl)
    (by rw [hTX, hTX, hF, hF, hF]; rfl) hrmid' hmn'
  have hright := heq_comp (by rw [hF, hTY, hTY]; rfl)
    (by rw [hTX, hTX, hF, hF, hF]; rfl)
    (by rw [hTX, hTX, hF, hF, hF]; rfl) hright₁ hrassoc'
  simp only [← Category.assoc]
  apply eq_of_heq
  simp only [← Functor.map_comp] at hleft hright
  have hh := canonicalIntegralPullbackTensor_associative_spec l E f M.obj N.obj P.obj
  simp only [← Category.assoc] at hh
  simpa only [pullbackTensorRationalAssociator, canonicalRationalPullbackTensor, F] using
    hleft.trans ((heq_of_eq (congrArg Q.map hh)).trans hright.symm)

/-- Coherence for the canonical commonstage comparison with the fixed associator.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
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

/-- Coherence for the canonical integral comparison with the fixed braiding.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
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
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Apply coherent reduction to both
routes.
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
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    have := (coherentReduction_fullyFaithful l E X).2
    let p := reduction_pullback l E f
    exact reduced_braiding
      (coherentReduction l E Y) (coherentReduction l E X)
      (constructibleIntegralPullback l E f) (pullbackTensorSequenceDerived l E f)
      (constructibleIntegralTensor l E Y) (constructibleIntegralTensor l E X)
      (pullbackTensorCalculus l E Y).systemClosed.tensor
      (pullbackTensorCalculus l E X).systemClosed.tensor
      (pullbackTensorIntegralReductionTensor l E Y)
      (pullbackTensorIntegralReductionTensor l E X) p
      (canonicalIntegralPullbackTensor l E f)
      (fun M N ↦ (pullbackTensorSystemComparison l E f).app (M, N))
      (pullbackTensorIntegralBraiding l E Y) (pullbackTensorIntegralBraiding l E X)
      (fun M N ↦ (pullbackTensorBraiding
        (coefficientSequenceTopology (ProEt.topology Y)) (coefficientSequenceCommRingSheaf l E Y)
        (pullbackTensorCalculus l E Y).systemClosed
        (pullbackTensorCalculus l E Y).systemTensorModel).app (M, N))
      (pullbackTensorBraiding
        (coefficientSequenceTopology (ProEt.topology X)) (coefficientSequenceCommRingSheaf l E X)
        (pullbackTensorCalculus l E X).systemClosed
        (pullbackTensorCalculus l E X).systemTensorModel)
      (fun M N ↦ (pullbackTensorIntegralBraiding_existsUnique l E Y M N).exists.choose_spec)
      (fun M N ↦ (pullbackTensorIntegralBraiding_existsUnique l E X M N).exists.choose_spec)
      (integralComparison_reduction l E f) (pullbackTensorSystemComparison_braiding l E f)

/-- Coherence for the canonical rational comparison with the fixed braiding.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
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
(blueprint: lem-pur-derived-pullback-tensor-constraints). Proof: Apply coherent reduction to both
routes.
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
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    intro M N
    let F := rationalDerivedPullback l E f
    let I := constructibleIntegralPullback l E f
    let Q := sfRationalConstructibleLocalization l E X
    have hF (K) : F.obj K =
        (sfRationalConstructibleLocalization l E X).obj (I.obj K.obj) :=
      (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.1 K
    have hTY (MN) : (rationalDerivedTensor l E Y).obj MN =
        (sfRationalConstructibleLocalization l E Y).obj
          ((constructibleIntegralTensor l E Y).obj (MN.1.obj,MN.2.obj)) :=
      (rationalDerivedTensor_existsUnique l E Y).exists.choose_spec.1 MN
    have hTX (MN) : (rationalDerivedTensor l E X).obj MN =
        Q.obj ((constructibleIntegralTensor l E X).obj (MN.1.obj,MN.2.obj)) :=
      (rationalDerivedTensor_existsUnique l E X).exists.choose_spec.1 MN
    have hm : (F.obj M).obj = I.obj M.obj := by
      rw [hF]
      rfl
    have hn : (F.obj N).obj = I.obj N.obj := by
      rw [hF]
      rfl
    have hmap {A B : sfRationalConstructibleCategory l E Y}
        {A' B' : sfIntegralConstructibleCategory l E Y}
        (hA : A = (sfRationalConstructibleLocalization l E Y).obj A')
        (hB : B = (sfRationalConstructibleLocalization l E Y).obj B')
        (a : A ⟶ B) (b : A' ⟶ B')
        (hab : HEq a ((sfRationalConstructibleLocalization l E Y).map b)) :
        HEq (F.map a) (Q.map (I.map b)) := by
      exact map_localized_heq I F (sfRationalConstructibleLocalization l E Y) Q
        (fun {K L} c ↦
          (rationalDerivedPullback_existsUnique l E f).exists.choose_spec.2.2 K L c 1)
        hA hB a b hab
    have hb := (pullbackTensorRationalBraiding_existsUnique l E Y M N).exists.choose_spec
    have hb' := hmap (hTY (M,N)) (hTY (N,M)) _ _ hb
    have hc := (canonicalRationalPullbackTensor_existsUnique l E f N M).exists.choose_spec
    have hleft := heq_comp
      (by rw [hF, hTY]; rfl)
      (by rw [hF, hTY]; rfl)
      (by rw [hTX, hF, hF]; rfl) hb' hc
    have hd := (canonicalRationalPullbackTensor_existsUnique l E f M N).exists.choose_spec
    have he := (pullbackTensorRationalBraiding_existsUnique l E X
      (F.obj M) (F.obj N)).exists.choose_spec
    have hsym {A B A' B' : sfIntegralConstructibleCategory l E X}
        (hA : A = A') (hB : B = B') :
        HEq (Q.map (pullbackTensorIntegralBraiding l E X A B).hom)
          (Q.map (pullbackTensorIntegralBraiding l E X A' B').hom) := by
      subst A' B'
      rfl
    have he' : HEq ((pullbackTensorRationalBraiding l E X (F.obj M) (F.obj N)).hom)
        (Q.map ((pullbackTensorIntegralBraiding l E X (I.obj M.obj) (I.obj N.obj)).hom)) :=
      he.trans (hsym hm hn)
    have hright := heq_comp
      (by rw [hF, hTY]; rfl)
      (by rw [hTX, hF, hF]; rfl)
      (by rw [hTX, hF, hF]; rfl) hd he'
    apply eq_of_heq
    refine hleft.trans ?_
    refine (heq_of_eq (Q.map_comp _ _).symm).trans ?_
    rw [canonicalIntegralPullbackTensor_braiding_spec l E f M.obj N.obj]
    exact (heq_of_eq (Q.map_comp _ _)).trans hright.symm

/-- Coherence for the canonical commonstage comparison with the fixed braiding.
Source: Stacks 06YS, 07A4, 0941; blueprint coefficient conventions
(blueprint: lem-pur-derived-pullback-tensor-constraints). -/
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

end RationalCoherenceElaboration

attribute [local irreducible] pullbackTensorIntegralBraiding pullbackTensorRationalBraiding
  rationalDerivedTensor rationalDerivedPullback canonicalRationalPullbackTensor

end HigherCoherence
end WeilConjectures
