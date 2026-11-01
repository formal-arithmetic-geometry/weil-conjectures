/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FixProjectionCompactification.FactorEvaluation.IntegralProjectionFactorEvaluationData
import WeilConjectures.SixFunctors.IntegralProjectionReduction.IntegralProjectionPullEvaluation

/-! # Evaluation of the unary proper direct-image coefficient mate

Source: prop-sf-pf-coherence, proper counit transpose.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale
namespace WeilConjectures.FixProjectionCompactification
open IntegralSystemRealization

attribute [local irreducible] CategoryTheory.constantSheaf HasDerivedCategory.standard
  AlgebraicGeometry.Scheme.residueField integralDerivedPullback integralCompletedTensor
  pullbackTensorCalculus

attribute [local implicit_reducible] identitySquare sixFunctorIntegralReduction
  coefficientFiniteDerivedExtension sixFunctorFinitePullback
  Over.Hom Over.homMk CostructuredArrow.homMk
  scalarReductionSourceDerived scalarReductionTargetDerived integralCoefficientSheaf
  integralCoefficientCommRingSheaf integralOperationsCommHasDerivedCategory
  integralCompletedRingHasDerivedCategory integralTowerHasDerivedCategory
  coefficientFiniteHasDerived reductionModulesHasDerivedCategory SemilinearSections.moduleAbelian
  AlgebraicGeometry.Scheme.proEtaleRingModules_hasDerivedCategory scalarReductionDerivedExtension

attribute [local irreducible] DerivedCategory instCategoryDerivedCategory
  SheafOfModules.instAbelian

private theorem evaluateTranspose
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    {F : A ⥤ B} {G : B ⥤ A} {F' : A' ⥤ B'} {G' : B' ⥤ A'}
    (adj : F ⊣ G) (adj' : F' ⊣ G') (V : A ⥤ A') (W : B ⥤ B')
    (a : F ⋙ W ≅ V ⋙ F') (b : G ⋙ V ≅ W ⋙ G')
    (hc : ∀ M : B, a.hom.app (G.obj M) ≫ F'.map (b.hom.app M) ≫
      adj'.counit.app (W.obj M) = W.map (adj.counit.app M))
    {N : A} {M : B} (v : F.obj N ⟶ M) :
    V.map (adj.homEquiv N M v) ≫ b.hom.app M =
      adj'.homEquiv _ _ (a.inv.app N ≫ W.map v) := by
  apply (adj'.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_apply, Functor.map_comp]
  rw [Category.assoc]
  have h := hc M
  have h' : F'.map (b.hom.app M) ≫ adj'.counit.app (W.obj M) =
      a.inv.app (G.obj M) ≫ W.map (adj.counit.app M) := by
    rw [← h]
    simp only [Iso.inv_hom_id_app_assoc]
  rw [h', ← Category.assoc]
  have hn := a.inv.naturality (adj.homEquiv N M v)
  simp only [Functor.comp_map] at hn
  rw [hn]
  rw [Category.assoc, ← W.map_comp]
  have he := (adj.homEquiv N M).symm_apply_apply v
  simp only [Adjunction.homEquiv_symm_apply] at he
  rw [he]

private theorem compositeCounit
    {A B A' B' A'' B'' : Type*}
    [Category* A] [Category* B] [Category* A'] [Category* B']
    [Category* A''] [Category* B'']
    {F : A ⥤ B} {G : B ⥤ A} {F' : A' ⥤ B'} {G' : B' ⥤ A'}
    {F'' : A'' ⥤ B''} {G'' : B'' ⥤ A''}
    {adj : F ⊣ G} {adj' : F' ⊣ G'} {adj'' : F'' ⊣ G''}
    {V : A ⥤ A'} {W : B ⥤ B'} {V' : A' ⥤ A''} {W' : B' ⥤ B''}
    (a : SuppliedExchangeProjection.ExchangeProjectionAdjunctionComparison adj adj' V W)
    (b : SuppliedExchangeProjection.ExchangeProjectionAdjunctionComparison adj' adj'' V' W')
    (M : B) :
    F''.map (V'.map (a.right.hom.app M) ≫ b.right.hom.app (W.obj M)) ≫
        adj''.counit.app (W'.obj (W.obj M)) =
      b.left.inv.app (V.obj (G.obj M)) ≫ W'.map (a.left.inv.app (G.obj M)) ≫
        W'.map (W.map (adj.counit.app M)) := by
  rw [Functor.map_comp, Category.assoc, b.counit]
  rw [← Category.assoc]
  have hn := b.left.inv.naturality (a.right.hom.app M)
  simp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [hn]
  rw [Category.assoc]
  rw [← W'.map_comp, a.counit, Functor.map_comp]

private theorem transportCounit
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    {F F₀ : A ⥤ B} {G G₀ : B ⥤ A} {F' : A' ⥤ B'} {G' : B' ⥤ A'}
    (adj : F ⊣ G) (adj₀ : F₀ ⊣ G₀) (adj' : F' ⊣ G')
    (hF : F = F₀) (hG : G = G₀) (ha : HEq adj adj₀)
    (V : A ⥤ A') (W : B ⥤ B')
    (a : F₀ ⋙ W ≅ V ⋙ F') (b : G₀ ⋙ V ≅ W ⋙ G')
    (hc : ∀ M : B, F'.map (b.hom.app M) ≫ adj'.counit.app (W.obj M) =
      a.inv.app (G₀.obj M) ≫ W.map (adj₀.counit.app M)) (M : B) :
    F'.map (V.map (eqToHom (congrArg (fun H : B ⥤ A ↦ H.obj M) hG)) ≫
        b.hom.app M) ≫ adj'.counit.app (W.obj M) =
      a.inv.app (G.obj M) ≫
        W.map (eqToHom (congrArg (fun H : A ⥤ B ↦ H.obj (G.obj M)) hF).symm) ≫
        W.map (adj.counit.app M) := by
  subst F₀
  subst G₀
  cases eq_of_heq ha
  simpa using hc M

private theorem mateEvaluation
    {A B A' B' : Type*} [Category* A] [Category* B] [Category* A'] [Category* B']
    {F : A ⥤ B} {G : B ⥤ A} {F' : A' ⥤ B'} {G' : B' ⥤ A'}
    (adj : F ⊣ G) (adj' : F' ⊣ G') (V : A ⥤ A') (W : B ⥤ B')
    (a : F ⋙ W ≅ V ⋙ F') (b : G ⋙ V ≅ W ⋙ G')
    (hc : ∀ M : B, a.hom.app (G.obj M) ≫ F'.map (b.hom.app M) ≫
      adj'.counit.app (W.obj M) = W.map (adj.counit.app M))
    {N : A} {M P : B} (p : P ≅ F.obj N) (v : P ⟶ M)
    {N' : A'} {M' : B'} (e : V.obj N ≅ N') (d : W.obj M ≅ M')
    (t : W.obj P ≅ F'.obj N') (s : N' ⟶ G'.obj M')
    (hp : W.map p.hom ≫ a.hom.app N ≫ F'.map e.hom = t.hom)
    (hs : F'.map s ≫ adj'.counit.app M' = t.inv ≫ W.map v ≫ d.hom) :
    V.map (adj.homEquiv _ _ (p.inv ≫ v)) ≫ b.hom.app M ≫ G'.map d.hom =
      e.hom ≫ s := by
  rw [← Category.assoc, evaluateTranspose adj adj' V W a b hc]
  apply (adj'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
  have hn := adj'.counit.naturality d.hom
  simp only [Functor.comp_map, Functor.id_map] at hn
  have he := (adj'.homEquiv (V.obj N) (W.obj M)).symm_apply_apply
    (a.inv.app N ≫ W.map (p.inv ≫ v))
  simp only [Adjunction.homEquiv_symm_apply, Functor.map_comp] at he
  rw [hn, ← Category.assoc, he, hs]
  have hp' : F'.map e.hom ≫ t.inv = a.inv.app N ≫ W.map p.inv := by
    have ht : t = W.mapIso p ≪≫ a.app N ≪≫ F'.mapIso e := by
      apply Iso.ext
      simpa only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
        Category.assoc] using hp.symm
    rw [ht]
    simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc]
    rw [← F'.map_comp_assoc, e.hom_inv_id, F'.map_id, Category.id_comp]
  rw [← Category.assoc (F'.map e.hom), hp']
  simp only [Category.assoc]

set_option maxHeartbeats 2000000 in
-- Transporting the derived adjunctions elaborates dependent functor comparison squares.
/-- Evaluation of the proper coefficient mate on one arbitrary constructible input.
Neither open extension nor compact-support identification occurs in this equation.

Source: prop-sf-pf-coherence.proof.md, the proper counit transpose;
def-sf-operation-stages, pullProjection and the coefficient counit equation.
(blueprint: lem-sf-integral-projection-direct-factor-evaluation).

Proof: transport the exchange stage's proper adjunction to integral.pullDirectAdjunction
using properPull, properPush and properAdjunction. Transpose both sides under the finite
pull/direct adjunction. DirectEvaluation.counit identifies evaluation of the system
transpose with its finite transpose. integralProjectionPullEvaluation identifies the
inverse pullback-reduction comparison with directAdjunction.left inverse. The coefficient
counit equation then gives directAdjunction.right followed by finiteDirectImage, which
is FactorEvaluation.direct. Naturality of reductionEvaluation moves the source and target
coordinate isomorphisms through the counit. Cancel the finite Hom equivalence. This uses
an arbitrary constructible input, including zero, and applies to identity proper maps;
there is no compact-support factorization, no tensor and no equality detection step. -/
theorem integralProjectionDirectFactorEvaluation
    (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
    (E : Type u) [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] (n : ℕ) (hn : 1 ≤ n)
    (S : SixFunctorOperationDatum D C E n hn) (hl : IsUnit (C.l : D.k))
    (o : Operations C.l E) (z : Realizations C.l E D o)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    (c : Compactification f.hom.left) (m : ℕ)
    (M : sfIntegralConstructibleCategory C.l E (identitySquare f c).Z.obj.left) :
    (coefficientSequenceDerivedEvaluation C.l E Y.obj.left m).map
        (ProjectionFactors.directReduction D C E n hn S hl o z f c M) ≫
      ((o.evaluation c.g).evaluation m).hom.app
        ((calculus C.l E c.Z).reduction.obj M.obj) ≫
      (proEtaleConstantDerivedDirectImage c.g
        (Padic.coefficientExtensionRing C.l E (m + 1))).map
          (((calculus C.l E c.Z).reductionEvaluation m).hom.app M.obj) =
    ((calculus C.l E Y.obj.left).reductionEvaluation m).hom.app
        (((S.higher.integralExchange (identitySquare f c)).stage.properPush.obj M).obj) ≫
      (FactorEvaluation.direct D C E n hn S f c m M).hom := by
  let A := S.higher.integralExchange (identitySquare f c)
  let R := (S.integralNormalization.reduction m).directAdjunction (identitySquare f c).p
  let T := S.integralNormalization.finiteLevels m
  let IY := (intrinsicFiniteTorsionConstructible C.l E (m + 1)
    (Nat.le_add_left 1 m) Y.obj.left).ι
  let IZ := (intrinsicFiniteTorsionConstructible C.l E (m + 1)
    (Nat.le_add_left 1 m) c.Z).ι
  let QY := sixFunctorIntegralReduction D C E m Y ⋙ IY
  let QZ := sixFunctorIntegralReduction D C E m (identitySquare f c).Z ⋙ IZ
  let V := coefficientSequenceDerivedEvaluation C.l E Y.obj.left m
  let W := coefficientSequenceDerivedEvaluation C.l E c.Z m
  let RY := (calculus C.l E Y.obj.left).reduction
  let RZ := (calculus C.l E c.Z).reduction
  let q := finiteDerivedPullback C.l E m c.g
  let eY := (calculus C.l E Y.obj.left).reductionEvaluation m
  let eZ := (calculus C.l E c.Z).reductionEvaluation m
  let t := Functor.isoWhiskerRight R.left IZ ≪≫
    Functor.isoWhiskerLeft (sixFunctorIntegralReduction D C E m Y)
      (T.finitePullback (identitySquare f c).p)
  let s := FactorEvaluation.directIso D C E n hn S f c m
  let ts := Functor.isoWhiskerRight (eqToIso A.properPull) QZ ≪≫ t
  let ss := Functor.isoWhiskerRight (eqToIso A.properPush) QY ≪≫ s
  obtain ⟨b, hbL, hbR⟩ := T.finiteDirectAdjunctionNormalization (identitySquare f c).p
  have hc₀ (N : sfIntegralConstructibleCategory C.l E c.Z) :
      q.map (s.hom.app N) ≫ (finiteAdj C.l E c.g m).counit.app (QZ.obj N) =
        t.inv.app ((S.higher.integral.direct (identitySquare f c).p).obj N) ≫
          QZ.map ((S.higher.integral.pullDirectAdjunction
            (identitySquare f c).p).counit.app N) := by
    have h := compositeCounit R b N
    rw [hbL, hbR] at h
    simp only [t, s, FactorEvaluation.directIso, Iso.trans_hom, Iso.trans_inv,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
      Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.comp_map,
      Category.assoc, q, R, T, finiteCoefficientRing,
      finiteAdj, finiteDerivedPullback, sfIntrinsicDerivedPullback,
      QZ, IZ, Functor.comp_obj,
      proEtaleDerivedCategory,
      proEtaleRingModules, proEtaleConstantRing, ringedSiteModules] at h ⊢
    dsimp only [identitySquare, Over.mk, Over.left, Over.Hom.left, CostructuredArrow.mk,
      ObjectProperty.homMk, Over.homMk, CostructuredArrow.homMk] at h ⊢
    exact h
  have hc₁ (N : sfIntegralConstructibleCategory C.l E c.Z) :
      q.map (ss.hom.app N) ≫ (finiteAdj C.l E c.g m).counit.app (QZ.obj N) =
        ts.inv.app (A.stage.properPush.obj N) ≫
          QZ.map (A.stage.properAdjunction.counit.app N) := by
    have h := transportCounit A.stage.properAdjunction
      (S.higher.integral.pullDirectAdjunction (identitySquare f c).p)
      (finiteAdj C.l E c.g m) A.properPull A.properPush A.properAdjunction
      QY QZ t s hc₀ N
    simpa only [ts, ss, Iso.trans_hom, Iso.trans_inv,
      NatTrans.comp_app, Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
      Functor.whiskerRight_app, eqToIso.hom, eqToIso.inv, eqToHom_app,
      Category.assoc] using h
  have hp (N : sfIntegralConstructibleCategory C.l E Y.obj.left) :
      W.map (ProjectionFactors.properPullReduction D C E n hn S hl o z f c N).hom ≫
        (pullbackTensorDerivedEvaluation C.l E c.g m).hom.app (RY.obj N.obj) ≫
        q.map (eY.hom.app N.obj) =
      eZ.hom.app (A.stage.properPull.obj N).obj ≫ ts.hom.app N := by
    let p₀ := RZ.mapIso (Coordinates.pullValue D C E S.higher hl
      (identitySquare f c).p N) ≪≫ Coordinates.pullReduction D C E o z c.g N.obj
    have h₀ : W.map p₀.hom ≫
        (pullbackTensorDerivedEvaluation C.l E c.g m).hom.app (RY.obj N.obj) ≫
        q.map (eY.hom.app N.obj) =
      eZ.hom.app ((S.higher.integral.pull (identitySquare f c).p).obj N).obj ≫
        t.hom.app N := by
      have h := congrArg (fun k ↦ k ≫ (T.finitePullback
        (identitySquare f c).p).hom.app
          ((sixFunctorIntegralReduction D C E m Y).obj N))
        (IntegralProjectionReduction.integralProjectionPullEvaluation S m hl o z
          (identitySquare f c).p N)
      dsimp only [IntegralProjectionReduction.pullIso, ObjectProperty.isoMk,
        ObjectProperty.homMk] at h
      simp only [p₀, W, RY, RZ, eY, eZ, q, R, T, IZ,
        finiteCoefficientRing,
        IntegralProjectionReduction.evaluation, IntegralProjectionReduction.evaluatedPull,
        IntegralProjectionReduction.reductionEvaluation,
        IntegralProjectionReduction.stage, ObjectProperty.ι_map,
        IntegralProjectionReduction.reduction, Functor.mapIso_hom, Iso.trans_hom,
        Iso.app_hom, t, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
        Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
        Functor.comp_obj, ObjectProperty.ι_obj, integralCoefficientSheaf,
        scalarReductionTarget, normalizedDVRModules, normalizedDVRDerived,
        proEtaleDerivedCategory] at h ⊢
      dsimp only [identitySquare, Over.mk, Over.left, Over.Hom.left, CostructuredArrow.mk,
        ObjectProperty.homMk, Over.homMk, CostructuredArrow.homMk] at h ⊢
      dsimp only [Iso.trans, Iso.symm, Iso.app, Functor.mapIso,
        ObjectProperty.ι, inducedFunctor] at h
      erw [Category.assoc, Category.assoc, Category.assoc,
        Iso.inv_hom_id_app, Category.comp_id, Category.assoc] at h
      exact h
    let v := eqToHom (congrArg (fun F ↦ (F.obj N).obj) A.properPull)
    have hv := eZ.hom.naturality v
    have he : (ProjectionFactors.properPullReduction D C E n hn S hl o z f c N).hom =
        RZ.map v ≫ p₀.hom := by
      dsimp only [ProjectionFactors.properPullReduction, Iso.trans_hom, Functor.mapIso_hom,
        eqToIso.hom]
      rfl
    rw [he, W.map_comp, Category.assoc, h₀]
    simpa only [ts, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
      Functor.whiskerRight_app, eqToIso.hom, eqToHom_app, QZ, Functor.comp_map,
      ObjectProperty.ι_map, ObjectProperty.eqToHom_hom, eqToHom_map, v,
      Category.assoc] using
        congrArg (fun k ↦ k ≫ t.hom.app N) hv
  have hs : q.map (ss.hom.app M) ≫
      (finiteAdj C.l E c.g m).counit.app (QZ.obj M) =
      ((eZ.app (A.stage.properPull.obj (A.stage.properPush.obj M)).obj) ≪≫
        ts.app (A.stage.properPush.obj M)).inv ≫
        W.map (RZ.map (A.stage.properAdjunction.counit.app M).hom) ≫
        eZ.hom.app M.obj := by
    rw [hc₁]
    have hε := eZ.hom.naturality (A.stage.properAdjunction.counit.app M).hom
    simp only [Iso.trans_inv, Iso.app_inv, Category.assoc]
    simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hε
    rw [hε]
    simp only [Iso.inv_hom_id_app_assoc]
    rfl
  have h := mateEvaluation (o.direct c.g).adj (finiteAdj C.l E c.g m) V W
    (pullbackTensorDerivedEvaluation C.l E c.g m) ((o.evaluation c.g).evaluation m)
    ((o.evaluation c.g).counit m)
    (ProjectionFactors.properPullReduction D C E n hn S hl o z f c
      (A.stage.properPush.obj M))
    (RZ.map (A.stage.properAdjunction.counit.app M).hom)
    (eY.app (A.stage.properPush.obj M).obj) (eZ.app M.obj)
    ((eZ.app (A.stage.properPull.obj (A.stage.properPush.obj M)).obj) ≪≫
      ts.app (A.stage.properPush.obj M))
    (ss.hom.app M) (hp (A.stage.properPush.obj M)) hs
  simpa only [ProjectionFactors.directReduction, FactorEvaluation.direct,
    ss, s, QY, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    eqToIso.hom, eqToHom_app, ObjectProperty.ι_map,
    Functor.comp_map, Functor.comp_obj, Functor.id_obj, ObjectProperty.ι_obj,
    integralCoefficientSheaf, scalarReductionTarget, normalizedDVRModules,
    normalizedDVRDerived, proEtaleDerivedCategory,
    eqToHom_map, ObjectProperty.eqToHom_hom, Category.assoc] using h

end WeilConjectures.FixProjectionCompactification
