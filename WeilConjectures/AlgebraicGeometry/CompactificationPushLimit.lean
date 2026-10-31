/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompleteCompactificationLimitSupport

import all WeilConjectures.AlgebraicGeometry.CompletedDirectImageLimits
import all WeilConjectures.AlgebraicGeometry.ConstantTowerDirectImageNormalization

/-! # Direct image and fixed-coefficient strict limits
Source: blueprint direct-image proof, paragraph (2); Stacks 0A07, 0D6E.
(blueprint: lem-sp-compactification-push-limit).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Evaluate the actual constant-tower/limit counit using the canonical exact factors. -/
private def counitProjection (T : Scheme.{u}) (n : ℕ) :
    coefficientConstantTowerLimit l E T ⟶ coefficientConstantTowerEvaluation l E T n where
  app M := (constantEvaluationIso (scalarReductionSource l E T) (op n)).inv.app
      ((coefficientConstantTowerLimit l E T).obj M) ≫
    (coefficientConstantTowerEvaluation l E T n).map
      ((cbcRealizationLimitAdj T ((PurCompactSupport.completed l E).ring T)).counit.app M)
  naturality M N a := by
    let V := coefficientConstantTowerEvaluation l E T n
    let L := coefficientConstantTowerLimit l E T
    let C := (Functor.const ℕᵒᵖ : scalarReductionSource l E T ⥤ _).mapDerivedCategory
    let e := constantEvaluationIso (scalarReductionSource l E T) (op n)
    have hn := e.inv.naturality (L.map a)
    change L.map a ≫ e.inv.app (L.obj N) =
      e.inv.app (L.obj M) ≫ V.map (C.map (L.map a)) at hn
    change L.map a ≫ (e.inv.app (L.obj N) ≫ V.map _) =
      (e.inv.app (L.obj M) ≫ V.map _) ≫ V.map a
    rw [← Category.assoc, hn, Category.assoc, ← V.map_comp]
    erw [(cbcRealizationLimitAdj T
      ((PurCompactSupport.completed l E).ring T)).counit.naturality]
    simp only [V.map_comp, Category.assoc, Functor.id_map]

/-- The prescribed K-injective normalization uniquely identifies the counit projection. -/
private theorem counitProjection_eq (T : Scheme.{u}) (n : ℕ) :
    counitProjection l E T n = coefficientConstantTowerProjection l E T n := by
  apply (coefficientConstantTowerProjection_exists l E T n).choose_spec.2
  intro I hI
  let L : Fixed l E T ⥤ scalarReductionSource l E T := lim
  have hu : L.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj I) = L.rightDerivedFunctorUnitQ I := by
    dsimp only [Functor.rightDerivedFunctorUnitQ]
    erw [AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.quotient_inv_id,
      AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.quotient_hom_id,
      L.rightDerivedFunctor.map_id, Category.id_comp, Category.comp_id]
  have h := constantLimit_projection_unit (scalarReductionSource l E T) (op n) I
  change L.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I) ≫
    (counitProjection l E T n).app (DerivedCategory.Q.obj I) = _ at h
  rw [hu, L.rightDerivedFunctorUnitQ_eq] at h
  apply (cancel_epi (L.rightDerivedFunctorObjQIso I).inv).mp
  rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id_assoc]
  rw [Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- Fixed-tower direct-image evaluation and the projections of its specified limit mate.

Proof. Use the unique K-injective-normalized tower evaluation comparison from the
completed direct-image machinery. Its mate description identifies it with the
right mate of the exact pullback/evaluation square. Exact localization preserves
the ordinary constant/pullback/evaluation triangle, and taking mates gives the
corresponding direct-image triangle. Apply the abstract mate/limit projection
identity to this triangle. The iterated-mate identity identifies the resulting
comparison with the specified pushLimit. Finally identify the counit projections
with the prescribed coefficientConstantTowerProjection using their uniqueness on
K-injective towers, and cancel the evaluation isomorphism. This works for every
morphism p, including identities and maps between empty schemes; no properness or
boundedness hypothesis is used.
Source: current blueprint, sec-smooth-purity/sk-prop-sp-integral-adjunction,
sk-prop-sp-integral-adjunction-direct-image.proof.md, paragraph (2);
parent node step 3; Stacks 0A07, lemma-Rf-commutes-with-Rlim, and 0D6E,
lemma-derived-pushforward-composition.
(blueprint: lem-sp-compactification-push-limit). -/
theorem compactificationPushLimit {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    ∃ w : ∀ n : ℕ, (fixedPushOrd l E p).rightDerivedFunctor ⋙
        coefficientConstantTowerEvaluation l E Y n ≅
      coefficientConstantTowerEvaluation l E Z n ⋙ (pushOrd l E p).rightDerivedFunctor,
    (∀ n : ℕ,
      ∀ (I : CochainComplex (Fixed l E Z) ℤ) [I.IsKInjective],
    (fixedEvaluation l E Y n).mapDerivedCategory.map
        ((fixedPushOrd l E p).rightDerivedFunctorObjQIso I).hom ≫
      (fixedEvaluation l E Y n).mapDerivedCategoryFactors.hom.app
        (((fixedPushOrd l E p).mapHomologicalComplex (.up ℤ)).obj I) =
    (w n).hom.app (DerivedCategory.Q.obj I) ≫
      (pushOrd l E p).rightDerivedFunctor.map
        ((fixedEvaluation l E Z n).mapDerivedCategoryFactors.hom.app I) ≫
      ((pushOrd l E p).rightDerivedFunctorObjQIso
        (((fixedEvaluation l E Z n).mapHomologicalComplex (.up ℤ)).obj I)).hom) ∧
    ∀ (K : DerivedCategory (Fixed l E Z)) (n : ℕ),
      (pushLimit l E p).hom.app K ≫
          (coefficientConstantTowerProjection l E Y n).app
            (((fixedPushOrd l E p).rightDerivedFunctor).obj K) =
        (pushOrd l E p).rightDerivedFunctor.map
          ((coefficientConstantTowerProjection l E Z n).app K) ≫ (w n).inv.app K := by
  let P := proEtaleRingModulePullback p ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring Z) ((PurCompactSupport.completed l E).pull p)
  let G := pushOrd l E p
  let H := (Functor.whiskeringRight ℕᵒᵖ _ _).obj P
  let CZ := (Functor.const ℕᵒᵖ : scalarReductionSource l E Z ⥤ _).mapDerivedCategory
  let CY := (Functor.const ℕᵒᵖ : scalarReductionSource l E Y ⥤ _).mapDerivedCategory
  let a := proEtaleRingModuleAdjunction p ((PurCompactSupport.completed l E).ring Y)
    ((PurCompactSupport.completed l E).ring Z) ((PurCompactSupport.completed l E).pull p)
  let ad := a.mapDerivedCategoryRightDerivedAdjunction
  let bd := (a.whiskerRight ℕᵒᵖ).mapDerivedCategoryRightDerivedAdjunction
  let w := fun n : ℕ ↦ (normalizedTowerEvaluation
    (scalarReductionSource l E Z) (scalarReductionSource l E Y) G (op n)).choose
  have hw n := (normalizedTowerEvaluation
    (scalarReductionSource l E Z) (scalarReductionSource l E Y) G (op n)).choose_spec.1
  refine ⟨w, fun n ↦ hw n, ?_⟩
  intro K n
  let EZ := fixedEvaluation l E Z n
  let EY := fixedEvaluation l E Y n
  let v := (Functor.mapDerivedCategoryCompIso H EZ).symm ≪≫
    Functor.mapDerivedCategoryNatIso (Iso.refl _) ≪≫
      Functor.mapDerivedCategoryCompIso EY P
  have hm : (w n).hom = (mateEquiv bd ad (TwoSquare.mk _ _ _ _ v.inv)).natTrans :=
    evaluationComparison_mate P G a (op n) (w n) (hw n)
  have hpull (N : Integral l E Y) :
      v.inv.app (CY.obj N) ≫
        EZ.mapDerivedCategory.map ((cbcRealizationConst P).inv.app N) ≫
        (constantEvaluationIso (scalarReductionSource l E Z) (op n)).hom.app
          (P.mapDerivedCategory.obj N) =
      P.mapDerivedCategory.map
        ((constantEvaluationIso (scalarReductionSource l E Y) (op n)).hom.app N) := by
    have h := AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.exact_triangle_square
      (Functor.const ℕᵒᵖ : scalarReductionSource l E Y ⥤ _)
      (Functor.const ℕᵒᵖ : scalarReductionSource l E Z ⥤ _) P H EY EZ
      (Functor.compConstIso ℕᵒᵖ P).symm (Iso.refl (EY ⋙ P))
      (Functor.constCompEvaluationObj (D := scalarReductionSource l E Y) (op n))
      (Functor.constCompEvaluationObj (D := scalarReductionSource l E Z) (op n))
      (fun M ↦ by
        change P.map (𝟙 M) ≫ 𝟙 _ ≫ 𝟙 _ = 𝟙 _
        rw [P.map_id, Category.id_comp, Category.id_comp]) N
    simpa only [v, cbcRealizationConst, constantEvaluationIso,
      Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
      Iso.symm_inv, NatTrans.comp_app, ← Functor.mapDerivedCategoryNatIso_symm,
      Iso.refl_symm, Functor.mapDerivedCategoryNatIso_refl, NatTrans.id_app,
      Category.id_comp, Category.comp_id, Category.assoc, CY] using h
  let e := TwoSquare.mk _ _ _ _ (cbcRealizationConst P).inv
  let chi := mateEquiv ad bd e
  have hpush (N : Integral l E Z) :
      EY.mapDerivedCategory.map (chi.natTrans.app N) ≫ (w n).hom.app (CZ.obj N) ≫
        G.rightDerivedFunctor.map
          ((constantEvaluationIso (scalarReductionSource l E Z) (op n)).hom.app N) =
      (constantEvaluationIso (scalarReductionSource l E Y) (op n)).hom.app
        (G.rightDerivedFunctor.obj N) := by
    have h := AlgebraicGeometry.ProEtale.StrictTower.ConstantNormalization.mates_evaluation
      ad bd CY CZ EY.mapDerivedCategory EZ.mapDerivedCategory
      (constantEvaluationIso (scalarReductionSource l E Y) (op n))
      (constantEvaluationIso (scalarReductionSource l E Z) (op n))
      (cbcRealizationConst P).inv v.inv hpull N
    rw [hm]
    exact h
  let ax := cbcRealizationLimitAdj Z ((PurCompactSupport.completed l E).ring Z)
  let ay := cbcRealizationLimitAdj Y ((PurCompactSupport.completed l E).ring Y)
  have h := mate_limit_projection CZ CY
    (coefficientConstantTowerLimit l E Z) (coefficientConstantTowerLimit l E Y) ax ay
    G.rightDerivedFunctor (fixedPushOrd l E p).rightDerivedFunctor
    EZ.mapDerivedCategory EY.mapDerivedCategory
    (constantEvaluationIso (scalarReductionSource l E Z) (op n))
    (constantEvaluationIso (scalarReductionSource l E Y) (op n))
    chi.natTrans (w n) hpush K
  have hi := iterated_mateEquiv_conjugateEquiv ad bd ay ax e
  change (mateEquiv ax ay chi).natTrans = (pushLimit l E p).hom at hi
  change (mateEquiv ax ay chi).natTrans.app K ≫ _ = _ at h
  rw [hi] at h
  have h' : (pushLimit l E p).hom.app K ≫
      (counitProjection l E Y n).app _ ≫ (w n).hom.app K =
      G.rightDerivedFunctor.map ((counitProjection l E Z n).app K) := by
    simpa only [counitProjection, Category.assoc, EZ, EY, ax, ay,
      coefficientConstantTowerEvaluation, fixedEvaluation] using h
  rw [counitProjection_eq, counitProjection_eq] at h'
  apply (cancel_mono ((w n).hom.app K)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  exact h'.trans (Category.comp_id _).symm

end AlgebraicGeometry.ProEtale.CompleteCompactificationLimit
