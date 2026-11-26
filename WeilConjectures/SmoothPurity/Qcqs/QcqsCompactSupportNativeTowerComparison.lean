/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Compact.CompactSupportReductionTower
public import WeilConjectures.SmoothPurity.Compact.CompactSupportNativeSystemEvaluation
import all WeilConjectures.SmoothPurity.Compact.CompactSupportNativeTowerPresentation

/-!
# Comparison of the recorded and native compact-support towers, before total limit

## Implementation details

The native presentation of the chosen recorded tower from
`exists_compactSupportReductionTower` is retained. Both `S.reduction` and `SX.reduction` are left
adjoint to `coefficientSequenceLimit`, so uniqueness of left adjoints gives an isomorphism of
whole derived systems preserving the units. The `unit_projection` equations identify its finite
scalar-restriction transpose, and whiskering by native open extension, proper image and
completed restriction gives the displayed equation. No faithfulness of finite evaluation is
required.

## References

* [Bhatt--Scholze, *The pro-étale topology for schemes*, Definition 6.7.6]
* [Stacks Project, Tags 06YY, 0941 and 0A95]
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime]
  (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (K₀ : Type u) [Field K₀] (hl : IsUnit (l : K₀))
  {X Y : Scheme.{u}} {f : X ⟶ Y}
  [X.Over (Spec (.of K₀))] [Y.Over (Spec (.of K₀))]
  [LocallyOfFiniteType (X ↘ Spec (.of K₀))] [QuasiCompact (X ↘ Spec (.of K₀))]
  [LocallyOfFiniteType (Y ↘ Spec (.of K₀))] [QuasiCompact (Y ↘ Spec (.of K₀))]
  [f.IsOver (Spec (.of K₀))] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (c : Compactification f)

/-- The actual native composite before taking a total inverse limit. -/
private def nativeCompactSupportTower (S : CoefficientDerivedSystemCalculus l E X) :
    DerivedCategory (scalarReductionSource l E X) ⥤
      DerivedCategory (pbcTowers Y (completedIntegralCommRingSheafUnrestricted l E Y)) :=
  S.reduction ⋙
    ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.i ⋙
    ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g ⋙
    coefficientSequenceDerivedRestriction l E Y

/-- The canonical pasting of native finite evaluations, with its full type retained. -/
private def nativeCompactSupportTowerEvaluations (S : CoefficientDerivedSystemCalculus l E X) :
    ∀ n : ℕ, nativeCompactSupportTower l E c S ⋙
      pbcTowerEvaluation Y (completedIntegralCommRingSheafUnrestricted l E Y) n ≅
        compactSupportRestrictedLevel l E c n :=
  fun n ↦
    Functor.isoWhiskerLeft (S.reduction ⋙
        ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) c.i ⋙
        ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
          (compactSupportSystemQuotient l E) c.g)
        (coefficientRestrictedEvaluationIso l E Y n) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft S.reduction (compactSupportSystemEvaluation l E c n) ≪≫
          (Functor.associator _ _ _).symm ≪≫
          Functor.isoWhiskerRight (S.reductionEvaluation n) _) _

/-- The unique comparison of reduction left adjoints preserves finite evaluation. -/
private theorem reductionComparison_evaluation
    (S S' : CoefficientDerivedSystemCalculus l E X)
    (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ) :
    (coefficientSequenceDerivedEvaluation l E X n).map
        ((S.adjunction.leftAdjointUniq S'.adjunction).hom.app K) ≫
        (S'.reductionEvaluation n).hom.app K =
      (S.reductionEvaluation n).hom.app K := by
  let δ := S.adjunction.leftAdjointUniq S'.adjunction
  let V := coefficientSequenceDerivedEvaluation l E X n
  let a := coefficientFiniteAdjunction l E X n
  have h : (S.reductionEvaluation n).inv.app K ≫ V.map (δ.hom.app K) =
      (S'.reductionEvaluation n).inv.app K := by
    apply (a.homEquiv _ _).injective
    rw [a.homEquiv_unit, a.homEquiv_unit, Functor.map_comp, ← Category.assoc,
      ← S.unit_projection K n, Category.assoc]
    have hn := (coefficientSequenceProjection l E X n).naturality (δ.hom.app K)
    dsimp only [Functor.comp_map] at hn
    rw [← hn, ← Category.assoc,
      S.adjunction.unit_leftAdjointUniq_hom_app S'.adjunction K,
      S'.unit_projection K n]
  apply (cancel_epi ((S.reductionEvaluation n).inv.app K)).mp
  simp only [← Category.assoc, Iso.inv_hom_id_app]
  change ((S.reductionEvaluation n).inv.app K ≫ V.map (δ.hom.app K)) ≫
    (S'.reductionEvaluation n).hom.app K = 𝟙 _
  rw [h, Iso.inv_hom_id_app]

omit [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] in
/-- Transport the native reduction comparison through open extension and proper image. -/
private theorem nativePresentation_comparison
    (SX S : CoefficientDerivedSystemCalculus l E X)
    (T : DerivedCategory (scalarReductionSource l E X) ⥤
      coefficientSequenceRestrictedDerived l E Y)
    (eT : ∀ n : ℕ, T ⋙ coefficientConstantTowerEvaluation l E Y n ≅
      compactSupportRestrictedLevel l E c n)
    (hT : T = nativeCompactSupportTower l E c S)
    (heT : HEq eT (nativeCompactSupportTowerEvaluations l E c S)) :
    let N := SX.reduction ⋙ ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.i ⋙
      ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.g
    let e (n : ℕ) :=
      Functor.isoWhiskerLeft SX.reduction (compactSupportSystemEvaluation l E c n) ≪≫
        Functor.isoWhiskerRight (SX.reductionEvaluation n)
          (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))
    ∃ α : T ≅ N ⋙ coefficientSequenceDerivedRestriction l E Y,
      ∀ (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ),
        (coefficientConstantTowerEvaluation l E Y n).map (α.hom.app K) ≫
            (coefficientRestrictedEvaluationIso l E Y n).hom.app (N.obj K) ≫
            (coefficientFiniteDerivedRestriction l E Y n).map ((e n).hom.app K) =
          (eT n).hom.app K := by
  dsimp only [nativeCompactSupportTower] at hT
  dsimp only [nativeCompactSupportTower, nativeCompactSupportTowerEvaluations] at heT
  subst T
  cases eq_of_heq heT
  let G : coefficientSequenceDerived l E X ⥤ coefficientSequenceDerived l E Y :=
    ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.i ⋙
    ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
      (compactSupportSystemQuotient l E) c.g
  let U := coefficientSequenceDerivedRestriction l E Y
  let δ := S.adjunction.leftAdjointUniq SX.adjunction
  refine ⟨Functor.isoWhiskerRight δ (G ⋙ U), ?_⟩
  intro K n
  dsimp only [nativeCompactSupportTowerEvaluations, nativeCompactSupportTower,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Functor.map_comp, Category.id_comp]
  have hU := (coefficientRestrictedEvaluationIso l E Y n).hom.naturality
    (G.map (δ.hom.app K))
  have hδ := reductionComparison_evaluation l E S SX K n
  dsimp only [Functor.comp_map] at hU
  let F := sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1))
  let ε : G ⋙ coefficientSequenceDerivedEvaluation l E Y n ≅
      coefficientSequenceDerivedEvaluation l E X n ⋙ F :=
    compactSupportSystemEvaluation l E c n
  have hG := ε.hom.naturality (δ.hom.app K)
  dsimp only [Functor.comp_map] at hG
  change (coefficientConstantTowerEvaluation l E Y n).map
        (U.map (G.map (δ.hom.app K))) ≫
      (coefficientRestrictedEvaluationIso l E Y n).hom.app (G.obj (SX.reduction.obj K)) ≫
      (coefficientFiniteDerivedRestriction l E Y n).map (ε.hom.app (SX.reduction.obj K)) ≫
      (coefficientFiniteDerivedRestriction l E Y n).map
        (F.map ((SX.reductionEvaluation n).hom.app K)) =
    (coefficientRestrictedEvaluationIso l E Y n).hom.app (G.obj (S.reduction.obj K)) ≫
      (coefficientFiniteDerivedRestriction l E Y n).map (ε.hom.app (S.reduction.obj K)) ≫
      (coefficientFiniteDerivedRestriction l E Y n).map
        (F.map ((S.reductionEvaluation n).hom.app K))
  have hf := congrArg
    (fun z ↦ z ≫ F.map ((SX.reductionEvaluation n).hom.app K)) hG
  simp only [Category.assoc] at hf
  rw [← F.map_comp, hδ] at hf
  rw [reassoc_of% hU]
  simpa only [Functor.map_comp, Category.assoc] using congrArg
    (fun z ↦ (coefficientRestrictedEvaluationIso l E Y n).hom.app
      (G.obj (S.reduction.obj K)) ≫
        (coefficientFiniteDerivedRestriction l E Y n).map z) hf

-- Retain the original base-compatibility instance binder.
/-- Compare the whole recorded reduction tower with native proper/open reduction. -/
theorem qcqsCompactSupport_nativeTowerComparison
    (SX : CoefficientDerivedSystemCalculus l E X) :
    let hT := exists_compactSupportReductionTower l E K₀ X Y f hl c
    let T := hT.choose_spec.choose_spec.2.2.choose
    let eT := hT.choose_spec.choose_spec.2.2.choose_spec.2.choose_spec.2.choose
    let N := SX.reduction ⋙ ProEtale.VaryingRing.J (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.i ⋙
      ProEtale.VaryingRing.P (compactSupportSystemLevel l E)
        (compactSupportSystemQuotient l E) c.g
    let e (n : ℕ) :=
      Functor.isoWhiskerLeft SX.reduction (compactSupportSystemEvaluation l E c n) ≪≫
        Functor.isoWhiskerRight (SX.reductionEvaluation n)
          (sfIntrinsicCompactSupport c (Padic.coefficientExtensionRing l E (n + 1)))
    ∃ α : T ≅ N ⋙ coefficientSequenceDerivedRestriction l E Y,
      ∀ (K : DerivedCategory (scalarReductionSource l E X)) (n : ℕ),
        (coefficientConstantTowerEvaluation l E Y n).map (α.hom.app K) ≫
            (coefficientRestrictedEvaluationIso l E Y n).hom.app (N.obj K) ≫
            (coefficientFiniteDerivedRestriction l E Y n).map ((e n).hom.app K) =
          (eT n).hom.app K := by
  let H := exists_compactSupportReductionTower l E K₀ X Y f hl c
  have h := H.choose_spec.choose_spec.2.2.choose_spec.2.choose_spec.2.choose_spec.2
  unfold IsNativeCompactSupportTowerPresentation at h
  obtain ⟨S, hS, heS⟩ := h
  with_unfolding_all
    exact nativePresentation_comparison l E c SX S _ _ hS heS

end WeilConjectures
