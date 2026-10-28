/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q8 and E7
-/
module

public import Sheaf.SixFunctors.IntegralDualizingMappingTower
import all Sheaf.Paper.NormalizedDVREffectivity
import all Sheaf.Paper.CoefficientSequenceRoosModel
import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Sheaf.CategoryTheory.NormalizedDVRTowerEvaluationFull

/-! # A quotient-system realization of one normalized DVR tower -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures

attribute [local implicit_reducible] completedIntegralCoefficientSheaf
  completedIntegralCommRingSheafUnrestricted
  coefficientFiniteDerivedExtension coefficientFiniteDerivedRestriction
  coefficientConstantTowerEvaluation
attribute [local irreducible] completedIntegralCoefficientSheafUnrestricted

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

private theorem transportTransition
    {A B : Type*} [Category A] [Category B] (R : B ⥤ A)
    {Pm Am Bm : A} {Pn An Bn : B}
    (cm : Am ≅ Pm) (cn : An ≅ Pn) (dm : Am ≅ Bm) (dn : An ≅ Bn)
    (f : Pm ⟶ R.obj Pn) (r : Am ⟶ R.obj An) (t : Bm ⟶ R.obj Bn)
    (hc : cm.hom ≫ f = r ≫ R.map cn.hom)
    (hd : dm.hom ≫ t = r ≫ R.map dn.hom) :
    f ≫ R.map (cn.inv ≫ dn.hom) = (cm.inv ≫ dm.hom) ≫ t := by
  apply (cancel_epi cm.hom).1
  calc
    cm.hom ≫ f ≫ R.map (cn.inv ≫ dn.hom) =
        r ≫ R.map (cn.hom ≫ cn.inv ≫ dn.hom) := by
      rw [← Category.assoc cm.hom f, hc]
      simp only [Functor.map_comp, Category.assoc]
    _ = r ≫ R.map dn.hom := by rw [cn.hom_inv_id_assoc]
    _ = dm.hom ≫ t := hd.symm
    _ = cm.hom ≫ (cm.inv ≫ dm.hom) ≫ t := by
      simp only [Category.assoc, cm.hom_inv_id_assoc]

private theorem towerIso
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : NormalizedDVRTower l E X D hl)
    (N : coefficientSequenceDerived l E X)
    (a : ∀ n : ℕ, T.M n ≅ (coefficientSequenceDerivedEvaluation l E X n).obj N)
    (ha : ∀ {m n : ℕ} (h : n ≤ m),
      T.tau h ≫ (normalizedDVRRes l E X h).map (a n).hom =
        (a m).hom ≫ (coefficientSequenceDerivedTransition l E X h).app N) :
    Nonempty (T.tower ≅ (coefficientSequenceDerivedRestriction l E X).obj N) := by
  let e (n : ℕ) := T.evaluationIso n ≪≫
    (normalizedDVRResCompleted l E X D hl n).mapIso (a n) ≪≫
      ((coefficientRestrictedEvaluationIso l E X n).app N).symm
  have he (n : ℕ) : (e (n + 1)).hom ≫
      (normalizedDVRTowerTransition l E X D hl n.le_succ).app
        ((coefficientSequenceDerivedRestriction l E X).obj N) =
      (normalizedDVRTowerTransition l E X D hl n.le_succ).app T.tower ≫ (e n).hom := by
    apply (cancel_mono ((coefficientRestrictedEvaluationIso l E X n).hom.app N)).1
    dsimp only [e, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Iso.app_inv,
      Functor.mapIso_hom]
    simp only [Category.assoc, derivedRestrictedTransition l E X D hl N n.le_succ,
      Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app]
    rw [← Category.assoc _ (T.evaluationIso n).hom, T.tower_tau]
    simp only [Category.assoc]
    have hn := (normalizedDVRResCompletedComp l E X D hl n.le_succ).hom.naturality
      (a n).hom
    dsimp only [Functor.comp_map] at hn
    erw [← reassoc_of% hn]
    rw [← Functor.map_comp_assoc, ← ha, Functor.map_comp]
    simp only [Category.assoc]
    erw [Category.comp_id]
  obtain ⟨g, hg⟩ := normalizedDVRTowerEvaluation_full l E X D hl T.tower
    ((coefficientSequenceDerivedRestriction l E X).obj N) (fun n ↦ (e n).hom) he
  have hEval (n : ℕ) : IsIso ((normalizedDVRTowerEvaluation l E X D hl n).map g) := by
    rw [hg]
    infer_instance
  have : IsIso g := by
    rw [DerivedCategory.isIso_iff]
    intro j
    let : ∀ n : ℕᵒᵖ, IsIso (((DerivedCategory.homologyFunctor _ j).map g).app n) :=
      fun n ↦ by
        have := hEval n.unop
        let V := (evaluation ℕᵒᵖ (completedIntegralModuleSheaves l E X D hl)).obj n
        exact (NatIso.isIso_map_iff (V.mapDerivedCategoryHomologyFunctorIso j) g).2
          (show IsIso ((DerivedCategory.homologyFunctor _ j).map
            ((normalizedDVRTowerEvaluation l E X D hl n.unop).map g)) from inferInstance)
    exact NatIso.isIso_of_isIso_app _
  exact ⟨asIso g⟩

private theorem projectionTransition
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (N : coefficientSequenceDerived l E X) {m n : ℕ} (h : n ≤ m) :
    (coefficientSequenceProjection l E X m).app N ≫
      (normalizedDVRResCompleted l E X D hl m).map
        ((coefficientSequenceDerivedTransition l E X h).app N) ≫
      (normalizedDVRResCompletedComp l E X D hl h).hom.app
        ((coefficientSequenceDerivedEvaluation l E X n).obj N) =
      (coefficientSequenceProjection l E X n).app N := by
  let Y := (coefficientSequenceDerivedRestriction l E X).obj N
  obtain ⟨hp, δ, hδ⟩ := coefficientConstantTower_roos l E X D hl Y
  let := hp
  have ht : (coefficientConstantTowerProjection l E X m).app Y ≫
      (normalizedDVRTowerTransition l E X D hl h).app Y =
      (coefficientConstantTowerProjection l E X n).app Y := by
    induction m, h using Nat.le_induction with
    | base =>
      simp only [normalizedDVRTransition_refl, NatTrans.id_app]
      erw [Category.comp_id]
    | succ m h ih =>
      rw [← normalizedDVRTransition_comp l E X D hl m.le_succ h, NatTrans.comp_app]
      have hs := adjacentRoosProjection _ _ _ δ hδ m
      simp only [Pi.lift_π_assoc, Pi.lift_π] at hs
      rw [← Category.assoc, hs, ih]
  change ((coefficientConstantTowerProjection l E X m).app Y ≫
    (coefficientRestrictedEvaluationIso l E X m).hom.app N) ≫ _ ≫ _ =
    (coefficientConstantTowerProjection l E X n).app Y ≫
      (coefficientRestrictedEvaluationIso l E X n).hom.app N
  rw [Category.assoc, ← derivedRestrictedTransition l E X D hl N h]
  rw [← Category.assoc, ht]

private theorem reductionTransition
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (S : CoefficientDerivedSystemCalculus l E X)
    (K : DerivedCategory (scalarReductionSource l E X)) {m n : ℕ} (h : n ≤ m) :
    (S.reductionEvaluation m).inv.app K ≫
      (coefficientSequenceDerivedTransition l E X h).app (S.reduction.obj K) =
      normalizedDVRReductionTransition l E X D hl h K ≫
        (normalizedDVRRes l E X h).map ((S.reductionEvaluation n).inv.app K) := by
  have ht := adjointTransition (coefficientFiniteAdjunction l E X m)
    (coefficientFiniteAdjunction l E X n) (normalizedDVRRes l E X h)
    (normalizedDVRResCompletedComp l E X D hl h)
    (S.adjunction.unit.app K ≫
      (coefficientSequenceProjection l E X m).app (S.reduction.obj K))
    (S.adjunction.unit.app K ≫
      (coefficientSequenceProjection l E X n).app (S.reduction.obj K))
    ((coefficientSequenceDerivedTransition l E X h).app (S.reduction.obj K)) (by
      have hp := projectionTransition l E X D hl (S.reduction.obj K) h
      change (coefficientSequenceProjection l E X m).app (S.reduction.obj K) ≫
        (coefficientFiniteDerivedRestriction l E X m).map
          ((coefficientSequenceDerivedTransition l E X h).app (S.reduction.obj K)) ≫
        (normalizedDVRResCompletedComp l E X D hl h).hom.app _ = _ at hp
      simpa only [Category.assoc] using congrArg
        (fun f ↦ S.adjunction.unit.app K ≫ f) hp)
  have ha (j : ℕ) : ((coefficientFiniteAdjunction l E X j).homEquiv _ _).symm
      (S.adjunction.unit.app K ≫
        (coefficientSequenceProjection l E X j).app (S.reduction.obj K)) =
      (S.reductionEvaluation j).inv.app K := by
    apply ((coefficientFiniteAdjunction l E X j).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    exact S.unit_projection K j
  rw [ha, ha] at ht
  exact ht

/-- A normalized DVR derived tower has a strict quotient-system representative,
whose completed restriction is isomorphic to the given strict tower.

Source: blueprint prop-coef-integral-dualizing, second paragraph, first mapping
comparison; Stacks 079P and 070I.
(blueprint: lem-coef-normalized-dvr-quotient-system-realization).

Proof: form the canonical Roos limit M of the given completed tower. DVR effectivity
identifies every finite derived scalar extension of M with T.M n, compatibly with all
quotient transitions. Apply the coefficient-system reduction functor to M. Its finite
evaluation isomorphisms identify its levels with the same derived scalar extensions.
To compare transitions, the Roos triangle gives the successor projection equation;
induction gives every longer equation and the identity equation. The reduction
adjunction's unit-projection formula then identifies the transition mates. Compose
these evaluation isomorphisms with the inverses of the effectivity comparisons.
Choose a complex Q representing the resulting derived quotient system and transport
the finite isomorphisms along its localization isomorphism, using naturality of the
localized transitions. After completed restriction the finite isomorphisms commute
with the tower maps by the canonical restriction-composition square and T.tower_tau.
Sequential tower fullness lifts this fixed compatible family. Evaluation commutes
with homology, so the lift is an isomorphism. This route uses normalization through
DVR effectivity; it imposes no boundedness, constructibility or flatness hypothesis. -/
theorem normalizedDVR_quotient_system_realization
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    (T : NormalizedDVRTower l E X D hl) :
    ∃ (Q : CochainComplex (coefficientSequenceModules l E X) ℤ)
      (a : ∀ n : ℕ, T.M n ≅
        (coefficientSequenceDerivedEvaluation l E X n).obj (coefTraceInput l E X Q)),
      (∀ {m n : ℕ} (h : n ≤ m),
        T.tau h ≫ (normalizedDVRRes l E X h).map (a n).hom =
          (a m).hom ≫ (coefficientSequenceDerivedTransition l E X h).app
            (coefTraceInput l E X Q)) ∧
      Nonempty (T.tower ≅ (coefficientSequenceDerivedRestriction l E X).obj
        (coefTraceInput l E X Q)) := by
  obtain ⟨hp, δ, hδ⟩ := coefficientConstantTower_roos l E X D hl T.tower
  have hpDVR : HasProduct (fun n : ℕ ↦
      (normalizedDVRTowerEvaluation l E X D hl n).obj T.tower) := hp
  let := hpDVR
  let M : completedIntegralDerivedCategory l E X D hl :=
    (coefficientConstantTowerLimit l E X).obj T.tower
  let p := Pi.lift (fun n : ℕ ↦ (coefficientConstantTowerProjection l E X n).app T.tower)
  have heff := normalizedDVRTower_effectivity l E X D hl T M p δ hδ
  obtain ⟨S, _⟩ := coefficientDerivedSystemEvaluationCalculus l E X
  let N := S.reduction.obj M
  let c (n : ℕ) := @asIso _ _ _ _
    (normalizedDVRCounitComparison l E X D hl T M p n) (heff.1 n)
  let b (n : ℕ) := (c n).symm ≪≫ ((S.reductionEvaluation n).app M).symm
  have hb {m n : ℕ} (h : n ≤ m) :
      T.tau h ≫ (normalizedDVRRes l E X h).map (b n).hom =
        (b m).hom ≫ (coefficientSequenceDerivedTransition l E X h).app N := by
    exact transportTransition (normalizedDVRRes l E X h) (c m) (c n)
      (((S.reductionEvaluation m).app M).symm) (((S.reductionEvaluation n).app M).symm)
      (T.tau h) (normalizedDVRReductionTransition l E X D hl h M)
      ((coefficientSequenceDerivedTransition l E X h).app N)
      (heff.2.1 h) (reductionTransition l E X D hl S M h)
  let Q := DerivedCategory.Q.objPreimage N
  let q : coefTraceInput l E X Q ≅ N := DerivedCategory.Q.objObjPreimageIso N
  let a (n : ℕ) := b n ≪≫
    (coefficientSequenceDerivedEvaluation l E X n).mapIso q.symm
  have ha {m n : ℕ} (h : n ≤ m) :
      T.tau h ≫ (normalizedDVRRes l E X h).map (a n).hom =
        (a m).hom ≫ (coefficientSequenceDerivedTransition l E X h).app
          (coefTraceInput l E X Q) := by
    dsimp only [a, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rw [Functor.map_comp, ← Category.assoc, hb, Category.assoc]
    have hn := (coefficientSequenceDerivedTransition l E X h).naturality q.inv
    dsimp only [Functor.comp_map] at hn
    rw [← hn, Category.assoc]
  exact ⟨Q, a, ha, towerIso l E X D hl T _ a ha⟩

end WeilConjectures
