/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.Paper.PerfectQuotientExchangePresentation
import Sheaf.Paper.QuotientExchangeDiagramNormalization
import Sheaf.Paper.PerfectStrictReductionProjection
import Sheaf.Paper.StrictReductionProjectionCompletionUnit
import Sheaf.Paper.FlatRingedIdealCompleteEquivalence

/-! # Perfect quotient coefficient exchange

Source: Stacks Project, Tags 0944, 0B56, 07A6, 0D6E, 0941 and 0A07.
(blueprint: lem-pur-perfect-quotient-exchange-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.proofsInPublic true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion

namespace CategoryTheory.AdicSites.PerfectQuotientExchange

variable {Y X : Site.{u}} {f : Morphism Y X} {A : Type u} [CommRing A] {I : Ideal A}
  (p : Presentation f A I)

private theorem strictExchange_app (F : X.derived A) :
    (strictExchange p).app F =
      p.reductionY.tower.hom.app ((f.push A).obj F) ≫
        f.towerProjection A I F ≫
          (f.towerPush A).map (p.reductionX.tower.inv.app F) := by
  dsimp only [strictExchange, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  congr 1
  congr 1
  unfold Morphism.towerProjection
  exact ((f.towerAdjunction A).homEquiv _ _).symm_apply_eq.mp
    (mateEquiv_counit (f.adj A) (f.towerAdjunction A)
      (TwoSquare.mk _ _ _ _ (f.reductionPullIso A I).hom) F)

private theorem completionExchange_eq (F : X.derived A) :
    completionExchange p F =
      (Y.rlim A).map (f.towerProjection A I F) ≫
        (f.directLimitIso A).inv.app ((X.reduction A I).obj F) := by
  rw [completionExchange, strictExchange_app]
  have hn := (f.directLimitIso A).inv.naturality (p.reductionX.tower.inv.app F)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn]
  simp only [← Functor.map_comp, ← Category.assoc, Iso.inv_hom_id_app,
    Functor.map_id, Category.id_comp, Category.comp_id]

/-- Perfect quotients give the canonical strict quotient coefficient exchange,
its quotient-linear evaluations, and its completion-unit normalization.

Source: Stacks Project, sites-cohomology.tex, Tags 0944 (projection formula),
0B56 (projection map), 07A6 (derived adjunction), 0D6E (derived composition),
0941 and 0A07 (strict derived limits); agent strict coefficient-exchange auxiliary
(blueprint: lem-pur-perfect-quotient-exchange-normalization).

Proof:
1. quotientExchangeDiagramNormalization constructs p and d, with all ordinary and
full-cochain normalizations and both strict and finite evaluation identities.
2. The counit mate equation factors strictExchange through towerProjection and the
two reduction-tower comparisons. perfectStrictReductionProjection makes this whole
strict morphism invertible. The equation with d makes scalar restriction of exchange
invertible. Exact conservative derived restriction reflects this property, giving
invertibility of exchange. Its quotient evaluations preserve isomorphisms.
3. Substitute the same factorization into completionExchange. Naturality of
directLimitIso and cancellation of the reduction-tower comparisons identify it
with Rlim(towerProjection) followed by directLimitIso inverse. The theorem
strictReductionProjectionCompletionUnit gives exactly the asserted unit equation. -/
theorem perfectQuotientExchangeNormalization [IsNoetherianRing A]
    (hperfect : PerfectQuotients A I) :
    ∃ (p : Presentation f A I)
      (d : p.push.rightDerivedFunctor ⋙ p.atY.restrictionD ≅
        p.atX.restrictionD ⋙ f.towerPush A),
      PresentationNormalized f A I p ∧
      d.hom = restrictionMate p ∧
      (∀ F : X.derived A,
        p.atY.restrictionD.map ((exchange p).app F) ≫
            d.hom.app (p.atX.reductionD.obj F) = (strictExchange p).app F) ∧
      (∀ (F : X.derived A) (n : ℕ),
        (finiteExchange p n).app F = f.finiteProjection A I n F) ∧
      (∀ (F : X.derived A) (n : ℕ),
        (Y.evaluate A n).map ((strictExchange p).app F) ≫
            (Y.evaluate A n).map
              ((f.towerPush A).map (p.reductionX.tower.hom.app F)) ≫
            (f.evaluatePushIso A n).hom.app ((X.reduction A I).obj F) ≫
            (f.push A).map ((X.finiteEvaluationIso A I n).hom.app F) ≫
            (f.finiteRestrictionPushIso A I n).hom.app ((X.finiteReduction A I n).obj F) =
          (Y.evaluate A n).map (p.reductionY.tower.hom.app ((f.push A).obj F)) ≫
            (Y.finiteEvaluationIso A I n).hom.app ((f.push A).obj F) ≫
            (Y.finiteRestriction A I n).map ((finiteExchange p n).app F)) ∧
      IsIso (exchange p) ∧ (∀ n : ℕ, IsIso (finiteExchange p n)) ∧
      (∀ F : X.derived A,
        (Y.unit A I).app ((f.push A).obj F) ≫ completionExchange p F =
          (f.push A).map ((X.unit A I).app F)) := by
  obtain ⟨p, d, hp, hd, hs, hf, he⟩ :=
    quotientExchangeDiagramNormalization f A I
  have ht (F : X.derived A) : IsIso ((strictExchange p).app F) := by
    have := perfectStrictReductionProjection f A I hperfect F
    rw [strictExchange_app]
    infer_instance
  have hx (F : X.derived A) : IsIso ((exchange p).app F) := by
    have : IsIso (p.atY.restrictionD.map ((exchange p).app F) ≫
        d.hom.app (p.atX.reductionD.obj F)) := by
      rw [hs]
      exact ht F
    have : IsIso (p.atY.restrictionD.map ((exchange p).app F)) :=
      (isIso_comp_right_iff _ (d.hom.app (p.atX.reductionD.obj F))).mp inferInstance
    unfold StrictQuotientDiagonalPresentation.restrictionD at this
    rw [p.atY.restrictionModel_eq] at this
    have hres := this
    have : (res p.atY.ringMap).mapDerivedCategory.ReflectsIsomorphisms :=
      siteDerivedRestrictScalars_reflectsIsomorphisms p.atY.ringMap
    have : p.atY.towers.functor.mapDerivedCategory.ReflectsIsomorphisms := inferInstance
    have : IsIso (p.atY.towers.functor.mapDerivedCategory.map
        ((res p.atY.ringMap).mapDerivedCategory.map ((exchange p).app F))) := hres
    have : IsIso ((res p.atY.ringMap).mapDerivedCategory.map ((exchange p).app F)) :=
      isIso_of_reflects_iso _ p.atY.towers.functor.mapDerivedCategory
    exact isIso_of_reflects_iso _ (res p.atY.ringMap).mapDerivedCategory
  have : IsIso (exchange p) := NatIso.isIso_of_isIso_app (exchange p)
  refine ⟨p, d, hp, hd, hs, hf, he, inferInstance, ?_, ?_⟩
  · intro n
    unfold finiteExchange
    infer_instance
  · intro F
    rw [completionExchange_eq]
    exact strictReductionProjectionCompletionUnit f A I F

end CategoryTheory.AdicSites.PerfectQuotientExchange
