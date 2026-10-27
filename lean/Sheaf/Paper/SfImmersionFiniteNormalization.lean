/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Sheaf.Paper.CompletedPullback
public import Sheaf.CategoryTheory.RingedConstantTowerPushforwardNormalization
import Sheaf.Paper.LevelwiseAdicTruncations
import Sheaf.Paper.PbcActualStrictPullback
import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
import all Sheaf.Paper.CompletedTowerPullback
import all Sheaf.Paper.WeilTensorProduct
import Sheaf.Paper.WeilCompletedTensorReflector
import all Sheaf.CategoryTheory.ExactTowerAugmentedCounitEvaluation
import all Sheaf.Paper.CompletedDirectImageLimits
import all Sheaf.Paper.ReductionAugmentationCompatibility
import all Sheaf.Paper.StratumCompletionUnitRestriction
import all Sheaf.Paper.AdicCoefficientDatum
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Normalized finite evaluations of strict quotient towers

The generic adic-datum calculations used by the immersion pullback comparison.
Source: localization Step 6; Stacks 03EL, 06YY and 0941.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.ProEtale WeilConjectures
attribute [-instance] CategoryTheory.ringedConstantTowerModulesAbelian
attribute [-instance] CategoryTheory.ringedConstantTowerTowersAbelian
attribute [-instance] CategoryTheory.ringedConstantTowerAdditive
attribute [-instance] CategoryTheory.strictTowerConstantAdditive
attribute [-instance] CategoryTheory.strictTowerLimitAdditive
attribute [local irreducible] AlgebraicGeometry.Scheme.AdicCoefficients.ringSystem
  CategoryTheory.Limits.limit HasDerivedCategory.standard
namespace AlgebraicGeometry.Scheme

private theorem finite_square_component
    {C₁ C₂ D₁ D₂ : Type*} [Category C₁] [Category C₂] [Category D₁] [Category D₂]
    (L₁ : C₁ ⥤ D₁) (R₁ : D₁ ⥤ C₁) (L₂ : C₂ ⥤ D₂) (R₂ : D₂ ⥤ C₂)
    (G : C₁ ⥤ C₂) (H : D₁ ⥤ D₂) (e : R₁ ⋙ G ≅ H ⋙ R₂)
    (χ : L₁ ⋙ H ≅ G ⋙ L₂) (K : C₁) :
    ((Functor.associator L₁ R₁ G ≪≫ isoWhiskerLeft L₁ e ≪≫
      (Functor.associator L₁ H R₂).symm ≪≫ isoWhiskerRight χ R₂ ≪≫
      Functor.associator G L₂ R₂).hom.app K) =
      e.hom.app (L₁.obj K) ≫ R₂.map (χ.hom.app K) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id]

section GenericFinite

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  {X Y : Scheme.{u}} (f : Y ⟶ X)

private abbrev generic_restrictedReduction (T : Scheme.{u}) (n : ℕ) :=
  d.reduction T n ⋙
    pbcDerivedRestrict (d.projection T n)

private def generic_reductionUnit (T : Scheme.{u}) (n : ℕ) :=
  (pbcDerivedScalarAdjunction (d.projection T n)).unit

private def generic_reductionTransition (T : Scheme.{u}) (b a : ℕ) (h : a ≤ b)
    (K : PbcCompletedDerived T d) :
    (generic_restrictedReduction d T b).obj K ⟶ (generic_restrictedReduction d T a).obj K :=
  (pbcDerivedRestrict (pbcAdicProjection T d b)).map
      (pbcReductionTransition (pbcAdicProjection T d b)
        (pbcAdicQuotient T d b a h)
        (pbcAdicProjection T d a)
        (pbcAdicProjection_comp T d b a h) K) ≫
    (pbcDerivedRestrictComp (pbcAdicProjection T d b)
      (pbcAdicQuotient T d b a h)
      (pbcAdicProjection T d a)
      (pbcAdicProjection_comp T d b a h)).hom.app
        ((d.reduction T a).obj K)

private def generic_restrictedComparison (n : ℕ) :
    generic_restrictedReduction d X n ⋙ d.pull f ≅
      d.pull f ⋙ generic_restrictedReduction d Y n :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (d.reduction X n)
      (proEtaleRingRestrictionDerivedPullback f _ _ _ _
        (d.projection X n) (d.projection Y n)
        (d.integralRingIso f)
        (d.finiteRingIso f n)
        (d.projection_comm f n)).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (d.chi f n)
      (pbcDerivedRestrict (d.projection Y n)) ≪≫
    Functor.associator _ _ _

attribute [local irreducible] reductionChange reductionDerivedChange
attribute [local irreducible] Functor.mapHomotopyCategory
attribute [local irreducible] Functor.mapHomotopyCategoryFactors
attribute [local irreducible] completedReductionModuleTowerFunctor completedReductionTower
attribute [local irreducible] Functor.mapDerivedCategory
attribute [local irreducible] Functor.mapDerivedCategoryFactors
attribute [local irreducible] Functor.mapDerivedCategoryFactorsh

private theorem generic_restrictedComparison_app (n : ℕ)
    (K : PbcCompletedDerived X d) :
    (generic_restrictedComparison d f n).hom.app K =
      (proEtaleRingRestrictionDerivedPullback f _ _ _ _
        (d.projection X n) (d.projection Y n)
        (d.integralRingIso f)
        (d.finiteRingIso f n)
        (d.projection_comm f n)).inv.app
          ((d.reduction X n).obj K) ≫
      (pbcDerivedRestrict (d.projection Y n)).map
        ((d.chi f n).hom.app K) := by
  exact finite_square_component _ _ _ _ _ _ _ _ K

private theorem conjugate_comp
    {C : Type*} [Category C] {A₀ A₁ A₂ B₀ B₁ B₂ : C}
    (e₀ : A₀ ⟶ B₀) (e₁ : A₁ ⟶ B₁) (e₂ : A₂ ⟶ B₂)
    (f : A₀ ⟶ A₁) (g : A₁ ⟶ A₂) (h : A₀ ⟶ A₂)
    (f' : B₀ ⟶ B₁) (g' : B₁ ⟶ B₂) (h' : B₀ ⟶ B₂)
    [Epi e₀] (hf : e₀ ≫ f' = f ≫ e₁) (hg : e₁ ≫ g' = g ≫ e₂)
    (hh : e₀ ≫ h' = h ≫ e₂) (hfg : f ≫ g = h) : f' ≫ g' = h' := by
  apply (cancel_epi e₀).1
  calc
    e₀ ≫ (f' ≫ g') = f ≫ (e₁ ≫ g') := by rw [← Category.assoc, hf, Category.assoc]
    _ = h ≫ e₂ := by rw [hg, ← Category.assoc, hfg]
    _ = e₀ ≫ h' := hh.symm

private theorem conjugate_square
    {C : Type*} [Category C] {P Q S T U V : C}
    (p : P ⟶ Q) (q : S ⟶ T) (a : Q ⟶ T) (b : U ⟶ V)
    (x : Q ⟶ U) (y : T ⟶ V) (c : P ⟶ S) (d : P ⟶ U) (e : S ⟶ V)
    [Epi p] (hp : c ≫ q = p ≫ a) (hx : p ≫ x = d) (hy : q ≫ y = e)
    (hc : c ≫ e = d ≫ b) : a ≫ y = x ≫ b := by
  apply (cancel_epi p).1
  calc
    p ≫ (a ≫ y) = c ≫ (q ≫ y) := by rw [← Category.assoc, ← hp, Category.assoc]
    _ = d ≫ b := by rw [hy, hc]
    _ = p ≫ (x ≫ b) := by rw [← hx, Category.assoc]

private theorem generic_finite_unit (K : PbcCompletedDerived X d) (n : ℕ) :
    (d.pull f).map ((generic_reductionUnit d X n).app K) ≫
        (generic_restrictedComparison d f n).hom.app K =
      (generic_reductionUnit d Y n).app ((d.pull f).obj K) := by
  let e := proEtaleRingRestrictionDerivedPullback f _ _ _ _
    (d.projection X n) (d.projection Y n) (d.integralRingIso f)
    (d.finiteRingIso f n) (d.projection_comm f n)
  have h : (d.pull f).map ((generic_reductionUnit d X n).app K) ≫
        e.inv.app ((d.reduction X n).obj K) =
      (generic_reductionUnit d Y n).app ((d.pull f).obj K) ≫
        (pbcDerivedRestrict (d.projection Y n)).map ((d.chi f n).inv.app K) := by
    exact unit_mateEquiv_symm (pbcDerivedScalarAdjunction (d.projection X n))
      (pbcDerivedScalarAdjunction (d.projection Y n))
      (TwoSquare.mk _ _ _ _ e.inv) K
  rw [generic_restrictedComparison_app]
  calc
    (d.pull f).map ((generic_reductionUnit d X n).app K) ≫
        e.inv.app ((d.reduction X n).obj K) ≫
        (pbcDerivedRestrict (d.projection Y n)).map ((d.chi f n).hom.app K) =
      ((generic_reductionUnit d Y n).app ((d.pull f).obj K) ≫
        (pbcDerivedRestrict (d.projection Y n)).map ((d.chi f n).inv.app K)) ≫
        (pbcDerivedRestrict (d.projection Y n)).map ((d.chi f n).hom.app K) := by
          rw [← Category.assoc, h]
    _ = _ := by
      rw [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
      erw [CategoryTheory.Functor.map_id, Category.comp_id]


private theorem strict_transition_comp
    {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A]
    [HasDerivedCategory (ℕᵒᵖ ⥤ A)] {i j k : ℕᵒᵖ} (a : i ⟶ j) (b : j ⟶ k) :
    towerDerivedEvaluationTransition A a ≫ towerDerivedEvaluationTransition A b =
      towerDerivedEvaluationTransition A (a ≫ b) := by
  simp only [towerDerivedEvaluationTransition, Localization.comp_liftNatTrans,
    ← Functor.whiskerRight_comp, ← NatTrans.mapHomologicalComplex_comp,
    ← CategoryTheory.Functor.map_comp]

private theorem generic_evaluation_transition (T : Scheme.{u})
    (K : PbcCompletedDerived T d) (b a : ℕ) (h : a ≤ b) :
    (completedReductionEvaluation T d b).app K ≫
        generic_reductionTransition d T b a h K =
      (pbcTowerTransition T (pbcAdicCompletion T d) b a h).app
          ((completedReductionTower T d).obj K) ≫
        (completedReductionEvaluation T d a).app K := by
  have ht : adicTowerSemilinearTransition T d
      (fun n ↦ (pbcCompletedReduction T d n).obj K)
      (fun b a hab ↦ pbcReductionNormalization (pbcAdicProjection T d b)
        (pbcAdicQuotient T d b a hab) (pbcAdicProjection T d a)
        (pbcAdicProjection_comp T d b a hab) K) b a h =
      pbcReductionTransition (pbcAdicProjection T d b) (pbcAdicQuotient T d b a h)
        (pbcAdicProjection T d a) (pbcAdicProjection_comp T d b a h) K := by
    change ((pbcDerivedScalarAdjunction (pbcAdicQuotient T d b a h)).homEquiv _ _)
      (((pbcDerivedScalarAdjunction (pbcAdicQuotient T d b a h)).homEquiv _ _).symm
        (pbcReductionTransition (pbcAdicProjection T d b) (pbcAdicQuotient T d b a h)
          (pbcAdicProjection T d a) (pbcAdicProjection_comp T d b a h) K)) = _
    exact Equiv.apply_symm_apply _ _
  let e (n : ℕ) := (asIso (completedReductionEvaluation T d n)).app K
  let q := (pbcTowerTransition T (pbcAdicCompletion T d) b a h).app
    ((completedReductionTower T d).obj K)
  have hs : generic_reductionTransition d T b a h K ≫ (e a).inv = (e b).inv ≫ q := by
    have hi := (pbc_reduction_adic_tower_laws T d K).1 b a h
    rw [ht] at hi
    simpa only [generic_reductionTransition, pbcReductionEvaluationIso, e, q,
      Iso.symm_hom, Iso.app_hom, Iso.app_inv, Category.assoc,
      pbcCompletedReduction, pbcDerivedExtend, AdicCoefficientDatum.reduction,
      AdicCoefficientDatum.projection, completedReductionProjection, pbcAdicProjection,
      pbcAdicRings, reductionCoefficientSystem, AdicCoefficients.completedRing,
      completedReductionCoefficient, pbcTowerEvaluation, reductionTowerDerivedEvaluation,
      reductionTowerEvaluation] using hi
  change (e b).hom ≫ generic_reductionTransition d T b a h K = q ≫ (e a).hom
  apply (cancel_mono (e a).inv).1
  calc
    ((e b).hom ≫ generic_reductionTransition d T b a h K) ≫ (e a).inv =
        (e b).hom ≫ ((e b).inv ≫ q) := by rw [Category.assoc, hs]
    _ = q := by rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    _ = (q ≫ (e a).hom) ≫ (e a).inv := by
      rw [Category.assoc, Iso.hom_inv_id, Category.comp_id]

private theorem generic_finite_cocycle (T : Scheme.{u}) (K : PbcCompletedDerived T d)
    (c b a : ℕ) (hab : a ≤ b) (hbc : b ≤ c) :
    generic_reductionTransition d T c b hbc K ≫ generic_reductionTransition d T b a hab K =
      generic_reductionTransition d T c a (hab.trans hbc) K := by
  let M := (completedReductionTower T d).obj K
  let e (n : ℕ) := (completedReductionEvaluation T d n).app K
  let q (b a : ℕ) (h : a ≤ b) :=
    (pbcTowerTransition T (pbcAdicCompletion T d) b a h).app M
  have he (j i : ℕ) (hij : i ≤ j) :
      e j ≫ generic_reductionTransition d T j i hij K = q j i hij ≫ e i :=
    generic_evaluation_transition d T K j i hij
  have hq : q c b hbc ≫ q b a hab = q c a (hab.trans hbc) := by
    have hh := congr_app (strict_transition_comp
      (A := pbcModules T (pbcAdicCompletion T d)) (homOfLE hbc).op (homOfLE hab).op) M
    have hi : (homOfLE hbc).op ≫ (homOfLE hab).op =
        (homOfLE (hab.trans hbc)).op := Subsingleton.elim _ _
    rw [hi] at hh
    exact hh
  exact conjugate_comp (e c) (e b) (e a) (q c b hbc) (q b a hab)
    (q c a (hab.trans hbc))
    (generic_reductionTransition d T c b hbc K) (generic_reductionTransition d T b a hab K)
    (generic_reductionTransition d T c a (hab.trans hbc) K)
    (he c b hbc) (he b a hab) (he c a (hab.trans hbc)) hq

private theorem generic_finite_transition (K : PbcCompletedDerived X d)
    (b a : ℕ) (h : a ≤ b) :
    (d.pull f).map (generic_reductionTransition d X b a h K) ≫
        (generic_restrictedComparison d f a).hom.app K =
      (generic_restrictedComparison d f b).hom.app K ≫
        generic_reductionTransition d Y b a h ((d.pull f).obj K) := by
  let F := d.pull f
  let M := (completedReductionTower X d).obj K
  let N := (completedReductionTower Y d).obj (F.obj K)
  let t := (stratumReductionIso d f).hom.app K
  let eX (n : ℕ) := (completedReductionEvaluation X d n).app K
  let eY (n : ℕ) := (completedReductionEvaluation Y d n).app (F.obj K)
  let v (n : ℕ) := (stratumTowerEvaluationIso d f n).hom.app M
  let c (n : ℕ) := (generic_restrictedComparison d f n).hom.app K
  let u (n : ℕ) := v n ≫ F.map (eX n)
  let qX := (pbcTowerTransition X (pbcAdicCompletion X d) b a h).app M
  let qY := (pbcTowerTransition Y (pbcAdicCompletion Y d) b a h).app N
  let qF := (pbcTowerTransition Y (pbcAdicCompletion Y d) b a h).app
    ((d.towerPull f).obj M)
  let evY (n : ℕ) := reductionTowerDerivedEvaluation Y
    (reductionModuleRing Y (d.completedRing Y)) n
  have he (n : ℕ) : u n ≫ c n = (evY n).map t ≫ eY n := by
    have hs := (stratumReduction_evaluation d f n K).symm
    simp only [u, c, generic_restrictedComparison_app, v, eX, eY, F, M,
      pbcDerivedRestrict, pbcRestrict, proEtaleRingRestrictScalars,
      reductionDerivedRestrict, reductionRestrict, Category.assoc]
    exact hs
  have hx : eX b ≫ generic_reductionTransition d X b a h K = qX ≫ eX a := by
    exact generic_evaluation_transition d X K b a h
  have hy : eY b ≫ generic_reductionTransition d Y b a h (F.obj K) = qY ≫ eY a := by
    exact generic_evaluation_transition d Y (F.obj K) b a h
  have hv : qF ≫ v a = v b ≫ F.map qX := by
    have hv₀ := CategoryTheory.ExactTowerAugmentedCounit.interchange_transition
      (stratumModulePull d f) (homOfLE h).op M
    change qF ≫
      (towerDerivedEvaluationInterchange (stratumModulePull d f) (op a)).hom.app M =
      (towerDerivedEvaluationInterchange (stratumModulePull d f) (op b)).hom.app M ≫
        F.map qX at hv₀
    simpa only [v, stratumTowerEvaluationIso, towerDerivedEvaluationInterchange,
      Iso.trans_hom, NatTrans.comp_app,
      Functor.mapDerivedCategoryNatIso_refl, NatTrans.id_app, Category.id_comp,
      Category.comp_id, Category.assoc] using
      hv₀
  have ht : (evY b).map t ≫ qY = qF ≫ (evY a).map t :=
    (pbcTowerTransition Y (pbcAdicCompletion Y d) b a h).naturality t
  have hp : qF ≫ u a = u b ≫ F.map (generic_reductionTransition d X b a h K) := by
    dsimp only [u]
    rw [← Category.assoc, hv, Category.assoc, ← F.map_comp, ← hx, F.map_comp]
    simp only [Category.assoc]
  have hc : qF ≫ ((evY a).map t ≫ eY a) =
      ((evY b).map t ≫ eY b) ≫ generic_reductionTransition d Y b a h (F.obj K) := by
    rw [← reassoc_of% ht, ← hy]
    simp only [Category.assoc]
  exact conjugate_square (u b) (u a)
    (F.map (generic_reductionTransition d X b a h K))
    (generic_reductionTransition d Y b a h (F.obj K)) (c b) (c a) qF
    ((evY b).map t ≫ eY b) ((evY a).map t ≫ eY a) hp (he b) (he a) hc


section ProjectionProofs

attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
local instance siteSmall (T : Scheme.{u}) :
  EssentiallySmall.{u + 1} T.ProEt := essentiallySmallSelf.{0, u, u + 1} _
attribute [local instance] reductionModulesHasDerivedCategory
attribute [local irreducible] Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso

-- Evaluate the adjoint transpose, then use constant/evaluation coherence.
private theorem generic_augmented_projection
    {K : d.derived X} {M : DerivedCategory (d.towers X)}
    (i : (d.derivedConstantTower X).obj K ⟶ M) (n : ℕ) :
    ((d.constantRlimAdjunction Y).unit.app ((d.pull f).obj K) ≫
      (completedRlim Y (d.completedRing Y)).map
        ((d.derivedConstantPullbackIso f).inv.app K ≫ (d.towerPull f).map i)) ≫
      (completedRlimProjection Y (d.completedRing Y) n).app ((d.towerPull f).obj M) ≫
      (stratumTowerEvaluationIso d f n).hom.app M =
    (d.pull f).map
      ((constantEvaluationIso (reductionModules X (d.completedRing X)) (op n)).inv.app K ≫
        (reductionTowerDerivedEvaluation X
          (reductionModuleRing X (d.completedRing X)) n).map i) := by
  let F := d.pull f
  let T := d.towerPull f
  let E := reductionTowerDerivedEvaluation Y (reductionModuleRing Y (d.completedRing Y)) n
  let c := constantEvaluationIso (reductionModules Y (d.completedRing Y)) (op n)
  let adj := d.constantRlimAdjunction Y
  let b := adj.unit.app (F.obj K) ≫ (completedRlim Y (d.completedRing Y)).map
    ((d.derivedConstantPullbackIso f).inv.app K ≫ T.map i)
  have hp : (completedRlimProjection Y (d.completedRing Y) n).app (T.obj M) =
      c.inv.app ((completedRlim Y (d.completedRing Y)).obj (T.obj M)) ≫
        E.map (adj.counit.app (T.obj M)) := by
    exact congr_app (limitCounitProjection_eq d Y n).symm (T.obj M)
  have hb : (d.derivedConstantTower Y).map b ≫ adj.counit.app (T.obj M) =
      (d.derivedConstantPullbackIso f).inv.app K ≫ T.map i := by
    exact (adj.homEquiv _ _).symm_apply_apply _
  have hn := c.inv.naturality b
  change b ≫ c.inv.app _ = c.inv.app (F.obj K) ≫ E.map
    ((d.derivedConstantTower Y).map b) at hn
  change b ≫ _ ≫ _ = _
  rw [hp, ← Category.assoc, ← Category.assoc, hn, Category.assoc, Category.assoc,
    ← E.map_comp_assoc, hb, E.map_comp, Category.assoc]
  have hi := (stratumTowerEvaluationIso d f n).hom.naturality i
  dsimp only [Functor.comp_map] at hi
  rw [hi, ← Category.assoc, ← Category.assoc]
  have hc := CategoryTheory.ExactTowerAugmentedCounit.constant_coherence
    (stratumModulePull d f) (op n) K
  have hd : d.derivedConstantPullbackIso f =
      ringedConstantTowerPullback (stratumModulePull d f) := by
    have he : d.constantPullbackIso f =
        (Functor.compConstIso ℕᵒᵖ (stratumModulePull d f)).symm := by
      apply Iso.ext
      ext N k
      rfl
    simp only [AdicCoefficientDatum.derivedConstantPullbackIso,
      ringedConstantTowerPullback, he]
  rw [hd]
  have ht : stratumTowerEvaluationIso d f n =
      towerDerivedEvaluationInterchange (stratumModulePull d f) (op n) := by
    apply Iso.ext
    ext M
    simp only [stratumTowerEvaluationIso, towerDerivedEvaluationInterchange,
      Functor.mapDerivedCategoryNatIso_refl, Iso.trans_hom, NatTrans.comp_app,
      NatTrans.id_app, Category.id_comp]
  rw [ht]
  simpa only [constantEvaluationIso, ringedConstantTowerEvaluation,
    F, c, E, Functor.map_comp, Category.assoc] using
    congrArg (fun z ↦ z ≫ F.map
      ((reductionTowerDerivedEvaluation X
        (reductionModuleRing X (d.completedRing X)) n).map i)) hc

attribute [local semireducible] completedReductionModuleTowerFunctor

-- The two normalized computing counits identify this with the tensor-unit map.
private theorem generic_augmentation_level_unit_on_KFlat (T : Scheme.{u}) (n : ℕ)
    (P : CochainComplex (reductionModules T (d.completedRing T)) ℤ)
    (hP : CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
      (J := ProEt.topology T) (R := d.completedRing T) P) :
    (constantEvaluationIso (reductionModules T (d.completedRing T)) (op n)).inv.app
        (DerivedCategory.Q.obj P) ≫
      (reductionTowerDerivedEvaluation T (reductionModuleRing T (d.completedRing T)) n).map
        ((completedReductionAugmentation d T).app (DerivedCategory.Q.obj P)) ≫
      (completedReductionEvaluation T d n).app (DerivedCategory.Q.obj P) =
    (generic_reductionUnit d T n).app (DerivedCategory.Q.obj P) := by
  let E := reductionTowerEvaluation T (reductionModuleRing T (d.completedRing T)) n
  let R := pbcRestrict (d.projection T n)
  let ε := reductionScalarComplexCounit T (d.projection T n) P
  have hε : IsIso ε := scalarCounit_isIso T (d.projection T n) P hP
  apply (cancel_mono (R.mapDerivedCategory.map ε ≫ R.mapDerivedCategoryFactors.hom.app
    ((reductionChangeComplex T (d.projection T n)).obj P))).1
  have he :
      (completedReductionEvaluation T d n).app (DerivedCategory.Q.obj P) ≫
        R.mapDerivedCategory.map ε ≫ R.mapDerivedCategoryFactors.hom.app
          ((reductionChangeComplex T (d.projection T n)).obj P) =
      E.mapDerivedCategory.map (completedReductionTowerComplexCounit T d P) ≫
        E.mapDerivedCategoryFactors.hom.app
          ((completedReductionComplexTowerFunctor T d).obj P) := by
    simpa only [completedReductionEvaluation, R, ε, E, pbcRestrict,
      proEtaleRingRestrictScalars, reductionDerivedRestrict, reductionRestrict,
      AdicCoefficientDatum.projection, AdicCoefficientDatum.completedRing,
      reductionTowerDerivedEvaluation] using
      (completedReductionEvaluation_exists T d n).choose_spec.1.2 P hP
  have hu := stratumUnit_formula d T P hP
  have hs := (pbcDerivedScalarAdjunction_exists (d.projection T n)).exists.choose_spec P hP
  simp only [Category.assoc]
  erw [he]
  rw [← E.mapDerivedCategory.map_comp_assoc, hu, E.mapDerivedCategory.map_comp,
    Category.assoc]
  erw [E.mapDerivedCategoryFactors_hom_naturality]
  rw [← reassoc_of% (constantEvaluation_factors
    (reductionModules T (d.completedRing T)) (op n) P),
    Iso.inv_hom_id_app_assoc]
  change (generic_reductionUnit d T n).app (DerivedCategory.Q.obj P) ≫
    R.mapDerivedCategory.map ε ≫ R.mapDerivedCategoryFactors.hom.app
      ((reductionChangeComplex T (d.projection T n)).obj P) = _ at hs
  rw [hs]
  congr 1
  ext q : 1
  exact stratumModuleUnit_component d T (P.X q) n


-- K-flat resolutions and naturality extend the representative calculation.
/-- Finite evaluation of the actual quotient augmentation is the scalar-extension unit.
Source: localization Step 6; Stacks Tags 03EL and 06YY
(blueprint: lem-sf-completed-reduction-augmentation-level-unit).
Proof: on a K-flat representative, compose with the invertible scalar computing
counit. The normalized reduction evaluation and augmentation counits turn the
composite into the localization of the ordinary quotient-unit map. Its component
is the ordinary scalar-extension unit. The normalized derived scalar adjunction
therefore gives equality after cancellation. K-flat resolutions and naturality
extend this calculation to every derived object. -/
theorem sfCompletedReductionAugmentation_level_unit (T : Scheme.{u})
    (K : d.derived T) (n : ℕ) :
    (ringedConstantTowerEvaluation (reductionModules T (d.completedRing T)) (op n)).inv.app K ≫
      (reductionTowerDerivedEvaluation T (reductionModuleRing T (d.completedRing T)) n).map
        ((completedReductionAugmentation d T).app K) ≫
      (completedReductionEvaluation T d n).app K =
    (pbcDerivedScalarAdjunction (d.projection T n)).unit.app K := by
  let E := reductionTowerDerivedEvaluation T (reductionModuleRing T (d.completedRing T)) n
  let α := (constantEvaluationIso (reductionModules T (d.completedRing T)) (op n)).inv ≫
    whiskerRight (completedReductionAugmentation d T) E ≫ completedReductionEvaluation T d n
  have hres (C : CochainComplex (reductionModules T (d.completedRing T)) ℤ) :
      ∃ (P : CochainComplex (reductionModules T (d.completedRing T)) ℤ) (p : P ⟶ C),
        CochainComplex.IsKFlatIndependentCoefficients.{u + 1, u, u + 1}
          (J := ProEt.topology T) (R := d.completedRing T) P ∧
          QuasiIso p := by
    obtain ⟨P, p, hP, _, hp, _⟩ :=
      CochainComplex.exists_isKFlatResolutionIndependentCoefficients
        (J := ProEt.topology T) (R := d.completedRing T) C
    exact ⟨P, p, hP, hp⟩
  have he : α = generic_reductionUnit d T n :=
    derived_natTrans_ext _ _ _ hres α (generic_reductionUnit d T n)
      (fun P hP ↦ generic_augmentation_level_unit_on_KFlat d T n P hP)
  exact congr_app he K



end ProjectionProofs

end GenericFinite

private theorem completion_general
    {A : Type (u + 1)} [CommRing A]
    {X Y : Scheme.{u}} (g : X ⟶ Y) (d : AdicCoefficientDatum A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = d.ideal)
    (K : DerivedCategory (pbcModules Y (pbcAdicCompletion Y d)))
    (P : CochainComplex (pbcModules X (pbcAdicCompletion X d)) ℤ)
    (eP : DerivedCategory.Q.obj P ≅ (completedOrdinaryPullback g d).obj K) :
    ∃ α : completedPullbackObject g d K ≅
        intrinsicCompletion X d r a ha ((completedOrdinaryPullback g d).obj K) P eP,
      completedPullbackComparison g d K ≫ α.hom =
        intrinsicCompletionUnit X d r a ha ((completedOrdinaryPullback g d).obj K) P eP := by
  let eL := pullbackDatumOrdinaryTransport g d
  let eT := pullbackDatumTowerTransport g d
  let τ := stratumReductionIso d g
  let R := completedTowerRlim d X
  let t : (completedTowerPullback g d).obj ((completedReductionTower Y d).obj K) ≅
      (completedReductionTower X d).obj ((completedOrdinaryPullback g d).obj K) :=
    eT.app ((completedReductionTower Y d).obj K) ≪≫ τ.app K ≪≫
      (completedReductionTower X d).mapIso (eL.app K).symm
  have ht : ((completedPullbackConstantIso g d).hom.app K ≫
      (completedTowerPullback g d).map ((completedReductionTowerUnit d Y).app K)) ≫
        t.hom = (completedReductionTowerUnit d X).app
          ((completedOrdinaryPullback g d).obj K) := by
    exact reductionAugmentationTransport
      (completedDerivedConstant d Y) (completedDerivedConstant d X)
      (completedReductionTower Y d) (completedReductionTower X d)
      (completedOrdinaryPullback g d) (d.pull g)
      (completedTowerPullback g d) (d.towerPull g) eL eT
      (completedPullbackConstantIso g d) (d.derivedConstantPullbackIso g)
      (completedReductionTowerUnit d Y) (completedReductionTowerUnit d X) τ K
      (datumConstantComparison g d K) (stratumReduction_augmentation d g K)
  obtain ⟨c, hc⟩ := completedKoszulQuotientComparison X d r a ha
    ((completedOrdinaryPullback g d).obj K) P eP
  refine ⟨R.mapIso t ≪≫ c.symm, ?_⟩
  change completedPullbackComparison g d K ≫ (R.map t.hom ≫ c.inv) = _
  rw [← Category.assoc]
  have hu : completedPullbackComparison g d K ≫ R.map t.hom =
      intrinsicCompletionUnit X d r a ha
        ((completedOrdinaryPullback g d).obj K) P eP ≫ c.hom := by
    dsimp only [completedPullbackComparison]
    rw [Category.assoc, ← R.map_comp, ht, constantRlimUnit_eq]
    exact hc.symm
  rw [hu, Category.assoc, Iso.hom_inv_id, Category.comp_id]



namespace ImmersionCompletedPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{u}} (f : Y ⟶ X)

attribute [local irreducible] pbcIntegralDatum

private theorem strict_completion (r : ℕ) (a : Fin r → PbcIntegralRing l E)
    (ha : Ideal.span (Set.range a) = (pbcIntegralDatum l E).ideal)
    (K : PbcCompletedDerived X (pbcIntegralDatum l E)) :
    ∃ α : (pbcActualStrictCompletedPull (pbcIntegralDatum l E) f).obj K ≅
        wfCompletionObj Y (pbcIntegralDatum l E) r a ha
          ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K),
      (pbcActualStrictCompletedPullUnit (pbcIntegralDatum l E) f).app K ≫ α.hom =
        wfCompletionUnit Y (pbcIntegralDatum l E) r a ha
          ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K) := by
  obtain ⟨α, hα⟩ := completion_general f (pbcIntegralDatum l E) r a ha K
    (wfCompletionRepresentative Y (pbcIntegralDatum l E)
      ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K))
    (DerivedCategory.Q.objObjPreimageIso
      ((pbcActualDerivedPull f (pbcIntegralDatum l E)).obj K))
  refine ⟨α, ?_⟩
  simpa only [pbcActualStrictCompletedPullUnit, completedPullbackComparison,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.rightUnitor_inv_app, Functor.associator_inv_app, Category.id_comp,
    Category.assoc, Functor.map_comp, wfCompletionUnit, wfCompletionObj] using hα

end ImmersionCompletedPullback

end AlgebraicGeometry.Scheme
