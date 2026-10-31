/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityReductionTowerNormalized
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerReconstruction
public import WeilConjectures.SixFunctors.Coefficient.CoefficientRingedSequenceSiteSupplement
import WeilConjectures.SmoothPurity.Coefficient.CoefficientConstantTowerRoos
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Exact completed-coefficient tower functors and their Roos presentation

Source: latest blueprint, sec-smooth-purity, sk-lem-sp-tower-equivalence.proof.md,
Adjunction paragraph; Stacks 0941 (blueprint: lem-sp-completed-tower-roos).

The five completed-tower constructions are moved verbatim from
SmoothPurityNormalizedEquivalence. Evaluation proves exactness of scalar forgetting.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules
namespace AlgebraicGeometry.ProEtale
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Forget the finite-level actions to completed coefficients, retaining all strict
transitions. Source: blueprint, definition of L_T (blueprint: det-sp-normalized-equivalence). -/
def spCompletedStrictTower (D : SpCoefficientTowersAbelian l E T) :
    spCoefficientTowers l E T ⥤
      (ℕᵒᵖ ⥤ WeilConjectures.scalarReductionSource.{u, u} l E T) :=
  (Functor.ofOpSequence (spCompletedTransition l E T D)).flip

/-- The coefficient-ring identification transports the existing reduction functor
from section modules to modules over the completed ring. Source: blueprint, r_T
(blueprint: det-sp-normalized-equivalence). -/
def spCompletedReduction (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) :
    DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T) ⥤
      spDerivedCoefficientTowers l E T D :=
  (restrictScalars.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      R.coefficient.hom)).mapDerivedCategory ⋙ R.red

/-- Total derived inverse limit after the exact scalar-forgetting functor. The
fixed-ring limit is the existing K-injective total derived inverse limit, including its
resolution-normalized projections. Source: blueprint, L_T; Stacks 0941
(blueprint: det-sp-normalized-equivalence). -/
def spCompletedTotalLimit (D : SpCoefficientTowersAbelian l E T)
    [(spCompletedStrictTower l E T D).Additive]
    [PreservesFiniteLimits (spCompletedStrictTower l E T D)]
    [PreservesFiniteColimits (spCompletedStrictTower l E T D)] :
    spDerivedCoefficientTowers l E T D ⥤
      DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T) :=
  letI := D.hasDerived
  (spCompletedStrictTower l E T D).mapDerivedCategory ⋙
    WeilConjectures.coefficientConstantTowerLimit l E T

/-- Exact evaluation commutes with forgetting the finite-level coefficient actions.
The comparison is the canonical localization comparison for the two exact composites.
Source: blueprint, definition of L_T (blueprint: det-sp-normalized-equivalence). -/
def spCompletedForgettingEvaluationIso (D : SpCoefficientTowersAbelian l E T)
    [(spCompletedStrictTower l E T D).Additive]
    [PreservesFiniteLimits (spCompletedStrictTower l E T D)]
    [PreservesFiniteColimits (spCompletedStrictTower l E T D)] (n : ℕ) :
    @Functor.mapDerivedCategory _ _ _ D.hasDerived _ _ _
        (HasDerivedCategory.standard _) (spCompletedStrictTower l E T D) _ _ _ ⋙
      WeilConjectures.coefficientConstantTowerEvaluation l E T n ≅
        spDerivedCompletedEvaluation l E T D n :=
  letI := D.hasDerived
  letI := D.evaluationLimits n
  letI := D.evaluationColimits n
  letI : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    Functor.additive_of_preserves_binary_products _
  (Functor.mapDerivedCategoryCompIso (spCompletedStrictTower l E T D)
    ((evaluation ℕᵒᵖ (WeilConjectures.scalarReductionSource l E T)).obj (op n))).symm ≪≫
    Functor.mapDerivedCategoryCompIso (spCoefficientEvaluation l E T D.equivalence n)
      (spCompletedEllRestriction l E T n)

/-- The actual total-limit projection to each completed-coefficient level. Its
normalization comes from the existing projection on simultaneous K-injective towers.
Source: blueprint, total limit and its counit (blueprint: det-sp-normalized-equivalence). -/
def spCompletedTotalProjection (D : SpCoefficientTowersAbelian l E T)
    [(spCompletedStrictTower l E T D).Additive]
    [PreservesFiniteLimits (spCompletedStrictTower l E T D)]
    [PreservesFiniteColimits (spCompletedStrictTower l E T D)] (n : ℕ) :
    spCompletedTotalLimit l E T D ⟶ spDerivedCompletedEvaluation l E T D n :=
  letI := D.hasDerived
  Functor.whiskerLeft (spCompletedStrictTower l E T D).mapDerivedCategory
    (WeilConjectures.coefficientConstantTowerProjection l E T n) ≫
      (spCompletedForgettingEvaluationIso l E T D n).hom

/-- Exact scalar forgetting preserves finite limits by exact evaluation.
Source: Stacks 0941 (blueprint: lem-sp-completed-tower-roos). -/
instance spCompletedStrictTowerLimits (D : SpCoefficientTowersAbelian l E T) :
    PreservesFiniteLimits (spCompletedStrictTower l E T D) := by
  apply preservesFiniteLimits_of_evaluation
  intro n
  change PreservesFiniteLimits (spCompletedEvaluation l E T D n.unop)
  infer_instance

/-- Exact scalar forgetting preserves finite colimits by exact evaluation.
Source: Stacks 0941 (blueprint: lem-sp-completed-tower-roos). -/
instance spCompletedStrictTowerColimits (D : SpCoefficientTowersAbelian l E T) :
    PreservesFiniteColimits (spCompletedStrictTower l E T D) := by
  apply preservesFiniteColimits_of_evaluation
  intro n
  change PreservesFiniteColimits (spCompletedEvaluation l E T D n.unop)
  infer_instance

/-- Scalar forgetting is additive since it preserves binary products.
Source: Stacks 0941 (blueprint: lem-sp-completed-tower-roos). -/
instance spCompletedStrictTowerAdditive (D : SpCoefficientTowersAbelian l E T) :
    (spCompletedStrictTower l E T D).Additive := by
  let := spCompletedStrictTowerLimits l E T D
  exact Functor.additive_of_preserves_binary_products _

/-- The exact forgetting and right-derived limit have their canonical shift structures.
Source: Stacks 0941 (blueprint: lem-sp-completed-tower-roos). -/
instance spCompletedTotalLimitShift (D : SpCoefficientTowersAbelian l E T)
    [(spCompletedStrictTower l E T D).Additive]
    [PreservesFiniteLimits (spCompletedStrictTower l E T D)]
    [PreservesFiniteColimits (spCompletedStrictTower l E T D)] :
    (spCompletedTotalLimit l E T D).CommShift ℤ := by
  let := D.hasDerived
  unfold spCompletedTotalLimit WeilConjectures.coefficientConstantTowerLimit
  infer_instance

/-- Exact forgetting and total right-derived inverse limit are triangulated.
Source: Stacks 0941 (blueprint: lem-sp-completed-tower-roos). -/
theorem spCompletedTotalLimit_triangulated (D : SpCoefficientTowersAbelian l E T)
    [(spCompletedStrictTower l E T D).Additive]
    [PreservesFiniteLimits (spCompletedStrictTower l E T D)]
    [PreservesFiniteColimits (spCompletedStrictTower l E T D)] :
    letI := spCompletedTotalLimitShift l E T D
    (spCompletedTotalLimit l E T D).IsTriangulated := by
  let := D.hasDerived
  unfold spCompletedTotalLimit WeilConjectures.coefficientConstantTowerLimit
    spCompletedTotalLimitShift
  infer_instance

/-- The actual completed tower limit has its Roos triangle with the specified projections.
Source: Stacks 0941; latest blueprint, normalized equivalence, Adjunction paragraph
(blueprint: lem-sp-completed-tower-roos).

Proof: apply the fixed-ring K-injective total-limit Roos theorem to the strict tower
obtained by exact scalar forgetting. At every level the canonical localization
comparison is spCompletedForgettingEvaluationIso. Its naturality and localization
uniqueness identify the conjugated successor maps with spDerivedCompletedTransition.
Transport the distinguished Roos triangle along the product of these evaluation
isomorphisms. Its first arrow is Pi.lift of spCompletedTotalProjection by the definition
of that projection and the universal property of the product. The third arrow is the
original connecting arrow precomposed with the inverse product isomorphism. -/
theorem spCompletedTotalLimit_roos (D : SpCoefficientTowersAbelian l E T)
    [HasCountableProducts
      (DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))]
    (C : spDerivedCoefficientTowers l E T D) :
    ∃ δ : (∏ᶜ fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C) ⟶
        ((spCompletedTotalLimit l E T D).obj C)⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle
        (fun n : ℕ ↦ (spDerivedCompletedTransition l E T D n).app C)
        ((spCompletedTotalLimit l E T D).obj C)
        (Pi.lift (fun n : ℕ ↦ (spCompletedTotalProjection l E T D n).app C)) δ := by
  classical
  let := D.hasDerived
  let F := spCompletedStrictTower l E T D
  let ev := fun n : ℕ ↦
    (evaluation ℕᵒᵖ (WeilConjectures.scalarReductionSource l E T)).obj (op n)
  let e := spCompletedForgettingEvaluationIso l E T D
  obtain ⟨p, hpl, hp⟩ := Nat.exists_infinite_primes (l + 1)
  let : Fact p.Prime := ⟨hp⟩
  let A : WeilConjectures.FiniteFieldDatum.{0} := {
    p := p
    a := 1
    q := p
    prime := hp
    exponent_pos := le_rfl
    cardinality_eq := (pow_one p).symm
    k₀ := ZMod p
    card_base := by simp [Nat.card_eq_fintype_card]
    k := AlgebraicClosure (ZMod p) }
  have hl : l ≠ A.p := by change l ≠ p; omega
  have he (n : ℕ) (P : CochainComplex (spCoefficientTowers l E T) ℤ) :
      (e n).hom.app (DerivedCategory.Q.obj P) ≫
          (spCompletedEvaluationFactors l E T D n).hom.app P =
        (ev n).mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
          (ev n).mapDerivedCategoryFactors.hom.app
            ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
    let := D.evaluationLimits n
    let := D.evaluationColimits n
    let : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
      Functor.additive_of_preserves_binary_products _
    have hcomp := Functor.mapDerivedCategoryCompIso_fac
      (spCoefficientEvaluation l E T D.equivalence n) (spCompletedEllRestriction l E T n) P
    have hforget := Functor.mapDerivedCategoryCompIso_fac F (ev n) P
    have hi : (Functor.mapHomologicalComplexCompIso
        (Iso.refl (spCoefficientEvaluation l E T D.equivalence n ⋙
          spCompletedEllRestriction l E T n)) (.up ℤ)).hom.app P = 𝟙 _ := rfl
    have hj : (Functor.mapHomologicalComplexCompIso
        (Iso.refl (F ⋙ ev n)) (.up ℤ)).hom.app P = 𝟙 _ := rfl
    erw [hi, DerivedCategory.Q.map_id, Category.comp_id] at hcomp
    erw [hj, DerivedCategory.Q.map_id, Category.comp_id] at hforget
    apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F (ev n)).hom.app
      (DerivedCategory.Q.obj P))).1
    dsimp only [e, spCompletedForgettingEvaluationIso, spCompletedEvaluationFactors,
      Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
      Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
      Functor.whiskerRight_app, Functor.whiskerLeft_app]
    dsimp only [F, ev] at *
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
    exact hcomp.trans hforget.symm
  let t (n : ℕ) : (ev (n + 1)).mapDerivedCategory ⟶ (ev n).mapDerivedCategory :=
    Localization.liftNatTrans DerivedCategory.Q
      (HomologicalComplex.quasiIso
        (ℕᵒᵖ ⥤ WeilConjectures.scalarReductionSource l E T) (.up ℤ)) _ _
      (ev (n + 1)).mapDerivedCategory (ev n).mapDerivedCategory
      (Functor.whiskerRight (NatTrans.mapHomologicalComplex
        ((evaluation ℕᵒᵖ (WeilConjectures.scalarReductionSource l E T)).map
          (homOfLE n.le_succ).op) (.up ℤ)) DerivedCategory.Q)
  have hf (n : ℕ) :
      Functor.whiskerLeft F.mapDerivedCategory (t n) ≫
          (e n).hom =
        (e (n + 1)).hom ≫ spDerivedCompletedTransition l E T D n := by
    apply Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso (spCoefficientTowers l E T) (.up ℤ))
    intro P
    apply (cancel_mono ((spCompletedEvaluationFactors l E T D n).hom.app P)).1
    have ht := (spDerivedCompletedTransition_existsUnique l E T D n).exists.choose_spec P
    change (spDerivedCompletedTransition l E T D n).app (DerivedCategory.Q.obj P) ≫
      (spCompletedEvaluationFactors l E T D n).hom.app P = _ at ht
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
    rw [ht, he, reassoc_of% (he (n + 1) P)]
    rw [← (t n).naturality_assoc]
    congr 1
    dsimp only [t, Functor.comp_obj]
    rw [Localization.liftNatTrans_app]
    dsimp only [ev]
    simp only [Localization.Lifting.iso, Category.assoc, Iso.inv_hom_id_app,
      Category.comp_id, Functor.whiskerRight_app]
    congr 1
    congr 1
    apply HomologicalComplex.Hom.ext
    funext i
    change ((Functor.ofOpSequence (spCompletedTransition l E T D)).map
      (homOfLE n.le_succ).op).app (P.X i) = _
    exact congr_app
      (Functor.ofOpSequence_map_homOfLE_succ (spCompletedTransition l E T D) n) (P.X i)
  obtain ⟨hP, δ, hδ⟩ := WeilConjectures.coefficientConstantTower_roos l E T A hl
    (F.mapDerivedCategory.obj C)
  let := hP
  let b := Pi.mapIso (fun n ↦ (e n).app C)
  have hb : towerTransitionEndomorphism
      (fun n ↦ (WeilConjectures.normalizedDVRTowerTransition l E T A hl n.le_succ).app
        (F.mapDerivedCategory.obj C)) ≫ b.hom =
      b.hom ≫ towerTransitionEndomorphism
        (fun n ↦ (spDerivedCompletedTransition l E T D n).app C) := by
    exact (towerTransitionEndomorphism_natural_backward _ _
      (fun n ↦ (e n).hom.app C) (fun n ↦ (congr_app (hf n) C).symm)).symm
  have hproj : Pi.lift (fun n : ℕ ↦
      (WeilConjectures.coefficientConstantTowerProjection l E T n).app
        (F.mapDerivedCategory.obj C)) ≫ b.hom =
      Pi.lift (fun n : ℕ ↦ (spCompletedTotalProjection l E T D n).app C) := by
    apply Pi.hom_ext
    intro n
    dsimp only [b, F, e]
    simp only [Functor.comp_obj, Category.assoc, Pi.mapIso_hom_π, Pi.lift_π_assoc,
      Pi.lift_π, Iso.app_hom, spCompletedTotalProjection, NatTrans.comp_app,
      Functor.whiskerLeft_app]
  refine ⟨b.inv ≫ δ, ?_⟩
  exact (Pretriangulated.distinguished_iff_of_iso
    (Pretriangulated.Triangle.isoMk
      (Pretriangulated.Triangle.mk _ _ δ)
      (Pretriangulated.Triangle.mk _ _ (b.inv ≫ δ)) (Iso.refl _) b b
      (by simpa using hproj) hb (by simp))).mp hδ

end AlgebraicGeometry.ProEtale
