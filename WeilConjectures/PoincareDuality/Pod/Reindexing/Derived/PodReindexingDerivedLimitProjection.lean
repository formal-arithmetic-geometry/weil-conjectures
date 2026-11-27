/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedCanonical
import all WeilConjectures.PoincareDuality.Pod.Reindexing.Derived.PodReindexingDerivedCanonical
import all WeilConjectures.PoincareDuality.Pod.Reindexing.PodReindexingRestrictedTowerNaturality
import all WeilConjectures.SmoothPurity.IntegralAmbient.IntegralAmbientOperationModels

/-! # Limit projection law for raw derived comparison data

We show that the completion reindexing datum assembled from raw derived comparison data
satisfies the limit-projection law, provided its restriction and evaluation comparisons are
the canonical ones and its limit comparison satisfies the limit-model law.

## Implementation details

Both sides of the law are natural in the coefficient system, so it suffices to check it on a
complex of strict systems. There the total-limit projections are computed through the normalized
Roos models, the limit comparison through the limit-model law, and the restriction and
evaluation comparisons through their strict models; the remaining strict identity holds by the
construction of the canonical evaluation comparison. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.SemilinearSections.moduleAbelian
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
attribute [local instance 5000] WeilConjectures.coefficientSequenceHasDerived
attribute [local instance 5000] WeilConjectures.coefficientFiniteHasDerived
attribute [local irreducible] HasDerivedCategory.standard

universe t u a b
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  {X Y : Scheme.{t}} (g : X ⟶ Y) [IsIso g]
  (SY : PodSignedRoosShift (scalarReductionSource l E Y))
  (SX : PodSignedRoosShift (scalarReductionSource l E X))

namespace PodReindexingLimitProjection

/-- The projection of the strict Roos complex of a tower to its `n`th term. -/
def roosProjection {W : Scheme.{t}}
    (T : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E W) ℤ) (n : ℕ) :
    DerivedCategory.Q.obj (integralOperationsRoos T) ⟶ DerivedCategory.Q.obj (T.obj (op n)) :=
  DerivedCategory.Q.map (CochainComplex.mappingCocone.fst (podRoosBoundary T) ≫
    Pi.π (fun m ↦ T.obj (op m)) n)

theorem roosProjection_natural {W : Scheme.{t}}
    {A B : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E W) ℤ} (a : A ⟶ B) (n : ℕ) :
    DerivedCategory.Q.map (integralOperationsRoosFunctor.map a) ≫ roosProjection l E B n =
      roosProjection l E A n ≫ DerivedCategory.Q.map (a.app (op n)) := by
  unfold roosProjection
  rw [← DerivedCategory.Q.map_comp, ← DerivedCategory.Q.map_comp]
  congr 1
  erw [← Category.assoc, (IntegralAmbient.roosMap_coordinates a).1, Category.assoc,
    Pi.map_π]
  exact (Category.assoc _ _ _).symm

theorem normalized_roosProjection (W : Scheme.{t}) (ρ : IntegralComparisonRoosModel l E W)
    (C : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (n : ℕ) :
    ρ.comparison.hom.app C ≫ roosProjection l E C.asFunctor n =
      (coefficientConstantTowerProjection l E W n).app (DerivedCategory.Q.obj C) ≫
        (coefficientConstantTowerEvaluationFactors l E W n).hom.app C := by
  have hi (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      [I.IsKInjective] :
      ρ.comparison.hom.app I ≫ roosProjection l E I.asFunctor n =
        (coefficientConstantTowerProjection l E W n).app (DerivedCategory.Q.obj I) ≫
          (coefficientConstantTowerEvaluationFactors l E W n).hom.app I := by
    rw [ρ.computes I]
    unfold roosProjection
    rw [Category.assoc, ← DerivedCategory.Q.map_comp]
    have h := (integralComparisonLimitToRoos_existsUnique l E W I).exists.choose_spec.1 n
    change integralComparisonLimitToRoos l E W I ≫ _ ≫ _ = _ at h
    rw [h]
    exact ((coefficientConstantTowerProjection_exists l E W n).choose_spec.1 I).symm
  obtain ⟨I, hI, f, _, hf⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective C
  have : QuasiIso f := hf
  let V := (evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n)
  apply (cancel_mono (DerivedCategory.Q.map
    ((V.mapHomologicalComplex (.up ℤ)).map f))).1
  have hv := V.mapDerivedCategoryFactors.hom.naturality f
  have hp := (coefficientConstantTowerProjection l E W n).naturality
    (DerivedCategory.Q.map f)
  have hθ := ρ.comparison.hom.naturality f
  dsimp only [Functor.comp_map] at hv hθ
  erw [Category.assoc, ← roosProjection_natural l E
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) n]
  rw [← Category.assoc, ← hθ, Category.assoc]
  erw [hi I]
  rw [Category.assoc, ← hv]
  exact (reassoc_of% hp) _

theorem projection_formula (W : Scheme.{t}) (ρ : IntegralComparisonRoosModel l E W)
    (C : CochainComplex (coefficientSequenceModules l E W) ℤ) (n : ℕ) :
    (coefficientSequenceProjection l E W n).app (DerivedCategory.Q.obj C) ≫
        (coefficientFiniteDerivedRestriction l E W n).map
          ((coefficientSequenceEvaluation l E W n).mapDerivedCategoryFactors.hom.app C) ≫
        (scalarReductionRestriction l E W n).mapDerivedCategoryFactors.hom.app
          (((coefficientSequenceEvaluation l E W n).mapHomologicalComplex (.up ℤ)).obj C) =
      (podLimitRoos l E ρ C).hom ≫ roosProjection l E (podRestrictedTower l E C) n ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
          (eqToIso (coefficientSequenceRestriction_evaluation l E W n)).hom (.up ℤ)).app C) := by
  have := (scalarReductionRestriction_exact l E W n).1
  have := (scalarReductionRestriction_exact l E W n).2
  dsimp only [podLimitRoos, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom]
  rw [Category.assoc]
  erw [reassoc_of% (normalized_roosProjection l E W ρ
    (((coefficientSequenceRestriction l E W).mapHomologicalComplex (.up ℤ)).obj C) n)]
  erw [reassoc_of% ((coefficientConstantTowerProjection l E W n).naturality
    ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.hom.app C))]
  unfold coefficientSequenceProjection
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  congr 1
  have h := PodReindexingDerivedCanonical.squareIso_factors
    (coefficientSequenceRestriction l E W)
    ((evaluation ℕᵒᵖ (scalarReductionSource l E W)).obj (op n))
    (coefficientSequenceEvaluation l E W n) (scalarReductionRestriction l E W n)
    (eqToIso (coefficientSequenceRestriction_evaluation l E W n)) C
  erw [← h, ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rfl

theorem roos_reindex_projection (S : PodReindexingStrictData l E g) (hS : S.RoosFst l E g)
    (T : ℕᵒᵖ ⥤ CochainComplex (scalarReductionSource l E Y) ℤ) (n : ℕ) :
    (podOrdinaryReindex l E g).map (roosProjection l E T n) ≫
        (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app (T.obj (op n)) =
      (isoReductionIntegralInverse l E g).mapDerivedCategoryFactors.hom.app
          (integralOperationsRoos T) ≫
        DerivedCategory.Q.map (S.roos T).hom ≫
        roosProjection l E ((podReindexTower l E g).obj T) n := by
  unfold roosProjection podOrdinaryReindex
  erw [Functor.mapDerivedCategoryFactors_hom_naturality]
  rw [← DerivedCategory.Q.map_comp]
  congr 1
  have h := congrArg (· ≫ Pi.π (fun m ↦ ((podReindexTower l E g).obj T).obj (op m)) n) (hS T)
  simp only [Category.assoc] at h
  erw [h]
  rw [Functor.map_comp]
  congr 1
  simp [podReindexProduct]

theorem strict_restricted (S : PodReindexingStrictData l E g)
    (hS : S.RestrictedGenerators l E g)
    (C : CochainComplex (coefficientSequenceModules l E Y) ℤ) (n : ℕ) :
    (isoReductionIntegralComplex l E g).map ((NatTrans.mapHomologicalComplex
        (eqToIso (coefficientSequenceRestriction_evaluation l E Y n)).hom (.up ℤ)).app C) ≫
      (NatTrans.mapHomologicalComplex (podReindexingStrictRestriction l E g n).hom (.up ℤ)).app
        (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C) =
    (S.restricted C).hom.app (op n) ≫ (NatTrans.mapHomologicalComplex
        (eqToIso (coefficientSequenceRestriction_evaluation l E X n)).hom (.up ℤ)).app
          (((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)).obj C) ≫
      ((scalarReductionRestriction l E X n).mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (podReindexingStrictEvaluation l E g n).hom
          (.up ℤ)).app C) := by
  have hr := restricted_eq l E g S hS C
  apply HomologicalComplex.hom_ext
  intro i
  have hri := congrArg (fun e ↦ (e.hom.app (op n)).f i) hr
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f]
  rw [podReindexingStrictEvaluation_hom_app l E g n (C.X i), hri]
  have hc : (((restrictedIso l E g).app C).hom.app (op n)).f i =
      ((restrictedModuleIso l E g).hom.app (C.X i)).app (op n) := rfl
  rw [hc]
  simp only [podReindexingRestrictedEvaluation, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, isoWhiskerLeft_hom,
    isoWhiskerRight_hom, Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
    NatIso.ofComponents_hom_app, Iso.refl_hom, Category.id_comp, Category.comp_id,
    eqToIso.hom, eqToHom_app, evaluation_obj_map]
  rw [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, ← NatTrans.comp_app_assoc,
    Iso.hom_inv_id_app, NatTrans.id_app]
  erw [Category.id_comp, Category.id_comp]
  rfl

end PodReindexingLimitProjection

open PodReindexingLimitProjection

/-- The assembled datum of raw derived comparison data `Q` with the canonical restriction and
evaluation comparisons and a limit comparison satisfying the limit-model law satisfies the
limit-projection law. -/
theorem podReindexingDerivedCoreData_limitProjection
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (S : PodReindexingStrictData l E g) (hS : S.Laws l E g SY SX)
    (β : ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ),
      integralOperationsGoodComplex l E Y P → ∀ n : ℕ,
      (isoReductionFiniteComplex l E g n).obj (unrestrictedTowerFiniteComplex l E Y n P) ≅
        unrestrictedTowerFiniteComplex l E X n
          ((isoReductionIntegralComplex l E g).obj P))
    (_hβ : podReindexingCoreQuotientGenerators l E g β)
    (_htransition : podReindexingCoreQuotientTransition l E g β)
    (CY : IntegralOnSlice.completion l E Y none ≅
      (podReindexCalculus l E Y).reduction ⋙ coefficientSequenceLimit l E Y)
    (CX : IntegralOnSlice.completion l E X none ≅
      (podReindexCalculus l E X).reduction ⋙ coefficientSequenceLimit l E X)
    (Q : PodReindexingDerivedCoreData l E g)
    (hrestriction : ∀ n, Q.restriction n = podReindexingDerivedRestriction l E g n)
    (hevaluation : ∀ n, Q.evaluation n = podReindexingDerivedEvaluation l E g n)
    (hlimit : PodCompletionReindex.LimitModel l E g (Q.assemble l E g SY SX S β CY CX)) :
    PodCompletionReindex.LimitProjection l E g
      (Q.assemble l E g SY SX S β CY CX) := by
  have hS' := hS
  obtain ⟨hFst, -, -, -, hGen⟩ := hS'
  intro A n
  dsimp only [PodReindexingDerivedCoreData.assemble]
  rw [hrestriction n, hevaluation n]
  let τ₁ : coefficientSequenceLimit l E Y ⋙ podOrdinaryReindex l E g ⟶
      coefficientSequenceDerivedEvaluation l E Y n ⋙ isoReductionFiniteDerived l E g n ⋙
        coefficientFiniteDerivedRestriction l E X n :=
    Functor.whiskerRight (coefficientSequenceProjection l E Y n) (podOrdinaryReindex l E g) ≫
      Functor.whiskerLeft (coefficientSequenceDerivedEvaluation l E Y n)
        (podReindexingDerivedRestriction l E g n).hom
  let τ₂ : coefficientSequenceLimit l E Y ⋙ podOrdinaryReindex l E g ⟶
      coefficientSequenceDerivedEvaluation l E Y n ⋙ isoReductionFiniteDerived l E g n ⋙
        coefficientFiniteDerivedRestriction l E X n :=
    Q.limit.hom ≫ Functor.whiskerLeft (integralComparisonDerivedSequencePullback l E g)
        (coefficientSequenceProjection l E X n) ≫
      Functor.whiskerRight (podReindexingDerivedEvaluation l E g n).hom
        (coefficientFiniteDerivedRestriction l E X n)
  suffices h : τ₁ = τ₂ from congr_app h A
  refine Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso (coefficientSequenceModules l E Y) (.up ℤ)) (fun C ↦ ?_)
  simp only [τ₁, τ₂, NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  have := (scalarReductionRestriction_exact l E Y n).1
  have := (scalarReductionRestriction_exact l E Y n).2
  have := (scalarReductionRestriction_exact l E X n).1
  have := (scalarReductionRestriction_exact l E X n).2
  let P := ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C
  have hr := PodReindexingDerivedCanonical.squareIso_factors (scalarReductionRestriction l E Y n)
    (isoReductionIntegralInverse l E g) (isoReductionFiniteInverse l E g n)
    (scalarReductionRestriction l E X n) (podReindexingStrictRestriction l E g n) P
  have hev := PodReindexingDerivedCanonical.squareIso_factors
    (integralComparisonSequencePullback l E g) (coefficientSequenceEvaluation l E X n)
    (coefficientSequenceEvaluation l E Y n) (isoReductionFiniteInverse l E g n)
    (podReindexingStrictEvaluation l E g n) C
  have hr' := (Iso.inv_comp_eq ((podOrdinaryReindex l E g).mapIso
    ((scalarReductionRestriction l E Y n).mapDerivedCategoryFactors.app P))).1 hr
  have hev' := (Iso.inv_comp_eq ((coefficientSequenceDerivedEvaluation l E X n).mapIso
    ((integralComparisonSequencePullback l E g).mapDerivedCategoryFactors.app C))).1 hev
  rw [← cancel_mono ((coefficientFiniteDerivedRestriction l E X n).map
      ((isoReductionFiniteDerived l E g n).map
        ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C)) ≫
    (coefficientFiniteDerivedRestriction l E X n).map
      ((isoReductionFiniteInverse l E g n).mapDerivedCategoryFactors.hom.app P) ≫
    (scalarReductionRestriction l E X n).mapDerivedCategoryFactors.hom.app
      (((isoReductionFiniteInverse l E g n).mapHomologicalComplex (.up ℤ)).obj P))]
  simp only [Category.assoc]
  erw [← reassoc_of% ((podReindexingDerivedRestriction l E g n).hom.naturality
    ((coefficientSequenceEvaluation l E Y n).mapDerivedCategoryFactors.hom.app C))]
  erw [hr']
  rw [Functor.mapIso_hom, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc, Iso.app_hom]
  erw [projection_formula l E Y Q.sourceRoos C n]
  simp only [Functor.map_comp, Category.assoc]
  erw [reassoc_of% (Functor.mapDerivedCategoryFactors_hom_naturality
    (isoReductionIntegralInverse l E g) ((NatTrans.mapHomologicalComplex
      (eqToIso (coefficientSequenceRestriction_evaluation l E Y n)).hom (.up ℤ)).app C))]
  erw [reassoc_of% (roos_reindex_projection l E g S hFst (podRestrictedTower l E C) n)]
  rw [← DerivedCategory.Q.map_comp]
  erw [strict_restricted l E g S hGen C n]
  rw [DerivedCategory.Q.map_comp, DerivedCategory.Q.map_comp]
  erw [← reassoc_of% (roosProjection_natural l E (S.restricted C).hom n)]
  have hL := hlimit C
  dsimp only [PodReindexingDerivedCoreData.assemble] at hL
  erw [reassoc_of% hL]
  erw [← reassoc_of% (projection_formula l E X Q.targetRoos
    (((integralComparisonSequencePullback l E g).mapHomologicalComplex (.up ℤ)).obj C) n)]
  rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  simp only [Category.assoc]
  erw [hev']
  simp only [Functor.map_comp, Category.assoc, Functor.mapIso_hom, Iso.app_hom]
  erw [Functor.mapDerivedCategoryFactors_hom_naturality]
  erw [← reassoc_of% ((coefficientSequenceProjection l E X n).naturality
    ((integralComparisonSequencePullback l E g).mapDerivedCategoryFactors.hom.app C))]

end WeilConjectures
