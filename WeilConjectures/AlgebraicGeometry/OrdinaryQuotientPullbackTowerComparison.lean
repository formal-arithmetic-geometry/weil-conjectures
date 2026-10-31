/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralComparisonRealizationModels
public import WeilConjectures.AlgebraicGeometry.CompletionUnitModels

import all WeilConjectures.AlgebraicGeometry.IntegralComparisonRealizationModels
import all WeilConjectures.AlgebraicGeometry.CompletionUnitModels
import all WeilConjectures.CategoryTheory.SequenceModulePullbackEvaluation
import all WeilConjectures.AlgebraicGeometry.OrdinaryQuotientPullbackSuccessor

/-! # Strict pullback comparison for ordinary quotient systems

Source: Stacks 06YY, 0941 and 099N(5), the strict quotient-system construction.
(blueprint: lem-trf-ordinary-quotient-pullback-tower-comparison)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe t u v w
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme
namespace WeilConjectures
attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  HasDerivedCategory.standard coefficientSequenceRestriction scalarReductionExtension
  completedIntegralCommRingProjectionUnrestricted
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Ordinary pullback of a strict quotient system is the defining pullback tower,
naturally on all complexes, with the tensor-unit generator normalization.
Source: Stacks 099N(5), 03D2, 0941, pullback of modules and quotient systems.
(blueprint: lem-trf-ordinary-quotient-pullback-tower-comparison).

Proof: at every quotient level, transpose the tensor-unit map through the actual
sequence inverse-image adjunction. The resulting evaluation comparison identifies
sequence inverse image with the finite constant-coefficient inverse image. Compose
with M.evaluation and then restrict coefficients to the completed ring. On unit
generators this sends the image of x to the image of its finite comparison.
These comparisons commute with quotient transitions because both adjuncts are the
same constant-section map followed by the actual quotient reduction. They commute
with differentials and every chain map by naturality of adjunction units. Their
inverses assemble too, giving the natural isomorphism θ on the entire strict tower.
For any strict presentation isomorphism a, pull back a inverse and compose with θ.
Naturality of the sequence inverse-image unit and the finite comparison equation
turn its generator formula into the displayed one. Restriction leaves the section
type unchanged through the recorded casts. No infinite product passes through
inverse image, and this statement uses no derived-limit comparison. -/
theorem ordinaryQuotientPullbackTowerComparison {X Y : Scheme.{t}} (f : X ⟶ Y)
    (M : CompletionUnit.OrdinaryModel l E Y) :
    let T := (integralComparisonSequencePullback l E f).mapHomologicalComplex (.up ℤ) ⋙
      (coefficientSequenceRestriction l E X).mapHomologicalComplex (.up ℤ) ⋙
      HomologicalComplex.complexOfFunctorsToFunctorToComplex
    ∃ θ : M.quotient l E Y ⋙ T ≅ integralOperationsPullbackTowerFunctor l E f,
    ∀ (P : CochainComplex (scalarReductionSource l E Y) ℤ)
      (C : CochainComplex (coefficientSequenceModules l E Y) ℤ)
      (a : (M.quotient l E Y).obj P ≅ C)
      (κ : ∀ n : ℕ,
        ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).obj C ≅
          (unrestrictedIntegralFiniteComplex l E Y n).obj P),
      (∀ n : ℕ,
        ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).mapIso a ≪≫
          κ n = (NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P) →
      ∀ (n : ℕ) (i : ℤ) (U : Y.ProEt) (x : (C.X i).val.obj (op (n, U))),
        (((T.mapIso a.symm ≪≫ θ.app P).hom.app (op n)).f i).val.app
            (op ((proEtaleBaseChange f).obj U))
          (integralComparisonRestrictedSection l E X
            ((integralComparisonSequencePullback l E f).obj (C.X i)) n
            (op ((proEtaleBaseChange f).obj U))
            (integralComparisonSequenceGenerator l E f (C.X i) n U x)) =
          integralOperationsPullbackGenerator l E f n
            (((unrestrictedIntegralFiniteComplex l E Y n).obj P).X i) U
            (((κ n).hom.f i).val.app (op U)
              (coefficientEvaluationSection l E Y (C.X i) n (op U) x)) := by
  dsimp only
  refine ⟨OrdinaryTowerProof.comparison l E f M, ?_⟩
  intro P C a κ hκ n i U x
  simp only [Iso.trans_hom, Iso.app_hom, NatTrans.comp_app, HomologicalComplex.comp_f,
    Functor.mapIso_hom, OrdinaryTowerProof.pullTower_map_app_f,
    OrdinaryTowerProof.comparison_hom_app_f, SheafOfModules.comp_val,
    PresheafOfModules.comp_app, ModuleCat.comp_apply]
  erw [OrdinaryTowerProof.restriction_map_section l E
    ((integralComparisonSequencePullback l E f).map (a.inv.f i)) n
    (op ((proEtaleBaseChange f).obj U))
    (integralComparisonSequenceGenerator l E f (C.X i) n U x)]
  erw [OrdinaryTowerProof.sequenceGenerator_naturality, OrdinaryTowerProof.level_unit]
  congr 1
  have hh :
      ((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex (.up ℤ)).map a.inv ≫
        ((NatIso.mapHomologicalComplex (M.evaluation n) (.up ℤ)).app P).hom =
      (κ n).hom := by
    rw [← hκ n]
    exact (((coefficientSequenceEvaluation l E Y n).mapHomologicalComplex
      (.up ℤ)).mapIso a).inv_hom_id_assoc (κ n).hom
  erw [← OrdinaryTowerProof.evaluation_map_section l E (a.inv.f i) n (op U) x]
  exact congrArg (fun b ↦ (b.f i).val.app (op U)
    (coefficientEvaluationSection l E Y (C.X i) n (op U) x)) hh

end WeilConjectures
