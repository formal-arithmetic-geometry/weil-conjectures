/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.IntegralComparisonRealizationModels
public import Sheaf.Paper.CompletionUnitModels

/-! # Section casts of ordinary quotient systems

Source: Stacks 03D7 and 0941, sectionwise restriction of modules.
(blueprint: lem-trf-ordinary-quotient-scalar-section-casts).
-/

@[expose] public noncomputable section
set_option linter.privateModule false
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective
universe t u v
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace WeilConjectures
namespace OrdinaryScalarTowerProof
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
  (L : Type u) [Field L] [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L]
  (ι : E →ₐ[ℚ_[l]] L) (W : Scheme.{t})

attribute [local irreducible] completedIntegralCommRingSheafUnrestricted
  integralScalarReduction scalarReductionExtension coefficientSequenceRestriction
  completedIntegralCommRingProjectionUnrestricted constantSheaf
attribute [local implicit_reducible] integralCoefficientCommRingSheaf
  SemilinearSections.systemRing
  coefficientSequenceCommRingSheaf coefficientSequenceCommRingPresheaf
  Functor.mapHomologicalComplex HomologicalComplex.complexOfFunctorsToFunctorToComplex

private theorem evaluation_section_heq {X : Scheme.{t}}
    (N : coefficientSequenceModules l E X) (n : ℕ) (U : X.ProEtᵒᵖ)
    (x : N.val.obj (op (n, U.unop))) :
    HEq (coefficientEvaluationSection l E X N n U x) x := by rfl

private theorem evaluation_map_section {X : Scheme.{t}}
    {N N' : coefficientSequenceModules l E X} (g : N ⟶ N')
    (n : ℕ) (U : X.ProEtᵒᵖ) (x : N.val.obj (op (n, U.unop))) :
    (((coefficientSequenceEvaluation l E X n).map g).val.app U)
      (coefficientEvaluationSection l E X N n U x) =
    coefficientEvaluationSection l E X N' n U
      (g.val.app (op (n, U.unop)) x) := rfl

private theorem eqToHom_section {C : Type v} [Category C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    {N N' : SheafOfModules.{u} R} (h : N = N') (U : Cᵒᵖ) (x : N.val.obj U) :
    HEq ((eqToHom h).val.app U x) x := by
  subst N'
  rfl

private theorem restrictionEvaluation_section {X : Scheme.{t}}
    (N : coefficientSequenceModules l E X) (n : ℕ) (U : X.ProEtᵒᵖ)
    (x : N.val.obj (op (n, U.unop))) :
    (((eqToIso (coefficientSequenceRestriction_evaluation l E X n)).app N).hom.val.app U)
      (integralComparisonRestrictedSection l E X N n U x) =
        coefficientEvaluationSection l E X N n U x := by
  simp only [Iso.app_hom, eqToIso.hom, eqToHom_app]
  apply eq_of_heq
  have h := eqToHom_section
    (congrArg (fun F ↦ F.obj N) (coefficientSequenceRestriction_evaluation l E X n))
    U (integralComparisonRestrictedSection l E X N n U x)
  have hc : HEq (integralComparisonRestrictedSection l E X N n U x) x :=
    cast_heq (integralComparisonRestrictedSectionType l E X N n U).symm x
  exact (h.trans hc).trans (evaluation_section_heq l E N n U x).symm

private theorem cast_map {A A' B B' : Type v} (hA : A = A') (hB : B = B')
    (f : A → B) (g : A' → B') (h : HEq f g) (x : A') :
    f (cast hA.symm x) = cast hB.symm (g x) := by
  cases hA
  cases hB
  exact congrFun (eq_of_heq h) x

private theorem restriction_map_section {X : Scheme.{t}}
    {N N' : coefficientSequenceModules l E X} (g : N ⟶ N')
    (n : ℕ) (U : X.ProEtᵒᵖ) (x : N.val.obj (op (n, U.unop))) :
    ((((coefficientSequenceRestriction l E X).map g).app (op n)).val.app U)
      (integralComparisonRestrictedSection l E X N n U x) =
    integralComparisonRestrictedSection l E X N' n U
      (g.val.app (op (n, U.unop)) x) := by
  have h : HEq (fun y ↦
      ((((coefficientSequenceRestriction l E X).map g).app (op n)).val.app U) y)
      (fun y : N.val.obj (op (n, U.unop)) ↦ g.val.app (op (n, U.unop)) y) := by
    unfold coefficientSequenceRestriction
    exact (coefficientSequenceRestriction_exists l E X).exists.choose_spec.2.2 g n U
  exact cast_map (integralComparisonRestrictedSectionType l E X N n U)
    (integralComparisonRestrictedSectionType l E X N' n U) _ _ h x

private theorem eqToHom_ab_heq {A B : AddCommGrpCat.{v}} (h : A = B) (x : A) :
    HEq ((eqToHom h) x) x := by
  subst B
  rfl

private theorem sequenceSection_heq (N : coefficientSequenceModules l E W)
    (n : ℕ) (U : W.ProEtᵒᵖ)
    (x : ((coefficientSequenceEvaluation l E W n).obj N).val.obj U) :
    HEq (integralComparisonSequenceSection l E W N n U x) x :=
  eqToHom_ab_heq (coefficientSequenceEvaluationAb_eq l E W N n U) x


end OrdinaryScalarTowerProof
end WeilConjectures
