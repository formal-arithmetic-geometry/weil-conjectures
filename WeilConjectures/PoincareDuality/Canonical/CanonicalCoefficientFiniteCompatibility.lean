/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.PoincareDuality.Canonical.CanonicalCoefficientPullbackModels
import all WeilConjectures.PoincareDuality.Canonical.CanonicalCoefficientPullbackModels
import all WeilConjectures.PoincareDuality.Canonical.CanonicalCoefficientUnitNormalization
import all WeilConjectures.PoincareDuality.Canonical.CanonicalCoefficientChainNormalization
import all WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure

/-!
# Compatibility of canonical finite coefficient projections

Source: Stacks Tags 03D6 and 08TC; the regular-unit and Roos APIs in
`WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure`.
(blueprint: lem-pod-canonical-coefficient-pullback-reduction).

This module contains proved comparison results and private helpers for the coefficient comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme AlgebraicGeometry.ProEtale

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

attribute [local irreducible] regularExtensionIso regularExtensionPresheafIso
  identityRestrictionIso scalarReductionExistence HasDerivedCategory.standard
  unrestrictedIntegralReductionExistence limit finiteRegularIso finiteSingleRegularIso
  finitePullbackRegularIso pullbackLevelRegularIso pullbackUnitLevel chainUnitCandidate
  integralDerivedPullback integralDerivedPullbackComparison
  constantWeilIntegralRoosComparison
  constantWeilIntegralLambda constantWeilDerivedCoefficientComparison
  SheafOfModules.monoidalCategory constantSheaf
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] canonicalCoefficientIntegralComparison
  canonicalCoefficientInverseImageTransport
  canonicalCoefficientLambda canonicalCoefficientKappa canonicalCoefficientLambdaFinite
  canonicalCoefficientFiniteComparison canonicalCoefficientPullbackReductionIso
  canonicalCoefficientRho canonicalCoefficientProjection canonicalCoefficientInverseProjection
  canonicalCoefficientTheta canonicalCoefficientPullbackTransition canonicalCoefficientTransition
  canonicalCoefficientInverseTransition

attribute [local irreducible] canonicalCoefficientIntegralUnit
  canonicalCoefficientFiniteUnit canonicalCoefficientFiniteKappaComplex
  coefficientFiniteInverseIso coefficientFinitePullIso

attribute [local irreducible] coefficientIntegralInverseIso coefficientProjectionComplex

private theorem coefficientProjection_inverse {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ)
    (h : (canonicalCoefficientTheta l E g).hom ≫ canonicalCoefficientProjection l E X n =
      canonicalCoefficientRho l E g n ≫ DerivedCategory.Q.map
        ((canonicalCoefficientRes l E X n).map
          ((canonicalCoefficientLambdaFinite l E g n).hom ≫
            (canonicalCoefficientFiniteComparison l E g n).hom))) :
    canonicalCoefficientRho l E g n ≫ DerivedCategory.Q.map
        ((canonicalCoefficientRes l E X n).map
          (canonicalCoefficientLambdaFinite l E g n).hom) =
      (canonicalCoefficientLambda l E g).hom ≫
        canonicalCoefficientInverseProjection l E g n := by
  apply (cancel_mono (DerivedCategory.Q.map
    ((canonicalCoefficientRes l E X n).map
      (canonicalCoefficientFiniteComparison l E g n).hom))).1
  have hc : DerivedCategory.Q.map ((canonicalCoefficientRes l E X n).map
      (canonicalCoefficientFiniteComparison l E g n).inv) ≫
      DerivedCategory.Q.map ((canonicalCoefficientRes l E X n).map
        (canonicalCoefficientFiniteComparison l E g n).hom) = 𝟙 _ := by
    rw [← Functor.map_comp, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  simp only [canonicalCoefficientInverseProjection, Category.assoc, hc]
  erw [Category.comp_id]
  simpa only [canonicalCoefficientTheta, Iso.trans_hom, Functor.map_comp,
    Category.assoc] using! h.symm

private theorem coefficientProjectionComplex_one (W : Scheme.{u}) (n : ℕ)
    (U : W.ProEtᵒᵖ) :
    ((coefficientProjectionComplex l E W n).f 0).val.app U
      (constantWeilUnitSection l E W U.unop) =
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit (integralCoefficientSheaf l E W n))).inv.val.app U
        (1 : (integralCoefficientSheaf l E W n).obj.obj U) := by
  let sX := HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit (completedIntegralCoefficientSheafUnrestricted l E W))
  let sB := HomologicalComplex.singleObjXSelf (.up ℤ) 0
    (SheafOfModules.unit (integralCoefficientSheaf l E W n))
  have h : sX.inv ≫ (coefficientProjectionComplex l E W n).f 0 =
      constantCoefficientProjection l E W n ≫
        (scalarReductionRestriction l E W n).map sB.inv := by
    simp only [coefficientProjectionComplex, HomologicalComplex.comp_f,
      Functor.mapCochainComplexSingleFunctor,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
      CochainComplex.singleFunctor, CochainComplex.singleFunctors,
      HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc, sX, sB]
  change ((sX.inv ≫ (coefficientProjectionComplex l E W n).f 0).val.app U)
    (1 : (completedIntegralCoefficientSheafUnrestricted l E W).obj.obj U) = _
  rw [h]
  change sB.inv.val.app U
    ((completedIntegralCommRingProjectionUnrestricted l E W n).hom.app U 1 * 1) = _
  rw [map_one, one_mul]


private theorem coefficientProjectionReduction_one (W : Scheme.{u}) (n : ℕ)
    (U : W.ProEtᵒᵖ) :
    ((coefficientProjectionComplex l E W n ≫
      (canonicalCoefficientRes l E W n).map (finiteSingleRegularIso l E W n).inv).f 0).val.app U
        (constantWeilUnitSection l E W U.unop) =
      constantWeilReducedUnitSection l E W n U.unop := by
  have hinj : Function.Injective (((finiteSingleRegularIso l E W n).hom.f 0).val.app U) := by
    intro x y h
    have h' := congrArg (fun z ↦ ((finiteSingleRegularIso l E W n).inv.f 0).val.app U z) h
    change (((finiteSingleRegularIso l E W n).hom ≫
      (finiteSingleRegularIso l E W n).inv).f 0).val.app U x =
      (((finiteSingleRegularIso l E W n).hom ≫
        (finiteSingleRegularIso l E W n).inv).f 0).val.app U y at h'
    simpa only [Iso.hom_inv_id, HomologicalComplex.id_f, SheafOfModules.id_val,
      PresheafOfModules.id_app, ModuleCat.id_apply] using h'
  apply hinj
  rw [finiteSingleRegularIso_one]
  change ((coefficientProjectionComplex l E W n ≫
    (canonicalCoefficientRes l E W n).map (finiteSingleRegularIso l E W n).inv ≫
    (canonicalCoefficientRes l E W n).map (finiteSingleRegularIso l E W n).hom).f 0).val.app U
      (constantWeilUnitSection l E W U.unop) = _
  rw [← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  exact coefficientProjectionComplex_one l E W n U

private theorem coefficientProjection_step (W : Scheme.{u}) (n : ℕ) :
    coefficientProjectionComplex l E W (n + 1) ≫ canonicalCoefficientTransition l E W n =
      coefficientProjectionComplex l E W n := by
  have hi : (@asIso _ _ _ _ (canonicalCoefficientReductionComplex l E W (n + 1))
      ((canonicalCoefficientModelMaps_isIso l E (𝟙 W)).2 (n + 1)).2.1) =
      finiteSingleRegularIso l E W (n + 1) := by
    apply Iso.ext
    exact coefficientReductionComplex_eq l E W (n + 1)
  let T : W.ProEt := ProEt.mk (𝟙 W)
  apply regular_hom_ext l E W T (MorphismProperty.Over.mkIdTerminal _ W)
  unfold canonicalCoefficientTransition
  rw [hi, coefficientReductionComplex_eq]
  rw [← Category.assoc]
  change ((finiteSingleRegularIso l E W n).hom.f 0).val.app (op T)
    ((((unrestrictedIntegralTransition l E W n).app
      (constantWeilIntegralComplex l E W)).f 0).val.app (op T)
        (((coefficientProjectionComplex l E W (n + 1) ≫
          (canonicalCoefficientRes l E W (n + 1)).map
            (finiteSingleRegularIso l E W (n + 1)).inv).f 0).val.app (op T)
            (constantWeilUnitSection l E W T))) = _
  rw [coefficientProjectionReduction_one, reducedUnit_transition, finiteSingleRegularIso_one]
  exact (coefficientProjectionComplex_one l E W n (op T)).symm

private theorem coefficientProjectionComplex_epi (W : Scheme.{u}) (n : ℕ) :
    Epi (coefficientProjectionComplex l E W n) := by
  let S := CochainComplex.singleFunctor (integralTowerModules l E W) 0
  have : Epi (constantCoefficientProjection l E W n) := quotientProjection_epi l E W n
  have hS : Epi (S.map (constantCoefficientProjection l E W n)) := {
    left_cancellation := by
      intro Z a b hab
      apply HomologicalComplex.from_single_hom_ext
      have he := HomologicalComplex.congr_hom hab 0
      simp only [HomologicalComplex.comp_f, S, CochainComplex.singleFunctor,
        CochainComplex.singleFunctors, HomologicalComplex.single_map_f_self,
        Category.assoc] at he
      simp only [cancel_epi] at he
      exact he }
  unfold coefficientProjectionComplex
  exact (epi_comp_iff_of_isIso _ _).2 hS

private theorem coefficientUnit_epi {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) : Epi (pullbackUnitLevel l E g n) := by
  have h := coefficientUnit_projection l E g n
  have : Epi (pullbackUnitLevel l E g n ≫
      (canonicalCoefficientPullbackReductionIso l E g n).hom ≫
        (canonicalCoefficientRes l E X n).map (coefficientFinitePullIso l E g n).hom) := by
    rw [h]
    exact coefficientProjectionComplex_epi l E X n
  exact (epi_comp_iff_of_isIso (pullbackUnitLevel l E g n)
    ((canonicalCoefficientPullbackReductionIso l E g n).hom ≫
      (canonicalCoefficientRes l E X n).map (coefficientFinitePullIso l E g n).hom)).1
        ‹Epi (pullbackUnitLevel l E g n ≫
          (canonicalCoefficientPullbackReductionIso l E g n).hom ≫
            (canonicalCoefficientRes l E X n).map (coefficientFinitePullIso l E g n).hom)›

/-- Finite multiplication respects the specified quotient transitions as a chain equation.
Source: Stacks 03D6 and 08TC; finite coefficient multiplication and quotient transitions
(blueprint: lem-pod-canonical-coefficient-finite-compatibility).
Proof: precompose with the epimorphic reduced regular unit and postcompose with the
finite coefficient isomorphism. The multiplication formula turns both sides into
coefficient projections; their compatibility follows by checking the regular unit
and the actual reduced-unit transition formula. Cancel the epi and the isomorphism. -/
theorem coefficientStrictTransition {X Y : Scheme.{u}}
    (g : X ⟶ Y) [IsIso g] (n : ℕ) :
    canonicalCoefficientPullbackTransition l E g n ≫
        (canonicalCoefficientRes l E X n).map
          (canonicalCoefficientLambdaFinite l E g n).hom =
      (canonicalCoefficientRes l E X (n + 1)).map
          (canonicalCoefficientLambdaFinite l E g (n + 1)).hom ≫
        canonicalCoefficientInverseTransition l E g n := by
  have := coefficientUnit_epi l E g (n + 1)
  apply (cancel_epi (pullbackUnitLevel l E g (n + 1) ≫
    (canonicalCoefficientPullbackReductionIso l E g (n + 1)).hom)).1
  apply (cancel_mono ((canonicalCoefficientRes l E X n).map
    (canonicalCoefficientFiniteComparison l E g n).hom)).1
  simp only [canonicalCoefficientInverseTransition, Category.assoc,
    ← Functor.map_comp, ← Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.comp_id]
  erw [coefficientFiniteCollapse l E g n, coefficientFiniteCollapse l E g (n + 1)]
  simp only [canonicalCoefficientPullbackTransition, Category.assoc,
    Iso.hom_inv_id_assoc]
  calc
    _ = pullbackUnitLevel l E g n ≫
        (canonicalCoefficientPullbackReductionIso l E g n).hom ≫
        (canonicalCoefficientRes l E X n).map (coefficientFinitePullIso l E g n).hom := by
      rw [← Category.assoc, pullbackUnitLevel_transition]
    _ = coefficientProjectionComplex l E X n := coefficientUnit_projection l E g n
    _ = coefficientProjectionComplex l E X (n + 1) ≫
        canonicalCoefficientTransition l E X n := (coefficientProjection_step l E X n).symm
    _ = _ := by
      rw [← coefficientUnit_projection l E g (n + 1)]
      simp only [Category.assoc]

end WeilConjectures
