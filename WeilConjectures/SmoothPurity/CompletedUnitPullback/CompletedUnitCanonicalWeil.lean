/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitPullbackData
import WeilConjectures.SmoothPurity.Supporting.ConstantWeilStructure
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitRealizationCoordinate
import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitProjectionExtensionality

/-! # The normalized completed unit and the constant Weil coefficient map -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.CompletedUnitPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (W : Scheme.{u})
private theorem augmentation_projection (r : Reduction l E W (calculus l E W)) (n : ℕ) :
    r.augmentation.hom ≫
      (coefficientSequenceProjection l E W n).app (systemObject l E W) ≫
      (coefficientFiniteDerivedRestriction l E W n).map
        ((evaluationSingle l E W n).hom ≫
          (DerivedCategory.singleFunctor.{u + 2} _ 0).map (r.finite n).hom) =
    (coefficientFiniteAdjunction l E W n).unit.app (integralConstantCoefficientObject l E W) ≫
      (coefficientFiniteDerivedRestriction l E W n).map
        (constantCoefficientReductionMap l E W n) := by
  rw [r.augmentation_eq]
  simp only [Category.assoc]
  rw [reassoc_of% (coefficientSequenceProjection l E W n).naturality r.comparison.hom]
  simp only [← Functor.map_comp]
  rw [r.reduction n]
  simp only [Functor.map_comp, ← Category.assoc]
  rw [(calculus l E W).unit_projection]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app, Category.id_comp]

private theorem augmentation_projection_actual
    (r : Reduction l E W (calculus l E W)) (n : ℕ) :
    r.augmentation.hom ≫
      (coefficientSequenceProjection l E W n).app (systemObject l E W) ≫
      (coefficientFiniteDerivedRestriction l E W n).map
        ((evaluationSingle l E W n).hom ≫
          (DerivedCategory.singleFunctor.{u + 2} _ 0).map (r.finite n).hom) =
    (DerivedCategory.singleFunctor.{u + 2} _ 0).map (constantCoefficientProjection l E W n) ≫
      ((scalarReductionRestriction l E W n).mapDerivedCategorySingleFunctor 0).inv.app
        (SheafOfModules.unit (integralCoefficientSheaf l E W n)) := by
  rw [augmentation_projection l E W r n]
  have h := ((coefficientFiniteAdjunction l E W n).homEquiv
    (integralConstantCoefficientObject l E W) (finiteConstantCoefficientObject l E W n))
    |>.apply_symm_apply
      ((DerivedCategory.singleFunctor.{u + 2} _ 0).map
        (constantCoefficientProjection l E W n) ≫
      ((scalarReductionRestriction l E W n).mapDerivedCategorySingleFunctor 0).inv.app
        (SheafOfModules.unit (integralCoefficientSheaf l E W n)))
  rw [Adjunction.homEquiv_unit] at h
  exact h

omit W in
private theorem core_unit_projection {X Y : Scheme.{u}} (g : X ⟶ Y) (c : Core l E g) (n : ℕ) :
    c.unit.hom ≫
      (DerivedCategory.singleFunctor.{u + 2} _ 0).map (constantCoefficientProjection l E X n) ≫
      ((scalarReductionRestriction l E X n).mapDerivedCategorySingleFunctor 0).inv.app
        (SheafOfModules.unit (integralCoefficientSheaf l E X n)) =
    c.realization.hom.app (integralConstantCoefficientObject l E Y) ≫
      (coefficientSequenceProjection l E X n).app
        ((PrimitiveCounit.pull l E g).obj
          ((calculus l E Y).reduction.obj (integralConstantCoefficientObject l E Y))) ≫
      (coefficientFiniteDerivedRestriction l E X n).map
        ((coefficientSequenceDerivedEvaluation l E X n).map
          ((PrimitiveCounit.pull l E g).map c.reductionY.comparison.hom ≫ systemMap l E g) ≫
          (evaluationSingle l E X n).hom ≫
            (DerivedCategory.singleFunctor.{u + 2} _ 0).map (c.reductionX.finite n).hom) := by
  have h := augmentation_projection_actual l E X c.reductionX n
  calc
    _ = c.unit.hom ≫ (c.reductionX.augmentation.hom ≫
        (coefficientSequenceProjection l E X n).app (systemObject l E X) ≫
        (coefficientFiniteDerivedRestriction l E X n).map
          ((evaluationSingle l E X n).hom ≫
            (DerivedCategory.singleFunctor.{u + 2} _ 0).map
              (c.reductionX.finite n).hom)) := by
      exact congrArg (fun t ↦ c.unit.hom ≫ t) h.symm
    _ = _ := by
      rw [c.unit_formula]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [reassoc_of% (coefficientSequenceProjection l E X n).naturality
        ((PrimitiveCounit.pull l E g).map c.reductionY.comparison.hom ≫ systemMap l E g)]
      simp only [Functor.map_comp, Category.assoc]

/-- Whole-system pullback multiplication reconstructs the actual constant Weil map.

Source: Bhatt--Scholze, Sections 3.5 and 6.5, Lemma 6.8.2; Stacks 0941;
completed-unit-pullback-tower, Steps 4--6, and coefficient-pullback-unit-coordinates.
(blueprint: lem-pur-completed-unit-canonical-weil)

Proof: evaluate the normalized reduction of the regular single complex using
reductionY.reduction. The finite identifications are the identity on sections by
finite_sections. Core.finite_components identifies the pulled system map with actual
finite coefficient-ring multiplication. These maps commute with quotient transitions:
they are adjoints of the same sequence-ring map. Apply Core.realization_model to the
regular flat-term K-flat single complex. Its strict comparison identifies restriction
of that whole-system map with integralChainUnit, including the quotient transitions.
In the normalized Roos realization both augmentations have the quotient projections
as their unshifted coordinates and zero shifted coordinate. Product and mapping-cocone
naturality give equality of these augmented chain maps, before localization. Substitute
unit_formula and reductionX.augmentation_eq; the adjunction triangle cancels the
reconstruction unit against its effective counit. The resulting arrow is integralUnit.
The theorem integralUnit_canonicalWeil identifies it with constantWeilIntegralTheta.
Apply Iso.ext. This uses the complete system, never joint faithfulness of arbitrary
derived evaluations, and also applies to the empty scheme. -/
theorem completedUnitCanonicalWeil
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X Y : Scheme.{u}} (g : X ⟶ Y) [IsIso g] (c : Core l E g) :
    c.unit = constantWeilIntegralTheta l E g := by
  rw [← ConstantGeometricStalkUnit.integralUnit_canonicalWeil l E g]
  let q := ConstantGeometricStalkUnit.integralUnit l E g
  apply Iso.ext
  have hproj (n : ℕ) :
      c.unit.hom ≫ (DerivedCategory.singleFunctor.{u + 2} _ 0).map
          (constantCoefficientProjection l E X n) =
        q.hom ≫ (DerivedCategory.singleFunctor.{u + 2} _ 0).map
          (constantCoefficientProjection l E X n) := by
    have hc := core_unit_projection l E g c n
    have ha := completedUnitRealizationCoordinate_eq_integralUnit l E g c n
    have hcoord :
        c.unit.hom ≫ (DerivedCategory.singleFunctor.{u + 2} _ 0).map
            (constantCoefficientProjection l E X n) ≫
          ((scalarReductionRestriction l E X n).mapDerivedCategorySingleFunctor 0).inv.app
            (SheafOfModules.unit (integralCoefficientSheaf l E X n)) =
          q.hom ≫ (DerivedCategory.singleFunctor.{u + 2} _ 0).map
            (constantCoefficientProjection l E X n) ≫
          ((scalarReductionRestriction l E X n).mapDerivedCategorySingleFunctor 0).inv.app
            (SheafOfModules.unit (integralCoefficientSheaf l E X n)) := by
      calc
        _ = c.realization.hom.app (integralConstantCoefficientObject l E Y) ≫
            completedUnitRealizationCoordinate l E c n := by
          simpa only [completedUnitRealizationCoordinate] using hc
        _ = _ := by simpa only [q] using ha
    apply (cancel_mono
      (((scalarReductionRestriction l E X n).mapDerivedCategorySingleFunctor 0).inv.app
        (SheafOfModules.unit (integralCoefficientSheaf l E X n)))).1
    simpa only [Category.assoc] using hcoord
  exact completedUnit_projection_extensionality l E g q c.unit.hom q.hom hproj

end WeilConjectures.CompletedUnitPullback
