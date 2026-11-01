/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import WeilConjectures.CategoryTheory.Exact.ExactDegreeZeroSupplement
import WeilConjectures.AlgebraicGeometry.FiniteSmoothPurity.FiniteSmoothCoefficientArrows
import WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientLeftUnitCoherence
import WeilConjectures.CategoryTheory.SmoothPurity.CompositeLeftUnitCoherence
import WeilConjectures.CategoryTheory.Tensor.TensorIsoUnitCoherence

/-! # Composition of the transported scalar units

Source: smooth-purity reduction compatibilities, part (3).
(blueprint: lem-pur-finite-smooth-zero-twist-composition).
-/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteSmoothPurity
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify
attribute [local irreducible] Functor.leftAdjoint Functor.rightAdjoint
  Functor.mapDerivedCategory
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

private theorem tensor_naturality_left
    {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (S : C ⥤ D)
    (d : Functor.uncurry.obj (curriedTensor C) ⋙ S ≅
      S.prod S ⋙ Functor.uncurry.obj (curriedTensor D))
    {P Q : C} (a : P ⟶ Q) (M : C) :
    S.map (a ▷ M) ≫ d.hom.app (Q, M) =
      d.hom.app (P, M) ≫ S.map a ▷ S.obj M := by
  have h := d.hom.naturality (show (P, M) ⟶ (Q, M) from (a, 𝟙 M))
  dsimp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map] at h
  change S.map (a ▷ M ≫ Q ◁ 𝟙 M) ≫ d.hom.app (Q, M) = _ at h
  simp only [whiskerLeft_id, Category.comp_id] at h
  change S.map (a ▷ M) ≫ d.hom.app (Q, M) =
    d.hom.app (P, M) ≫ S.map a ▷ S.obj M ≫ S.obj Q ◁ S.map (𝟙 M) at h
  rw [S.map_id, whiskerLeft_id, Category.comp_id] at h
  exact h

end AlgebraicGeometry.Etale.FiniteSmoothPurity
