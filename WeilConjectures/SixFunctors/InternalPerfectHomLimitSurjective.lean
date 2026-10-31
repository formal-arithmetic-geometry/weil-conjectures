/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.AlgebraicGeometry.Perfect.PerfectScalarChangeModel

import WeilConjectures.CategoryTheory.Triangulated.DerivedCountableProductsExistence
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp

/-! # Surjectivity onto compatible finite reduction morphisms

Source: Stacks Project, Tag 09C6, lemma-connected-adic-lisse; current blueprint
`sk-prop-integral-local-structure`, the displayed Milnor surjection.
(blueprint: lem-pe-internal-perfect-hom-limit-surjective)

The source complex `T = B ⊗_A P` is the existing termwise scalar model
`sfbScalarModelComplex` (the constant-sheaf scalar extension of
`det-def-sfb-constructible-local-model`, applied termwise), at the integral coefficients.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.AdicCompletion

attribute [local irreducible] upperStarFromPoint

private theorem restricted_compatible
    {C D A : Type*} [Category C] [Category D] [Category A]
    {U : D ⥤ C} {V : D ⥤ A} {J : A ⥤ D} {R : A ⥤ C}
    (b : V ⊣ J) (e : J ⋙ U ≅ R)
    {M M' : D} {N N' : A} (f : M ⟶ M') (g : N ⟶ N')
    (α : V.obj M ⟶ N) (β : V.obj M' ⟶ N')
    (h : V.map f ≫ β = α ≫ g) :
    U.map f ≫ (U.map (b.unit.app M' ≫ J.map β) ≫ e.hom.app N') =
      (U.map (b.unit.app M ≫ J.map α) ≫ e.hom.app N) ≫ R.map g := by
  have hu : f ≫ b.unit.app M' ≫ J.map β =
      b.unit.app M ≫ J.map α ≫ J.map g := by
    rw [← b.unit_naturality_assoc, ← J.map_comp, h, J.map_comp]
  calc
    _ = U.map (f ≫ b.unit.app M' ≫ J.map β) ≫ e.hom.app N' := by
      simp only [Functor.map_comp, Category.assoc]
    _ = U.map (b.unit.app M ≫ J.map α ≫ J.map g) ≫ e.hom.app N' := by rw [hu]
    _ = _ := by
      simp only [Functor.map_comp, Category.assoc]
      have he : U.map (J.map g) ≫ e.hom.app N' = e.hom.app N ≫ R.map g := by
        simpa only [Functor.comp_map] using e.hom.naturality g
      rw [he]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option maxHeartbeats 1000000 in
-- Allow normalization of the continuous coefficient category and its derived adjunctions.
end AlgebraicGeometry.ProEtale.AdicCompletion
