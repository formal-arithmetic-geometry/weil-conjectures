/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitTowerCone
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable

import Mathlib.Basic.Countable.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-! # Limit cone for a tower of complexes -/

@[expose] public section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory

/-- Existence of a limit cone for a tower of complexes. Source: Stacks Tag 002N. -/
theorem derivedCategory_towerLimit_cone
    (A : Type u) [Category.{v} A] [HasZeroMorphisms A]
    [HasCountableProducts A] [HasEqualizers A] :
    ∀ (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ),
      ∃ c : Cone I.asFunctor, Nonempty (IsLimit c) := by
  intro I
  exact ⟨_, ⟨(limitConeOfEqualizerAndProduct I.asFunctor).isLimit⟩⟩

end CategoryTheory
