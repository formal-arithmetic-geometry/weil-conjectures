/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

/-! # Limit of a tower of cochain complexes -/

@[expose] public section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex

/-- A tower of cochain complexes in an abelian category with countable products has a limit.
Source: Stacks Tag 002N. -/
theorem hasLimit_asFunctor (A : Type u) [Category.{v} A] [Abelian A]
    [HasCountableProducts A] (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : HasLimit I.asFunctor := by
  have : HasCountableProducts (CochainComplex A ℤ) := ⟨fun _ ↦ inferInstance⟩
  exact hasLimit_of_equalizer_and_product I.asFunctor

end CochainComplex
