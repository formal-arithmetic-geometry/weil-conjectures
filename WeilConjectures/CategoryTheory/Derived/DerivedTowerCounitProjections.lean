/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import
  WeilConjectures.FromJoel.Algebra.Homology.DerivedCategory.DerivabilityStructureKInjectives
import Mathlib.CategoryTheory.Functor.Derived.Adjunction
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
import WeilConjectures.Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives

/-!
# Derived constant towers and the actual inverse-limit counit

Source: Stacks Project, Derived Categories, Tags 09T5 and 0FND;
Cohomology on Sites, Tag 0941 (blueprint: lem-coef-derived-tower-counit-projections).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v wA wT uJ vJ

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable (A : Type u) [Category.{v} A] [Abelian A]

variable [HasLimitsOfShape ℕᵒᵖ A]

variable [HasDerivedCategory.{wA} A] [HasDerivedCategory.{wT} (ℕᵒᵖ ⥤ A)]

end CategoryTheory
