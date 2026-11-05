/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Linear.FunctorCategory

/-!
# The strict Roos functor on compatible homotopies

Source: Stacks Project, derived.tex, Tags 014E (definition-cone),
08TC (definition-derived-limit), 013H (definition-complexes-notation),
and dga.tex, Tag 09MJ (definition-linear-category).
(blueprint: lem-pur-strict-roos-homotopy-functor)
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory.Limits Opposite

namespace CategoryTheory

universe u v w

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]

end CategoryTheory
