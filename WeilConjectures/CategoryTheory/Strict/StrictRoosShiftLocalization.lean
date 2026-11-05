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
public import Mathlib.CategoryTheory.Shift.CommShift
import Mathlib.CategoryTheory.Shift.Localization
import WeilConjectures.CategoryTheory.ProductShift.ProductCommShift
import WeilConjectures.CategoryTheory.SignedCoconeShift.SignedMappingCoconeShift

/-!
# Signed strict Roos shifts and prescribed localization

Source: Stacks Project, Tag 014E, definition-cone; Tag 011G,
definition-shift-cochain; Tag 04VG, localization universal property
(blueprint: lem-a1-strict-roos-shift-localization).

The strict functor and inclusion are `roosF` and `roosι`. Natural tower index `n`
represents positive index `n+1`. The localization categories, their universes and
localization functors are arbitrary prescribed choices.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v uT vT uD vD

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

open CochainComplex

namespace StrictRoosShiftProof

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]

section LimitModel
variable [HasLimitsOfShape ℕᵒᵖ A]

attribute [local instance] baseLimit_additive

end LimitModel

attribute [local instance] levelCommShift

attribute [local instance] productShift

attribute [local irreducible] productShiftComponent

attribute [local instance] transitionEndomorphism_shift

attribute [local irreducible] roosShiftMap

attribute [local irreducible] roosCommShift

variable [HasLimitsOfShape ℕᵒᵖ A]

end StrictRoosShiftProof

open StrictRoosShiftProof

end CategoryTheory
