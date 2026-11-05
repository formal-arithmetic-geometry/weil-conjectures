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
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Cofinal subsequence comparison of strict Roos complexes

Source: Stacks Project, Cohomology on Sites, Tag 0941, lemma-derived-limit-is-ok;
More on Algebra, Tag 0H9K, lemma-pro-isomorphism-iso-Rlim, explicit product maps.
The strict cochain refinement is the nine-step agent proof of
(blueprint: lem-fix-cofinal-roos-restriction).

Positive indices are encoded by their predecessors. Thus an order embedding `φ`
represents the positive-index function `n + 1 ↦ φ n + 1`. The two product maps
are real constructions; the theorem specifies one family of cone maps by both
coordinates, so its existential quantifier leaves no choice of cone completion.
-/

@[expose] public section

set_option autoImplicit false

universe u v uC vC r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CofinalRoos

section Algebra

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

variable {B : Type u} [Category.{v} B] [Preadditive B] [HasCountableProducts B]

-- Reindex the middle object of a composite before simplifying transition maps.

-- The least selected index lying above i, including the initial unselected block.

-- Extend compatible coordinates by the transition from the next selected index.

-- Put zero in every coordinate outside the image of the subsequence.

-- A finite sum, even when the first selected index is positive.

end Algebra

section Complexes

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]

attribute [local instance] complexProducts

-- The product contraction gives a homotopy equivalence before shifting.

end Complexes

end CategoryTheory.CofinalRoos
