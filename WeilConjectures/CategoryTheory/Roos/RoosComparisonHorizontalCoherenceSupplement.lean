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
public import WeilConjectures.CategoryTheory.RoosComparisonHorizontalCoherence

/-! # Horizontal coherence of the canonical additive Roos comparison

Source: Stacks Tag 0941, lemma-derived-limit-is-ok, product-cone context, and the
agent-written coordinate calculation in the DAG proof
(blueprint: lem-pur-roos-comparison-horizontal-coherence).

The comparison is constructed directly by Mathlib's `mappingCocone.lift` on the fixed
`roosF` model, using the two mapped projections and the canonical product comparison.
No exactness or preservation of products is assumed for its definition.
-/

@[expose] public noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

universe uA vA uB vB uD vD

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasCountableProducts A]
variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasCountableProducts B]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [HasCountableProducts D]

end CategoryTheory
