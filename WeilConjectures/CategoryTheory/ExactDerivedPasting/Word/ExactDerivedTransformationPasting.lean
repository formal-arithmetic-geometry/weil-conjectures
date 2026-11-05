/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement

/-! # Pasting arbitrary cells of exact derived functors

Source: Stacks Project, Tags 015F and 04VG, and the natural-transformation enhancement of
localization in `Mathlib.CategoryTheory.Localization.Predicate`.
(blueprint: lem-sp-exact-derived-transformation-pasting)

Words are finite parenthesized composites, including empty words. Expressions record
finite pasting, with no invertibility restriction on their generating cells. A specified
ordinary compositor is included as a cell, in either direction.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe t u v w

open CategoryTheory Limits

namespace CategoryTheory.ExactDerivedPasting

variable {I : Type t} (C : I → Type u) [∀ i, Category.{v} (C i)]
  [∀ i, Abelian (C i)] [∀ i, HasDerivedCategory.{w} (C i)]

end CategoryTheory.ExactDerivedPasting
