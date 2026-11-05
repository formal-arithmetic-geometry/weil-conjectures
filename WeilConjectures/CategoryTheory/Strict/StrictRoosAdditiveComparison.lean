/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Strict.StrictRoosDerivedLimitComparisonSupplement
public import WeilConjectures.CategoryTheory.StrictTowerArithmetic.StrictTowerArithmeticRestrictionDefs
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-! # Additive comparison for the strict Roos cone

Source: Stacks 08TC and 0H9K; finite-product/cone portion of proof step 7 of
`lem-pur-compact-support-roos-cofinality`.
-/

@[expose] public section

set_option autoImplicit false

universe u v vA vB

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.StrictTowerArithmetic

namespace CategoryTheory

variable {A : Type u} [Category.{vA} A] [Abelian A] [HasCountableProducts A]
open HomologicalComplex
open StrictTowerArithmetic

variable {B : Type v} [Category.{vB} B] [Abelian B] [HasCountableProducts B]

end CategoryTheory
