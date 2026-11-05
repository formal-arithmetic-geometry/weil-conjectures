/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.LinearScalarCone.LinearScalarCone
import WeilConjectures.CategoryTheory.SignedCoconeShift.SignedMappingCoconeShift
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TriangleShift
import Mathlib.CategoryTheory.Linear.FunctorCategory

/-! # Exactness and products for the localized scalar cone

Source: Stacks, Tags 06YS and 0941, the bounded finite-free tensor argument.
(blueprint: lem-coef-linear-scalar-cone-exact-products).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe v u w r
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace CochainComplex.LinearScalarCone

open HomComplex

variable {R : Type r} [Ring R] {A : Type u} [Category.{v} A] [Abelian A] [Linear R A]

attribute [local irreducible] first second

attribute [local irreducible] interchangeIso interchangeComponentIso interchangeComponent

attribute [local irreducible] cochainShiftOne

variable [HasDerivedCategory.{w} A]

end CochainComplex.LinearScalarCone
