/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import WeilConjectures.CategoryTheory.ConstantScalarRealization.ConstantRealizationDerivedScalarExtensionSupplement

/-! # Derived scalar extension for ordinary modules

Source: Stacks Project Tags 06YY and 07A6 (blueprint: def-zl-ring-derived-scalar-extension).

This module records the canonical ordinary-module derived restriction and its left
adjoint used by the condensed evaluation statement.  The underlying constructions are
those of the published constant-realization module, with no alternate choice of derived
functor.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe r wR wS wT

open CategoryTheory

namespace CategoryTheory.RingDerivedScalarExtension

end CategoryTheory.RingDerivedScalarExtension
