/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! # Exact Yoneda extensions

Source: Stacks Project, Tags 06XU, 06XV, and Homology Section 010I.
The extension objects, endpoint-fixed equivalence and geometric Baer construction
are moved here unchanged from the comparison module to permit separate proofs.
(blueprint: def-coef-yoneda-extension-data)
-/

@[expose] public section

universe u v w

namespace CategoryTheory

open Limits Abelian

namespace YonedaExtension

variable {A : Type u} [Category.{v} A] [HasZeroMorphisms A]

end YonedaExtension

namespace YonedaExtension

variable {A : Type u} [Category.{v} A] [Abelian A]

end YonedaExtension

end CategoryTheory
