/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves
public import Mathlib.CategoryTheory.Monoidal.Preadditive

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-!

# Shortcut instances for monoidal cochain complex

-/

@[expose] public section

universe w v u

open CategoryTheory Limits MonoidalCategory

variable (A : Type u) [Category.{v} A] [Abelian A] [HasColimitsOfSize.{0, 0} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [MonoidalClosed A] [BraidedCategory A]

noncomputable instance :
    MonoidalCategory (HomologicalComplex A (ComplexShape.up ℤ)) :=
  have (X₁ X₂ : GradedObject ℤ A) : X₁.HasTensor X₂ := inferInstance
  inferInstance
