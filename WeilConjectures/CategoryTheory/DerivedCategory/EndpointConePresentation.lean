/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.CommutativeSquareLift
import WeilConjectures.CategoryTheory.DerivedCategory.ConeSquareUnrotation

/-! # Cone models with prescribed endpoint components -/

@[expose] public section

universe u v w
open CategoryTheory CategoryTheory.Limits Pretriangulated
set_option autoImplicit false

