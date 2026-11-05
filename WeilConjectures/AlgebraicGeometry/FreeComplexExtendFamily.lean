/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! Recursive extension of a comparison map along an exact resolution.
Source: literature/stacks-project/algebra.tex, Tag 00LS.
(blueprint: lem-weil-pbc-free-complex-extend-family).
-/

@[expose] public section

universe u

open CategoryTheory

