/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.Algebra.Module.Projective

/-! Base-degree lifting for a free module into an exact augmentation.
Source: literature/stacks-project/algebra.tex, Tag 00LS.
(blueprint: lem-weil-pbc-free-complex-base-lift).
-/

@[expose] public section

universe u

open CategoryTheory

