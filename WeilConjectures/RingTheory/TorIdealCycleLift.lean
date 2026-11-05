/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.Ideal.Quotient.Defs

import Mathlib.LinearAlgebra.TensorProduct.Quotient
import Mathlib.Algebra.BigOperators.Fin

/-! # Lifts of cycles in a quotient tensor complex
Source: Stacks Project, Algebra, proof of Tag 00M5 and Remark 00M6.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.MonoidalCategory
open scoped TensorProduct BigOperators
namespace ModuleCat

end ModuleCat
