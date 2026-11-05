/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import all WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import all Mathlib.Algebra.Homology.HomologicalComplexLimits
import all Mathlib.CategoryTheory.Limits.Shapes.Products
import all WeilConjectures.CategoryTheory.DerivedModuleDirectSums

/-! # Statements of the new targets (batch 2) about `GrothendieckDerivedCoproducts`

Kept in their own module so that `Sheaf.CategoryTheory.GrothendieckDerivedCoproducts`,
which the first task's targets use, is unchanged.
-/

@[expose] public section

universe t u v w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

end DerivedCategory
