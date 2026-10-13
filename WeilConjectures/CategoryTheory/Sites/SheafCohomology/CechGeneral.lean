/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-! Compatibility name for the existing equal-universe Čech double-complex comparison. -/

@[expose] public section

namespace CategoryTheory

/-- The existing Čech double-complex comparison, under its original enough-injectives
and equal-universe assumptions. This compatibility name reuses the existing theorem;
it does not assert the previously disputed independent-universe extension.

Source: blueprint sk-thm-picard-cech, Steps 1--3.
Proof: apply `Sheaf.exists_cechDoubleComplex`, which constructs the injective-resolution
bicomplex and supplies its column and total homology comparisons.
(blueprint: stage3-cech-general-double-complex)
-/
alias Sheaf.exists_cechDoubleComplex_general := Sheaf.exists_cechDoubleComplex

end CategoryTheory
