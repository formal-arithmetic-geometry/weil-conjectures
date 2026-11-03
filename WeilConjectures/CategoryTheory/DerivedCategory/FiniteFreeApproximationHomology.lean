/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.SixFunctors.FiniteFreeApproximationTriangle
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.Algebra.Homology.BoundedComplexTermAmplitude
import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.LinearAlgebra.Dimension.Free

/-! # Finite free approximation in one homology degree

Source: Stacks Project, Tag 0944, and the current scalar-extension blueprint
clause (2), bpq #46. (blueprint: lem-sp-finite-free-approximation-homology).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w x y z
open CategoryTheory CategoryTheory.Limits
namespace CochainComplex

set_option backward.defeqAttrib.useBackward true in
end CochainComplex

namespace DerivedCategory

end DerivedCategory
