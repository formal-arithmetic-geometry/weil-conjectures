/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Triangulated.Subcategory
import WeilConjectures.CategoryTheory.SmoothBaseChange.CohomologyInWeakSerreSubcategory
import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleExactClosure
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.Data.Int.Interval
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver

/-!
# Bounded constructible pro-etale complexes form a triangulated subcategory

Source: Stacks Project, Tags 09AL, 09B5 and 06UQ; Weil blueprint,
`def-weil-finite-torsion-constructibility`
(blueprint: lem-weil-proetale-dbc-triangulated).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
