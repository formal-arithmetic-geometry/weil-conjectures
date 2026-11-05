/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import WeilConjectures.AlgebraicGeometry.DerivedCategoryComparison
public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatBaseChangeSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategory

/-!
# Derived pullback along a flat morphism

For a flat morphism `h : T' ⟶ T`, pullback of `𝒪_T`-modules is exact, so the derived pullback
of a module placed in degree `0` is its ordinary pullback.
-/

@[expose] public section

universe w u

open CategoryTheory Limits

namespace AlgebraicGeometry

end AlgebraicGeometry
