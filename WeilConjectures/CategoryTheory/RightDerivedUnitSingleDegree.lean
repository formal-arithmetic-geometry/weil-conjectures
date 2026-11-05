/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.RightDerivedSingleDegreeComparison
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus
import WeilConjectures.CategoryTheory.SupportedComplexSingleRealization
import WeilConjectures.CategoryTheory.RightDerivedCanonicalSingleUnit

/-! # Normalization of the derived unit on a single-degree complex

Source: Stacks Project, derived.tex, Tag 015J, computation by an injective resolution.
-/

@[expose] public section

universe uB vB uC vC
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

variable {B : Type uB} [Category.{vB} B] [Abelian B] [IsGrothendieckAbelian.{vB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C]
  [HasDerivedCategory B] [HasDerivedCategory C]
  (G : B ⥤ C) [G.Additive] [PreservesFiniteLimits G]

end CategoryTheory.Functor
