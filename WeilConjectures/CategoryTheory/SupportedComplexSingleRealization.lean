/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusSingle
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Plus

@[expose] public section

universe uB vB
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
namespace DerivedCategory.Plus

variable {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory B]

end DerivedCategory.Plus
