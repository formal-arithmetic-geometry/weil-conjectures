/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.CategoryTheory.ExactDegreeZero

/-!
# A named interface for exact functors on degree-zero objects

The object and morphism functions have their own names. In particular, comparing their
images under a localized functor does not require unfolding the single-degree functor.
The constructions are the canonical Mathlib single functor and its exact-functor comparison.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits

namespace SheafExactDegreeZero

variable {V W X : Type*} [Category V] [Category W] [Category X]
  [Abelian V] [Abelian W] [Abelian X]
  [HasDerivedCategory V] [HasDerivedCategory W] [HasDerivedCategory X]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

universe u

end SheafExactDegreeZero
