/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus

/-!
# Notation for the right derived functor on the bounded below derived category

We introduce the notation `R+(F)` for
`CategoryTheory.Functor.rightDerivedFunctorPlus F`, the right derived functor
`DerivedCategory.Plus C ⥤ DerivedCategory.Plus D` of an additive functor `F : C ⥤ D`
between abelian categories, where `C` has enough injectives.
-/

@[expose] public section

namespace CategoryTheory

namespace Functor

@[inherit_doc rightDerivedFunctorPlus]
scoped notation "R+(" F ")" => rightDerivedFunctorPlus F

end Functor

end CategoryTheory
