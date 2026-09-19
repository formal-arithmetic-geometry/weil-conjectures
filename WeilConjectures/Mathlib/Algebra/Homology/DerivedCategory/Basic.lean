/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# The single functors of a derived category and the localization functor

`DerivedCategory.Q_obj_single_obj` records that the localization functor takes a complex
concentrated in a single degree to the corresponding object of
`DerivedCategory.singleFunctor`. This file adds the companion statement for morphisms.
-/

@[expose] public section

open CategoryTheory Category Limits

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- The definitional equality underlying `DerivedCategory.singleFunctorIsoCompQ`, at the
level of morphisms. -/
lemma Q_map_singleFunctor_map (n : ℤ) {X Y : C} (f : X ⟶ Y) :
    Q.map ((CochainComplex.singleFunctor C n).map f) = (singleFunctor C n).map f :=
  rfl

end DerivedCategory
