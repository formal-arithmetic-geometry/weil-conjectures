/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Linear.LinearFunctor

/-!
# Lifts of linear functors to full subcategories are linear

If `F : C ⥤ D` is an `R`-linear functor whose essential image is contained in a full subcategory
`P` of `D`, the lift `P.lift F hF : C ⥤ P.FullSubcategory` is `R`-linear, for the `R`-linear
structure on `P.FullSubcategory` induced from `D` (`CategoryTheory.Linear.fullSubcategory`).
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

variable (R : Type*) [Semiring R] {C D : Type*} [Category* C] [Category* D] [Preadditive C]
  [Preadditive D] [Linear R C] [Linear R D] (P : ObjectProperty D) (F : C ⥤ D)
  (hF : ∀ X, P (F.obj X))

/-- The lift of an `R`-linear functor to a full subcategory is `R`-linear. -/
instance lift_linear [F.Linear R] : (P.lift F hF).Linear R where
  map_smul f r := P.fullyFaithfulι.map_injective (F.map_smul r f)

end CategoryTheory.ObjectProperty
