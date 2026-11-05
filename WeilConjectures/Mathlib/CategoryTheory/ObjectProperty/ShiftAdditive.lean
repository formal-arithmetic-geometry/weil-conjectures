/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive

/-!
# Linearity of the shift functors on a full subcategory

If `C` is an `R`-linear category equipped with a shift by an additive monoid `A`, and
`P : ObjectProperty C` is stable under the shift, then the shift functors on the full
subcategory associated to `P` are `R`-linear if the shift functors on `C` are. This is the
`R`-linear analogue of the additivity instance of
`Mathlib.CategoryTheory.ObjectProperty.ShiftAdditive`.

-/

@[expose] public section

open CategoryTheory Category

namespace CategoryTheory.ObjectProperty

end CategoryTheory.ObjectProperty
