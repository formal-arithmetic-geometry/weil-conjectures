/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts

/-!
# Closure under finite products of an inverse image

If `P` is a property of objects of `C` closed under finite products and `F : D ⥤ C` preserves
finite products, then `P.inverseImage F` is closed under finite products.
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open Limits

variable {C D : Type*} [Category* C] [Category* D] (P : ObjectProperty C) (F : D ⥤ C)

instance [P.IsClosedUnderFiniteProducts] [PreservesFiniteProducts F] :
    (P.inverseImage F).IsClosedUnderFiniteProducts where
  isClosedUnderLimitsOfShape _ _ := inferInstance

end CategoryTheory.ObjectProperty
