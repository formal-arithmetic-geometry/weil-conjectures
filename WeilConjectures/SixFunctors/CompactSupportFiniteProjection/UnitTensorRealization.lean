/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Equivalence

/-! # The coefficient unit followed by a tensor comparison

## Implementation details

The endpoints of `unitTensorRealization` are stated explicitly, so that consumers can use it
without unfolding a concrete equivalence.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

open CategoryTheory

namespace WeilConjectures.CompactSupportFiniteProjection

/-- Cancel a coefficient equivalence unit, then tensor the specified comparison. -/
def unitTensorRealization
    {A B : Type*} [Category A] [Category B] (R : A ≌ B)
    (T : A ⥤ A ⥤ A) (k : A) {a c : A} (e : a ≅ c) :
    R.inverse.obj (R.functor.obj ((T.obj k).obj a)) ≅
      (T.obj k).obj c :=
  (R.unitIso.app ((T.obj k).obj a)).symm ≪≫ (T.obj k).mapIso e

end WeilConjectures.CompactSupportFiniteProjection
