/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.EndoFunctor

/-! # Normalization of the preadditive instance on Weil sheaves -/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

/-- The abelian structure uses the existing preadditive structure. -/
lemma projection_abelian_toPreadditive {C : Type*} [Category* C] [Abelian C]
    (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (abelian F).toPreadditive = (inferInstance : Preadditive (IsoAlgebra F)) := rfl

end CategoryTheory.Endofunctor.IsoAlgebra
