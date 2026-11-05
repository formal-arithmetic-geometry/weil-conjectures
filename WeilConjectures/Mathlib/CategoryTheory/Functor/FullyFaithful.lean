/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Functor.FullyFaithful
public import Mathlib.CategoryTheory.Yoneda

/-!
# Fully faithful functors and the Yoneda embedding

For a fully faithful functor `F : C ⥤ D` and `A : C`, the functor `T ↦ Hom(F T, F A)` is
isomorphic to `T ↦ Hom(T, A)`.
-/

@[expose] public section

universe v u₁ u₂

namespace CategoryTheory.Functor.FullyFaithful

variable {C : Type u₁} {D : Type u₂} [Category.{v} C] [Category.{v} D] {F : C ⥤ D}

/-- For a fully faithful functor `F`, the functor `T ↦ Hom(F T, F A)` is `T ↦ Hom(T, A)`. -/
noncomputable def opCompYonedaObjIso (hF : F.FullyFaithful) (A : C) :
    F.op ⋙ yoneda.obj (F.obj A) ≅ yoneda.obj A :=
  NatIso.ofComponents (fun _ ↦ hF.homEquiv.symm.toIso)
    (fun g ↦ by ext x; exact hF.map_injective (by simp))

end CategoryTheory.Functor.FullyFaithful
