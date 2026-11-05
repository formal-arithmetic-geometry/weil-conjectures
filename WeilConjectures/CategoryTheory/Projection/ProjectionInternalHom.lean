/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Parametrized
import Mathlib.CategoryTheory.HomCongr

/-! # Internal Hom from a support projection formula

The formal argument of steps 9--11 of the open/closed internal Hom calculation.
-/

@[expose] public section

set_option autoImplicit false

universe v w u u'

open CategoryTheory Opposite

namespace CategoryTheory

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{w} D]

variable (tC : C ⥤ C ⥤ C) (hC : Cᵒᵖ ⥤ C ⥤ C)
  (tD : D ⥤ D ⥤ D) (hD : Dᵒᵖ ⥤ D ⥤ D)
  (aC : tC ⊣₂ hC) (aD : tD ⊣₂ hD)
  (e : D ⥤ C) (r : C ⥤ D) (s : C ⥤ D) (q : D ⥤ C)
  (ae : e ⊣ s) (ar : r ⊣ q)
  (φ : ∀ (L : D) (T : C), e.obj ((tD.obj L).obj (r.obj T)) ⟶
    (tC.obj (e.obj L)).obj T)

end CategoryTheory
