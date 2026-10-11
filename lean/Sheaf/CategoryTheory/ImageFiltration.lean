/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.CategoryTheory.Filtration

/-!
# Image filtrations

Source: blueprint node `def-sp-image-filtration`, order 508
(blueprint: def-sp-image-filtration).
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The image filtration on `B` induced by a filtered object `(A, F)` and a
morphism `f : A ⟶ B` sends each step `FⁿA` to its image in `B`.

Source: blueprint node `def-sp-image-filtration`, order 508
(blueprint: def-sp-image-filtration). -/
noncomputable def DecreasingFiltration.image {A B : C}
    (F : DecreasingFiltration A) (f : A ⟶ B) : DecreasingFiltration B where
  step i := (Subobject.«exists» f).obj (F.step i)
  antitone_step := by
    intro i j hij
    exact leOfHom ((Subobject.«exists» f).map (homOfLE (F.antitone_step hij)))

end CategoryTheory
