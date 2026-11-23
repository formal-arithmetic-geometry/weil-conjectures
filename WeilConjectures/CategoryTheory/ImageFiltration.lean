/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.PBCFiltration

/-!
# Image filtrations
-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The image filtration on `B` induced by a filtered object `(A, F)` and a
morphism `f : A ⟶ B` sends each step `FⁿA` to its image in `B`.
-/
noncomputable def PBCDecreasingFiltration.image {A B : C}
    (F : PBCDecreasingFiltration A) (f : A ⟶ B) : PBCDecreasingFiltration B where
  step i := (Subobject.«exists» f).obj (F.step i)
  antitone_step := by
    intro i j hij
    exact leOfHom ((Subobject.«exists» f).map (homOfLE (F.antitone_step hij)))

end CategoryTheory
