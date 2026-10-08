/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.IsConnected
public import Mathlib.Topology.Category.TopCat.Opens

/-!
# The functor of preimages of open subsets is final

For a continuous map `f : X ⟶ Y`, the functor `TopologicalSpace.Opens.map f` is final:
the comma category of open subsets of `Y` whose preimage contains a given open subset of `X`
has `⊤` as a terminal object.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace TopologicalSpace.Opens

variable {X Y : TopCat.{u}}

instance (f : X ⟶ Y) : (Opens.map f).Final where
  out U := isConnected_of_isTerminal _ (IsTerminal.ofUniqueHom
    (Y := StructuredArrow.mk (S := U) (Y := (⊤ : Opens Y))
      (homOfLE (by simp) : U ⟶ (Opens.map f).obj ⊤))
    (fun _ ↦ StructuredArrow.homMk (homOfLE le_top) (Subsingleton.elim _ _))
    (fun _ _ ↦ StructuredArrow.hom_ext _ _ (Subsingleton.elim _ _)))

end TopologicalSpace.Opens

end
