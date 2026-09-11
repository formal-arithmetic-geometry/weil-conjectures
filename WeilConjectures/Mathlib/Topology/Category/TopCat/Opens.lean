/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Category.TopCat.Opens

/-!
# Taking preimages of open sets along a continuous map

Let `f : X ⟶ Y` be a continuous map. This file records two properties of the functor
`TopologicalSpace.Opens.map f` between the categories of open sets: it is final, and it
sends a family of open sets covering `Y` to a family of open sets covering `X`.

## Main results

- `TopologicalSpace.Opens.final_map`
- `TopologicalSpace.Opens.coversTop_map`
-/

@[expose] public section

universe u

open CategoryTheory

namespace TopologicalSpace.Opens

variable {X Y : TopCat.{u}}

/-- Taking preimages of open sets along a continuous map is a final functor: for every open
subset `U` of `X`, the open subset `⊤` of `Y` is terminal among those whose preimage
contains `U`. -/
instance final_map (f : X ⟶ Y) : (Opens.map f).Final := by
  refine ⟨fun U ↦ ?_⟩
  have : Nonempty (StructuredArrow U (Opens.map f)) :=
    ⟨StructuredArrow.mk (Y := (⊤ : Opens Y)) (homOfLE le_top)⟩
  refine zigzag_isConnected fun A B ↦ ?_
  have h (Z : StructuredArrow U (Opens.map f)) :
      Z ⟶ StructuredArrow.mk (Y := (⊤ : Opens Y)) (homOfLE le_top) :=
    StructuredArrow.homMk (homOfLE le_top) (Subsingleton.elim _ _)
  exact .trans (.of_hom (h A)) (.of_inv (h B))

/-- The preimages of a family of open subsets covering `Y` cover `X`. -/
lemma coversTop_map (f : X ⟶ Y) {ι : Type*} {V : ι → Opens Y}
    (hV : (Opens.grothendieckTopology Y).CoversTop V) :
    (Opens.grothendieckTopology X).CoversTop fun i ↦ (Opens.map f).obj (V i) := by
  rw [Opens.coversTop_iff] at hV ⊢
  simpa [IsOpenCover] using hV.comap f.hom

end TopologicalSpace.Opens
