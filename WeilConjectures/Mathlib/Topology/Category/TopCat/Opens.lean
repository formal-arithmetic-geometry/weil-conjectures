/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
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

We also record that `TopologicalSpace.Opens.map f` preserves finite products: taking preimages
commutes with `⊤` and with binary intersections.
-/

@[expose] public section

universe u

open CategoryTheory Limits

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

variable (X) in
lemma terminal_eq_top : (⊤_ (Opens X)) = ⊤ :=
  le_antisymm le_top (leOfHom (terminalIsTerminal.from ⊤))

instance isIso_prodComparison_map (f : X ⟶ Y) (U V : Opens Y) :
    IsIso (prodComparison (Opens.map f) U V) :=
  ⟨homOfLE (by rw [CompleteLattice.prod_eq_inf, CompleteLattice.prod_eq_inf]; exact le_rfl),
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- Taking preimages of open sets along a continuous map preserves binary products, i.e.
binary intersections. -/
instance preservesBinaryProducts_map (f : X ⟶ Y) :
    PreservesLimitsOfShape (Discrete WalkingPair) (Opens.map f) :=
  preservesBinaryProducts_of_isIso_prodComparison _

instance isIso_terminalComparison_map (f : X ⟶ Y) :
    IsIso (terminalComparison (Opens.map f)) :=
  ⟨homOfLE (by rw [terminal_eq_top, terminal_eq_top]; exact le_of_eq (Opens.map_top f).symm),
    Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- Taking preimages of open sets along a continuous map preserves the terminal object. -/
instance preservesTerminal_map (f : X ⟶ Y) :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (Opens.map f) :=
  have : PreservesLimit (Functor.empty.{0} (Opens Y)) (Opens.map f) :=
    PreservesTerminal.of_iso_comparison _
  preservesLimitsOfShape_pempty_of_preservesTerminal _

end TopologicalSpace.Opens
