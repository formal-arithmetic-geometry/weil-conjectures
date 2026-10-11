/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy

/-!
# A trivial Kan fibration is a homotopy equivalence

Source: Stacks Project, Simplicial, Lemma 08NS (label `lemma-trivial-kan-homotopy`),
using Lemma 08NM (label `lemma-trivial-kan`), and Definition 019K (label
`definition-homotopy`) (blueprint: lem-weil-pbc-trivial-kan-homotopy-equivalence).
-/

@[expose] public section

universe u

open CategoryTheory
open MonoidalCategory
open Simplicial

namespace SSet

/-- A trivial Kan fibration admits a section and a simplicial homotopy from the
identity to the composite with that section.

(blueprint: lem-weil-pbc-trivial-kan-homotopy-equivalence)

Source: Stacks Project, Simplicial, Lemma 08NS (`lemma-trivial-kan-homotopy`),
using Lemma 08NM (`lemma-trivial-kan`) and Definition 019K (`definition-homotopy`).

1. Apply `lem-weil-pbc-trivial-kan-lifts-monomorphisms` (08NM) to the degreewise
   injection `∅ ⟶ Y`, the unique map to `X`, and `𝟙 Y`. The lift is a section
   `g : Y ⟶ X` with `g ≫ p = 𝟙 Y`.
2. The boundary of `Δ[1]` consists in every degree of the two constant simplices
   (`def-weil-pbc-trivial-kan-fibration`, `def-weil-pbc-simplicial-set`). Thus
   `X × ∂Δ[1]` is two disjoint copies of `X`, and its inclusion into `X ⊗ Δ[1]`
   is degreewise injective. Map these copies to `X` by `𝟙 X` and `p ≫ g`.
   Map the cylinder to `Y` by its projection to `X` followed by `p`.
   The square commutes: both endpoint maps become `p`, since `g ≫ p = 𝟙 Y`.
3. Apply `lem-weil-pbc-trivial-kan-lifts-monomorphisms` again to this square.
   The lift `h` restricts to `𝟙 X` and `p ≫ g`, giving the displayed equations.
   These equations give the required homotopy; together with the strict section
   equation they make `g` a homotopy inverse to `p`. -/
theorem exists_section_homotopy_equivalence
    {X Y : SSet.{u}} (p : X ⟶ Y)
    (hp : SSet.modelCategoryQuillen.I.rlp p) :
    ∃ (g : Y ⟶ X),
      g ≫ p = 𝟙 Y ∧
        ∃ (h : X ⊗ Δ[1] ⟶ X),
          SSet.ι₀ ≫ h = 𝟙 X ∧ SSet.ι₁ ≫ h = p ≫ g := by
  sorry

end SSet
