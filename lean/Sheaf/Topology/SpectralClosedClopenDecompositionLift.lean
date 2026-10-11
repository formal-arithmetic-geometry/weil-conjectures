/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Connected.Basic

/-! # Lifting clopen decompositions from a closed spectral subspace

Source: Stacks Project, Etale Cohomology, Tag 0CAM, `lemma-connected-topological`
(blueprint: lem-weil-pbc-spectral-closed-clopen-decomposition-lift).
-/

universe u

open Set TopologicalSpace

namespace TopCat

/-- Source: Stacks Project, Etale Cohomology, Tag 0CAM, `lemma-connected-topological`.
(blueprint: lem-weil-pbc-spectral-closed-clopen-decomposition-lift)

A closed decomposition of `Z` extends to the spectral space `X` when `Z` meets each point
closure in a nonempty connected set.

Proof:
1. The relatively closed pieces `Z₁` and `Z₂` are closed in `X` and quasi-compact, since `X`
   is spectral (`def-weil-spectral-space`).
2. Let `Wᵢ` consist of points whose closure meets `Zᵢ`. By
   `lem-weil-pbc-spectral-generalizations-of-quasi-compact`, each is an intersection of
   quasi-compact opens. These opens are retrocompact by quasi-separatedness, hence
   constructible (`def-weil-constructible-subset`). Thus `Wᵢ` is proconstructible.
3. The nonempty connected intersection of each point closure with `Z` meets exactly one
   piece (`def-weil-connected-scheme`), so `W₁` and `W₂` are disjoint and cover `X`.
4. For `x` in the closure of `W₁`,
   `lem-weil-pbc-spectral-proconstructible-closure-specialization` supplies `x₁ ∈ W₁`
   specializing to `x`. Choose a point of `Z` in the closure of `x`. It also lies in the
   closure of `x₁`, which cannot meet `Z₂` by step 3. The point therefore lies in `Z₁`,
   giving `x ∈ W₁`. Hence `W₁` is closed; symmetrically `W₂` is closed.
5. Set `Xᵢ = Wᵢ`. Each `Zᵢ` lies in `Wᵢ`, since a point lies in its own closure.
   Conversely, step 3 excludes points of the other piece from `Z ∩ Wᵢ`. Thus
   `Zᵢ = Z ∩ Xᵢ`, and the required closed decomposition follows. -/
theorem spectral_closed_clopen_decomposition_lift
    (X : TopCat.{u}) [SpectralSpace X]
    (Z : Set X) (hZ : IsClosed Z)
    (hconn : ∀ x : X, ConnectedSpace (↥(Z ∩ closure ({x} : Set X))))
    (Z₁ Z₂ : Set (↥Z))
    (hZ₁ : IsClosed Z₁) (hZ₂ : IsClosed Z₂)
    (hpart : Z₁ ∪ Z₂ = Set.univ) (hdisj : Disjoint Z₁ Z₂) :
    ∃ X₁ X₂ : Set X,
      IsClosed X₁ ∧ IsClosed X₂ ∧ Disjoint X₁ X₂ ∧ X₁ ∪ X₂ = Set.univ ∧
      (Subtype.val '' Z₁) = Z ∩ X₁ ∧ (Subtype.val '' Z₂) = Z ∩ X₂ := by
  sorry

end TopCat
