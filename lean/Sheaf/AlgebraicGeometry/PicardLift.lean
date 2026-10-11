/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Sheaf.AlgebraicGeometry.TensorPullback

/-! # Lifting invertible modules along closed immersions in dimension at most one

Source: Stacks Project, Varieties, Lemma 09NY
(blueprint: lem-sc-pic-lift-closed-immersion-dim-le-one).
-/

universe u

open CategoryTheory
open TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- Every invertible module on a closed subscheme of a Noetherian scheme of dimension at most one
lifts to an invertible module on the ambient scheme.
Source: Stacks Project, Varieties, Lemma 09NY
(blueprint: lem-sc-pic-lift-closed-immersion-dim-le-one).

Proof:
1. Let `I` be the quasi-coherent ideal defining `i` (`def-weil-closed-immersion`).
   Restriction of units gives the short exact sequence
   `0 → (1 + I) ∩ O_Xˣ → O_Xˣ → i_* O_Zˣ → 0`.
2. Apply `lem-sc-noetherian-cohomology-vanishing-abelian-dim-one` to the kernel to obtain
   `H²(X, (1 + I) ∩ O_Xˣ) = 0`. The long exact sequence from
   `def-sc-topological-abelian-cohomology` makes `H¹(X, O_Xˣ) → H¹(X, i_* O_Zˣ)` surjective.
3. Apply `lem-sc-cohomology-closed-immersion-pushforward` with degree one and `O_Zˣ` to
   identify the target with `H¹(Z, O_Zˣ)`.
4. Apply `thm-sc-hilbert-90` to `X` and `Z` to identify these groups with their Picard groups.
   By `lem-sc-picard-h1-restriction-compatibility`, this map is pullback of invertible modules.
   Surjectivity therefore gives an invertible `L` with `i* L ≅ N` for every invertible `N`.
-/
theorem exists_isInvertible_tensorPullback_iso_of_isClosedImmersion
    {X Z : Scheme.{u}} [NoetherianSpace X] (i : Z ⟶ X) [IsClosedImmersion i]
    (hdim : topologicalKrullDim X ≤ 1) :
    ∀ (N : Z.Modules), N.IsInvertible →
      ∃ (L : X.Modules), L.IsInvertible ∧
        Nonempty ((tensorPullback i).obj L ≅ N) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
