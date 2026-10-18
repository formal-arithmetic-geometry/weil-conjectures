/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q20
-/
module

public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Product
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Segre

/-!
# Composition of H-projective morphisms

Source: Stacks Project, Morphisms of Schemes, Tag 01WE,
Lemma `lemma-H-projective-composition` (blueprint: lem-trf-h-projective-composition).

This module records the stage-2 statement for the composition lemma.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A composite of H-projective morphisms is H-projective.

Source: Stacks Project, Morphisms of Schemes, Tag 01WE,
Lemma `lemma-H-projective-composition` (blueprint: lem-trf-h-projective-composition).

Proof plan:
1. Unfold `IsHProjective` (def-kun-projective) to choose closed immersions
   `i : X ⟶ ℙ(n; Y)` and `j : Y ⟶ ℙ(m; S)` over their bases, with finite coordinate types.
2. Apply `ProjectiveSpace.isPullback_map` to `j`
   (lemma-nagata-projective-space-base-change-pullback). The induced map
   `ℙ(n; Y) ⟶ ℙ(n; ℙ(m; S))` is a base change of `j`, hence a closed immersion
   (lem-weil-pbc-closed-immersion-base-change); its square commutes.
3. Apply the same cartesian-square theorem to the projection `ℙ(m; S) ⟶ S`,
   then swap the fibre-product factors to identify the iterated projective space with
   `ℙ(n; S) ×_S ℙ(m; S)`. Composing with `i` gives a closed immersion `k` into this
   product (lem-weil-pbc-closed-immersion-comp). The square shows that its structure
   morphism is `g ≫ h`.
4. Compose `k` with the Segre closed immersion (lem-chow-segre) into
   `ℙ(n × m; S)`. The composite is a closed immersion over `S`, and `n × m` is finite.
   This is the factorization required by def-kun-projective. For coordinate types of
   sizes `N + 1` and `M + 1`, the target has dimension `N * M + N + M`, as in Tag 01WE.
-/
theorem IsHProjective.comp {X Y S : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ S)
    [IsHProjective g] [IsHProjective h] : IsHProjective (g ≫ h) := by
  sorry

end AlgebraicGeometry
