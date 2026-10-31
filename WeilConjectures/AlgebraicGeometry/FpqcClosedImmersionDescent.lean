/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-!
# Descent of closed immersions along fpqc coverings

Source: literature/stacks-project/descent.tex, Descent, Lemma Tag 02L6
(blueprint: lem-pc-fpqc-descend-closed-immersion).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- (blueprint: lem-pc-fpqc-descend-closed-immersion) Stacks Project, Descent,
Lemma Tag 02L6, descent direction. Each base change is affine because a closed
immersion is affine [lem-weil-pbc-closed-immersion-integral-separated-uc]; hence
`f` is affine by fpqc descent [lem-weil-pbc-fpqc-descend-affine]. Apply flat base
change [lem-pc-flat-base-change-cohom] to `O_X` in degree zero to identify each
base-changed pushforward. A closed immersion has a surjective structure map
[lem-weil-pbc-closed-immersion-affine-cover-criterion]. At each point of the target,
choose a point above it in the cover; the induced local ring map is flat
[def-weil-flat-morphism] and faithfully flat. Surjectivity of the structure map
therefore descends to the original stalk
[lem-pc-local-flat-faithful-flat-reflects-surjective]. Finally, an affine morphism
with surjective structure maps on all target stalks is a closed immersion
[lem-pc-affine-surjective-structure-map-closed-immersion].
-/
theorem isClosedImmersion_of_fpqc_cover {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v}
    (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (h : ∀ i, IsClosedImmersion (pullback.snd f (g i))) : IsClosedImmersion f := by
  -- Use the source library's singleton descent and its extension to covering families.
  have := IsClosedImmersion.descendsAlong_surjective_inf_flat_inf_quasicompact.{u}
  exact Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology
    (P := @IsClosedImmersion) (Precoverage.generate_mem_toGrothendieck hg) f
    (fun i ↦ pullback.fst f (g i)) (fun i ↦ pullback.snd f (g i))
    (fun i ↦ IsPullback.of_hasPullback f (g i)) h

end AlgebraicGeometry
