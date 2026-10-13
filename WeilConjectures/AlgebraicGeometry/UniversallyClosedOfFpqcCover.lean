/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import WeilConjectures.AlgebraicGeometry.FpqcLocalOnBaseCriterion

/-!
# Descent of universal closedness along fpqc coverings

Source: Stacks Project, Descent, Lemma Tag 02KS, descent direction of Definition Tag 02KO
(blueprint: lem-weil-pbc-fpqc-descend-universally-closed).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Universal closedness descends along an fpqc covering family.
Source: Stacks Project, Descent, Lemma Tag 02KS
(blueprint: lem-weil-pbc-fpqc-descend-universally-closed).

Proof:
1. Universal closedness respects isomorphisms, by
   `lem-weil-pbc-universally-closed-isomorphism` (`universallyClosed_respectsIso`).
2. It is stable under arbitrary, hence flat, base change, by
   `lem-weil-pbc-universally-closed-base-change`.
3. It is Zariski local on the base, by `lem-weil-pbc-universally-closed-zariski-local`.
4. For a flat surjection between affine schemes the covering map is affine, hence
   quasi-compact. Descent along a surjective flat quasi-compact morphism gives the
   affine case, as in `lem-weil-pbc-universally-closed-affine-descent`.
5. These are conditions (0)-(3) of `lem-weil-pbc-fpqc-local-on-base-criterion` (Tag 02KP).
   Apply that criterion to the given fpqc family (`def-weil-pbc-fpqc-covering`) and the
   universally closed second projections to conclude that `f` is universally closed.
-/
theorem universallyClosed_of_fpqc_cover {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v}
    (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (h : ∀ i, UniversallyClosed (pullback.snd f (g i))) : UniversallyClosed f := by
  refine fpqc_local_on_base_criterion (P := @UniversallyClosed) ?_ ?_ f g hg h
  · intro X S T f g _ hf
    exact MorphismProperty.pullback_snd f g hf
  · intro S T X _ _ f g hflat hsurj hclosed
    exact MorphismProperty.of_pullback_snd_of_descendsAlong
      (P := @UniversallyClosed) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ⟨⟨hsurj, hflat⟩, inferInstance⟩ hclosed

end AlgebraicGeometry
