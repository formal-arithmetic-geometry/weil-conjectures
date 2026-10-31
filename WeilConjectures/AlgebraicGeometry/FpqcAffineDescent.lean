/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Descent of affine morphisms along fpqc coverings

Source: Stacks Project, Descent, Lemma Tag 02L5, descent direction
(blueprint: lem-weil-pbc-fpqc-descend-affine).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- (blueprint: lem-weil-pbc-fpqc-descend-affine) Stacks Project, Descent, Tag 02L5:
a morphism is affine if its base changes along an fpqc covering family are affine.

Proof:
1. The source library proves descent of affineness along surjective flat quasi-compact
   morphisms (Stacks Tag 02L5), using flat base change of global sections and descent of
   the canonical morphism to the spectrum of global sections.
2. The given fpqc precover generates a covering sieve of the fpqc topology.
3. Apply the source library's covering-family descent theorem to `IsAffineHom`, using
   the canonical pullback squares and the hypotheses on their second projections.
-/
theorem isAffineHom_of_fpqc_cover {X S : Scheme.{u}} (f : X ⟶ S) {I : Type v}
    (S' : I → Scheme.{u}) (g : ∀ i, S' i ⟶ S)
    (hg : Presieve.ofArrows S' g ∈ Scheme.fpqcPrecoverage S)
    (h : ∀ i, IsAffineHom (pullback.snd f (g i))) : IsAffineHom f := by
  have := IsAffineHom.descendsAlong_surjective_inf_flat_inf_quasicompact
  exact Scheme.of_isPullback_of_ofArrows_mem_fpqcTopology (P := @IsAffineHom)
    (Precoverage.generate_mem_toGrothendieck hg) f
    (fun i ↦ pullback.fst f (g i)) (fun i ↦ pullback.snd f (g i))
    (fun i ↦ IsPullback.of_hasPullback f (g i)) h

end AlgebraicGeometry
