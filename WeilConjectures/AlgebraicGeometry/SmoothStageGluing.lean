/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# Smoothness at a finite stage from a smooth model

In a Noetherian approximation, a smooth finite-stage model of a pullback morphism, up to
isomorphism over the stage, makes the pullback morphism smooth at that stage.

## References

* [Stacks Project, Tag 0C0C](https://stacks.math.columbia.edu/tag/0C0C)
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- The gluing part of eventual smoothness.  A smooth finite-stage model `q` of the
pullback morphism, i.e. a smooth `q : Z ⟶ N.D.obj j.left` together with a comparison
isomorphism `e : Z ≅ pullback p (N.D.map j.hom)` over `N.D.obj j.left`, makes the pullback
morphism itself smooth at that stage. -/
theorem Scheme.NoetherianApproximation.smooth_stage_of_affine_models
    {S : Scheme.{u}} (N : S.NoetherianApproximation) {i : N.I}
    {Y : Scheme.{u}} (p : Y ⟶ N.D.obj i)
    (hmodel : ∃ (j : Over i) (Z : Scheme.{u}) (q : Z ⟶ N.D.obj j.left)
      (e : Z ≅ pullback p (N.D.map j.hom)),
        e.hom ≫ pullback.snd p (N.D.map j.hom) = q ∧ Smooth q) :
    ∃ j : Over i, Smooth (pullback.snd p (N.D.map j.hom)) := by
  obtain ⟨j, Z, q, e, he, hq⟩ := hmodel
  refine ⟨j, ?_⟩
  have : pullback.snd p (N.D.map j.hom) = e.inv ≫ q := by
    rw [← he, Iso.inv_hom_id_assoc]
  rw [this]
  infer_instance

end AlgebraicGeometry
