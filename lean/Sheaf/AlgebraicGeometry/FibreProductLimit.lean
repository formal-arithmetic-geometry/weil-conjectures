/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Fibre products commute with inverse limits of schemes

Source: Stacks Project, Categories, Lemma 4.14.10 (Tag 002M), limit clause;
blueprint node `lem-kun-fibre-product-limits` (blueprint: lem-kun-fibre-product-limits).
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- (blueprint: lem-kun-fibre-product-limits) For a compatible diagram of cospans of schemes,
the canonical map from the limit of the fibre products to the fibre product of the limits is
an isomorphism (Stacks Project, Categories, Tag 002M, limit clause). A map into the source is
a compatible family of maps into each fibre product. Its components are compatible pairs of
maps into `X` and `Y` with equal composites into `S`. The limit universal properties turn
these into a pair of maps into the limits of `X` and `Y` with equal composites into the limit
of `S`. The target fibre product represents the same pairs, and the comparison acts as the
identity on them, so it is invertible. -/
theorem Scheme.isIso_limit_pullback_comparison
    {J : Type w} [Category.{v} J]
    (X Y S : J ⥤ Scheme.{u}) (f : X ⟶ S) (g : Y ⟶ S)
    [HasLimit X] [HasLimit Y] [HasLimit S] [HasLimit (pullback f g)] :
    IsIso (pullback.lift (f := limMap f) (g := limMap g)
      (limMap (pullback.fst f g))
      (limMap (pullback.snd f g)) (by
        apply limit.hom_ext (F := S)
        intro j
        simp only [Category.assoc, limMap_π]
        rw [← Category.assoc, limMap_π, ← Category.assoc, limMap_π]
        simpa only [Category.assoc, NatTrans.comp_app] using
          congrArg (fun a : pullback f g ⟶ S => limit.π (pullback f g) j ≫ a.app j)
            (pullback.condition (f := f) (g := g)))) := by
  sorry

end AlgebraicGeometry
