/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedProjectionTower

/-! The comparison-image calculation for the affine projection tower.

Source: proper/open site normalization and compositor comparison in Stacks 0F7J.
(blueprint: lem-pur-affine-projection-tower-raw-image).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration
open AffineSpacePurity

set_option linter.auxLemma false in
attribute [local instance 100000] AffineSpacePurity.C._proof_1 AffineSpacePurity.C._proof_2

/-- The raw proper/open tower agrees with the origin compositor on comparison images.
This is the proper/open normalization and compactification-pasting part of the proof;
the descent from comparison images is deliberately a separate statement.
Source: lem-pur-compact-support-site-coherence and
lem-sf-proper-open-comparison-site-normalization, Step 1.
(blueprint: lem-pur-affine-projection-tower-raw-image).
-/
theorem projection_tower_raw_image
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian T] [IsNoetherian Y]
    (f : X ⟶ T) (g : T ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (b : Compactification g) (e : Compactification (f ≫ b.i))
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    projectionTowerMap A b e
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj) =
      towerOriginComposition A f g b e L := by
  sorry

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
