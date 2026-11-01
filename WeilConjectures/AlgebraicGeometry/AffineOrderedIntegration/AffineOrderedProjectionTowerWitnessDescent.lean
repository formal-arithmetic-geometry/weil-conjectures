/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedProjectionTower

/-! Descent of the affine projection tower equation from comparison images.

Source: etale-origin equivalence and naturality in the final paragraph of the
ordered affine projection calculation.
(blueprint: lem-pur-affine-projection-tower-witness-descent).
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

/-- Descent transports the raw tower equation from comparison images to every
witnessed etale-origin object. The raw equation is an explicit hypothesis so this
statement isolates only the equivalence descent and naturality argument.
Source: lem-pur-compact-support-site-coherence, Step 2 (etale-origin descent).
(blueprint: lem-pur-affine-projection-tower-witness-descent).
-/
theorem projection_tower_witness_descent
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian T] [IsNoetherian Y]
    (f : X ⟶ T) (g : T ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (M : C A X)
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M)
    (hraw : ∀ (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
      projectionTowerMap A (HasCompactification.compactification g)
          ((HasCompactification.compactification (f ≫ g)).ofComp
            (HasCompactification.compactification g))
          ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj) =
        towerOriginComposition A f g
          (HasCompactification.compactification g)
          ((HasCompactification.compactification (f ≫ g)).ofComp
            (HasCompactification.compactification g)) L) :
    normalizedProjectionTowerMap A f g M hM =
      projectionOriginComponent A f g M hM := by
  sorry

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
