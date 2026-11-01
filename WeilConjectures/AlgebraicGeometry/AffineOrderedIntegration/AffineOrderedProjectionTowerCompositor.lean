/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedProjectionTower
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedProjectionTowerWitnessDescent
import WeilConjectures.AlgebraicGeometry.AffineOrderedIntegration.AffineOrderedProjectionTowerRawImage

/-! # Identification of the proper/open tower with the actual origin compositor

Source: the compositor-comparison step of the ordered affine calculation; Stacks 0F7J
(blueprint: lem-pur-affine-projection-tower-compositor).
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

/-- The explicit proper/open map is the actual descended origin compositor.
This is an equation of compositor components only; it contains no tensor or projection.
Source: lem-pur-compact-support-site-coherence and the actual-compositor clause of
lem-pur-affine-ordered-integration-transposes, Step 3.
(blueprint: lem-pur-affine-projection-tower-compositor).

Proof: first evaluate at the comparison image of a bounded-below ordinary complex.
The site comparison of a change of compactification identifies towerCandidateComparison
with the canonical proper-refinement comparison. The proper/open mate square,
proper direct-image composition square, and open-extension composition square
identify projectionTowerMap with the ordinary compatible-tower compositor.
Pasting these squares with the two compactification changes gives
originCompositionModel, with its specified normalizations. The composition site
equation ensures it is this model, rather than an unspecified isomorphism of left
adjoints. Descend equality through comparisonUpperStarPlusEtaleOrigin, which is an
equivalence; naturality transports the equation along its counit to every full-origin
object. Proof irrelevance removes dependence on its retained witness. -/
theorem projection_tower_compositor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian T] [IsNoetherian Y]
    (f : X ⟶ T) (g : T ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    [HasCompactification f] [HasCompactification g] [HasCompactification (f ≫ g)]
    (M : C A X)
    (hM : DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} A) X M) :
    normalizedProjectionTowerMap A f g M hM =
      projectionOriginComponent A f g M hM := by
  apply projection_tower_witness_descent A f g M hM
  intro L
  exact projection_tower_raw_image A f g
    (HasCompactification.compactification g)
    ((HasCompactification.compactification (f ≫ g)).ofComp
      (HasCompactification.compactification g)) L

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
