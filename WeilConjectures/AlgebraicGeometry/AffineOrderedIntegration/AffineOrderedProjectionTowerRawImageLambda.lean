/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompositionTowerDefinitions
import all WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleCompositionTowerNormalization

/-! The invertibility witness for the affine ordered projection tower.

Source: Stacks 0F7J, proper/open site normalization.
(blueprint: lem-pur-affine-projection-tower-raw-image-lambda).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.AffineOrderedIntegration

/-- The comparison-image input admits the invertibility witness required by the
proper/open tower formula, and the resulting open mate is invertible.
Source: proper/open site normalization and compactification-pasting component.
(blueprint: lem-pur-affine-projection-tower-raw-image-lambda).
-/
theorem projection_tower_raw_image_lambda
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X T Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian T] [IsNoetherian Y]
    (f : X ⟶ T) (g : T ⟶ Y)
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated g] [LocallyOfFiniteType g] [QuasiCompact g]
    (b : Compactification g) (e : Compactification (f ≫ b.i))
    (L : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let M := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj
    ∃ hLambda : IsIso (towerLambda A (pullback.fst e.g b.i) b.i e.restrict.g e.g
      e.isPullback_restrict.w.symm ((towerJ A e.restrict.i).obj M)),
      IsIso (towerGamma A (pullback.fst e.g b.i) b.i e.restrict.g e.g
        e.isPullback_restrict.w.symm ((towerJ A e.restrict.i).obj M) hLambda) := by
  let : IsNoetherian b.Z := by
    let : IsLocallyNoetherian b.Z := LocallyOfFiniteType.isLocallyNoetherian b.g
    let : CompactSpace b.Z := QuasiCompact.compactSpace_of_compactSpace b.g
    exact ⟨⟩
  let : IsNoetherian e.Z := by
    let : IsLocallyNoetherian e.Z := LocallyOfFiniteType.isLocallyNoetherian e.g
    let : CompactSpace e.Z := QuasiCompact.compactSpace_of_compactSpace e.g
    exact ⟨⟩
  let : IsNoetherian e.restrict.Z := by
    let : IsLocallyNoetherian e.restrict.Z :=
      LocallyOfFiniteType.isLocallyNoetherian e.restrict.g
    let : CompactSpace e.restrict.Z :=
      QuasiCompact.compactSpace_of_compactSpace e.restrict.g
    exact ⟨⟩
  let M := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj L.obj
  let K := (Etale.openImmersionLowerShriek
    (ModuleCat.{u + 1} A) e.restrict.i).mapDerivedCategoryPlus.obj L
  let N := (towerJ A e.restrict.i).obj M
  let eN : (comparisonUpperStar (ModuleCat.{u + 1} A) e.restrict.Z).mapDerivedCategory.obj
      K.obj ≅ N :=
    DerivedCategory.Plus.ι.mapIso ((properOpenSiteExtensionIso A e.restrict.i).app L)
  let sq := e.isPullback_restrict.flip
  have hw := tower_witness_isIso A sq N K eN
  simpa only [sq, N, M] using hw

end AlgebraicGeometry.ProEtale.AffineOrderedIntegration
