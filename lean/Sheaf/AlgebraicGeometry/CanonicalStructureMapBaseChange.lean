/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N4
-/
module

public import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import Sheaf.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Sheaf.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility
import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapAlgebra
import Sheaf.AlgebraicGeometry.Picard.CanonicalSingleAdjunctionTranspose

/-! # Canonical structure maps and derived exchange

Source: Stacks Project, Tag 08HY, the mate description, and Tag 0096.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry

/-- The canonical structure maps commute with the pinned derived exchange map.
No cartesianness, flatness, vanishing or invertibility assumption is needed.
Source: Stacks Project, Tag 08HY, mate description, and Tag 0096, pullback of modules.
(blueprint: lem-sc-canonical-structure-map-base-change).

Proof: Represent each structure map as the single of the ordinary structure map
followed by the canonical right-derived unit. Apply derivedBaseChange_unit_compatibility
at the homotopy single of O_X. Naturality of the single-complex pullback and pushforward
comparisons moves these comparisons through the ordinary exchange. The last clause of
moduleBaseChangeMap_algebra is the ordinary identity:
tensorPullback g applied to f sharp, followed by ordinary exchange and pushforward
of tensorPullbackObjUnitToUnit p, equals tensorPullbackObjUnitToUnit g followed by
f' sharp. It follows by transposition from p f = f' g, using the adjunction triangles.
Localize the single of this identity. Naturality of the right-derived unit moves the
p-structure map to its target, and naturality of the left-derived counit moves f sharp
to its source. The comparisons from tensor to ordinary pullback are the unique maps
preserving the common pushforward adjunction;
therefore canonicalSingleAdjunctionTranspose identifies the remaining composites with
the displayed canonical single maps. Reassociate to obtain the equation. This proof
also applies to empty schemes, where the same functorial and triangle identities hold. -/
theorem canonical_structure_map_base_change
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g) :
    (derivedPullback g).map
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S.toRingedSpace)) 0).map
            (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
          Scheme.Modules.canonicalSingleDirectImageMap f
            (SheafOfModules.unit X.ringCatSheaf)) ≫
      (schemeDerivedBaseChangeMap f f' g p h
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj
            (SheafOfModules.unit X.ringCatSheaf)) ≫
        (schemeDerivedDirectImage f').map
          (Scheme.Modules.canonicalSinglePullbackMap p
              (SheafOfModules.unit X.ringCatSheaf) ≫
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).map
                (SheafOfModules.pullbackObjUnitToUnit p.toRingCatSheafHom))) =
    (Scheme.Modules.canonicalSinglePullbackMap g (SheafOfModules.unit S.ringCatSheaf) ≫
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).map
            (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom)) ≫
      ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).map
            (SheafOfModules.unitToPushforwardObjUnit f'.toRingCatSheafHom) ≫
        Scheme.Modules.canonicalSingleDirectImageMap f'
          (SheafOfModules.unit X'.ringCatSheaf)) := by sorry

end AlgebraicGeometry
