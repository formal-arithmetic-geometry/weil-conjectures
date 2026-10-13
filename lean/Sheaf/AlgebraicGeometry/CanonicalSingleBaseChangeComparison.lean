/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.AlgebraicGeometry.Picard.CanonicalSinglePullbackComparison
public import Sheaf.AlgebraicGeometry.Picard.CanonicalSingleDirectImageComparison
public import Sheaf.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import Sheaf.AlgebraicGeometry.ModuleBaseChangeMapOpenRestriction
import Sheaf.AlgebraicGeometry.DerivedBaseChangeUnitCompatibility

/-! # Derived exchange on a single module

Source: Stacks Project, Tag 08HY, the mate construction and its derived unit compatibility.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- Derived exchange commutes with the two canonical single-module comparisons.
This identity concerns an arbitrary module and has no structure-sheaf unit maps.
Source: Stacks Project, Tag 08HY, the mate construction.
(blueprint: lem-sc-canonical-single-base-change-comparison).

Proof: Apply derivedBaseChange_unit_compatibility at the homotopy single of M.
Precompose with derived pullback of the localized inverse single-map comparison
for pushforward f. Postcompose with derived pushforward of the localized single-map
comparison for tensor pullback p, followed by the single of the adjunction-preserving
isomorphism from tensor pullback to ordinary pullback. Naturality of the selected
left-derived counit moves the first comparison to its source; naturality of the
right-derived unit moves the second comparison to its target. The single-map
comparisons intertwine the termwise ordinary exchange with the single of ordinary
exchange: evaluate in degree zero, where the comparison maps are the canonical
single-object identifications, and in every other degree the source is zero.
The comparison from tensor to ordinary g-pullback cancels its inverse. Localizing
this identity and reassociating gives the equation. All steps are naturality,
functoriality and isomorphism cancellation, so no flatness, acyclicity, cartesianness
or nonemptiness of schemes is required. -/
theorem canonicalSingleBaseChangeComparison
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (p : X' ⟶ X)
    (h : p ≫ f = f' ≫ g) (M : X.Modules) :
    (derivedPullback g).map (canonicalSingleDirectImageMap f M) ≫
      schemeDerivedBaseChangeMap f f' g p h
        ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M) ≫
      (schemeDerivedDirectImage f').map (canonicalSinglePullbackMap p M) =
    canonicalSinglePullbackMap g ((pushforward f).obj M) ≫
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings S'.toRingedSpace)) 0).map
        (((Classical.choose (exists_tensorPullbackAdjunction g)).leftAdjointUniq
          (pullbackPushforwardAdjunction g)).inv.app ((pushforward f).obj M) ≫
          moduleBaseChangeMap f f' g p h M ≫
          (pushforward f').map
            (((Classical.choose (exists_tensorPullbackAdjunction p)).leftAdjointUniq
              (pullbackPushforwardAdjunction p)).hom.app M)) ≫
      canonicalSingleDirectImageMap f' ((pullback p).obj M) := by sorry

end AlgebraicGeometry.Scheme.Modules
