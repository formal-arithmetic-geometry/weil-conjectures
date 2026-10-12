/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedModuleBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Sheaf.AlgebraicGeometry.BaseChangeMapCech
import Sheaf.AlgebraicGeometry.CechResolution
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.AlgebraicGeometry.ModulePullbackAffineSections

/-! # Canonical relatively flat module base change

Source: Stacks Project, Tag 0A1D, and the finite affine Cech proof of
`lem-pc-rf-base-change-flat-module`.
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Relative flatness makes the canonical base-change map with ordinary module target
invertible, for any cartesian square. This does not assert that the derived-to-ordinary
pullback comparison itself is invertible.

Source: Stacks Project, Tag 0A1D; blueprint `lem-pc-rf-base-change-flat-module`,
Steps 1--5, and `lem-pc-base-change-map-cech`.
(blueprint: lem-pc-relatively-flat-canonical-module-base-change).

Proof: Take the left-derived counit of tensor pullback at G[0] and compose it with
singleMapHomologicalComplex to obtain c. This is the comparison characterized by
IsDerivedModulePullbackComparison. On affine opens of S and S', choose a finite
ordered affine cover of the inverse image in X. Separatedness makes its intersections
affine. The finite alternating Cech complex computes Rf_*G. Relative flatness makes
all its terms flat over the base ring; hence its derived pullback is ordinary tensor
pullback. The affine section-pullback formula identifies this tensor complex with
the Cech complex for the pulled-back module. The comparison respects restrictions
and hence differentials. By baseChangeMap_cech the resulting isomorphism is exactly
schemeDerivedBaseChangeMap followed by Rf'_*c. Check invertibility on cohomology
sheaves locally to conclude globally. For a general cartesian square, identify X'
with the chosen pullback using its unique projection-preserving isomorphism. The
pullback-composition comparisons and their adjunction mates commute with this
identification, so the formula and invertibility transport. The empty cover computes
zero on an empty scheme, so no nonemptiness assumption is needed. -/
theorem exists_isIso_canonicalModuleBaseChange_of_isFlatOver
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [IsSeparated f]
    (g : S' ⟶ S) (g' : X' ⟶ X) (f' : X' ⟶ S')
    (sq : IsPullback g' f' f g) [(Scheme.Modules.tensorPullback g').Additive]
    (G : X.Modules) [SheafOfModules.IsQuasicoherent.{u} G]
    (hflat : Scheme.Modules.IsFlatOver G f) :
    ∃ c : (derivedPullback g').obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ⟶
        (DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0).obj
            ((Scheme.Modules.tensorPullback g').obj G),
      IsDerivedModulePullbackComparison g' G c ∧
        IsIso (schemeDerivedBaseChangeMap f f' g g' sq.w
            ((DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G) ≫
          (schemeDerivedDirectImage f').map c) := by sorry

end AlgebraicGeometry
