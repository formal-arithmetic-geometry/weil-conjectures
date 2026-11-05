/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.AlgebraicGeometry.PinnedBaseChangeMateShifts
import WeilConjectures.AlgebraicGeometry.PinnedSingleTensorShifts

/-! # Shift covariance of the pinned single-complex base-change composite
Source: Stacks Project, Tags 08FE, 08HY, 08IB and 0D5U.
(blueprint: lem-pc-pinned-single-base-change-shift). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency.types false

/-- The source functor of the base-change comparison on single complexes.
Source: Stacks Project, Tag 08HY (blueprint: lem-pc-pinned-single-base-change-shift). -/
def singleDegreeBaseChangeSource
    {X S S' : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S'.toRingedSpace))]
    (f : X ⟶ S) (g : S' ⟶ S) (n : ℤ) :
    X.Modules ⥤ schemeDerivedCategory.{u, w} S' :=
  ((DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n ⋙
    schemeDerivedDirectImage.{u, w, w} f) ⋙ derivedPullback.{u, w} g)

/-- The target functor after applying the single-complex tensor counit.
Source: Stacks Project, Tag 08HY (blueprint: lem-pc-pinned-single-base-change-shift). -/
def singleDegreeBaseChangeTarget
    {X X' S' : Scheme.{u}}
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X'.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S'.toRingedSpace))]
    (g' : X' ⟶ X) (f' : X' ⟶ S') (n : ℤ) :
    X.Modules ⥤ schemeDerivedCategory.{u, w} S' :=
  ((Scheme.Modules.tensorPullback g' ⋙ DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) n) ⋙ schemeDerivedDirectImage.{u, w, w} f')

end AlgebraicGeometry
