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

/-- The base-change comparison followed by the composition-pinned tensor counit.
This uses the same composition-pinned left-derived counit as the original comparison.
Source: Stacks Project, Tag 08HY (blueprint: lem-pc-pinned-single-base-change-shift). -/
def singleDegreeBaseChangeComposite
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (h : g' ≫ f = f' ≫ g)
    (n : ℤ) (G : X.Modules) :
    (singleDegreeBaseChangeSource.{u, w} f g n).obj G ⟶
      (singleDegreeBaseChangeTarget.{u, w} g' f' n).obj G :=
  let ε := (Classical.choose
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})) g'
  let c : (derivedPullback.{u, w} g').obj
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj G) ⟶
      (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) n).obj
          ((Scheme.Modules.tensorPullback g').obj G) :=
    ε.app ((HomotopyCategory.singleFunctor _ n).obj G) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.tensorPullback g') (ComplexShape.up ℤ) n).hom.app G))
  schemeDerivedBaseChangeMap.{u, w} f f' g g' h
      ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj G) ≫
    (schemeDerivedDirectImage.{u, w, w} f').map c

end AlgebraicGeometry
