/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Topology.OpenModuleCohomology
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Unbounded derived sections of modules over an open

The unbounded derived functor `RΓ(U, -)` of sections of modules over an open `U`.

## Implementation details

`RΓ(U, -)` is computed by K-injective resolutions: on a K-injective complex it is represented by
its termwise sections (`Functor.rightDerivedFunctorObjQIso`). The K-injective resolutions of
module sheaves come from `moduleGrothendieckAbelian` (as for `derivedModuleDirectImage`) through
`Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`.

## References

* [Stacks Project, Tags 0D60 and 079P](https://stacks.math.columbia.edu/tag/0D60)
-/

@[expose] public section

universe a b c

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- `RΓ(U,-)`, the unbounded right derived functor of sections of module sheaves over `U`.
Cohomology over `U` in integer degree `m` is the composite with
`DerivedCategory.homologyFunctor`. -/
noncomputable abbrev openModuleDerivedSections (X : RingedSpace.{a}) (U : Opens X)
    [HasDerivedCategory.{b} (SheafOfModules.{a} (moduleRings X))]
    [HasDerivedCategory.{c} AddCommGrpCat.{a}] :
    DerivedCategory (SheafOfModules.{a} (moduleRings X)) ⥤
      DerivedCategory AddCommGrpCat.{a} :=
  (openModuleSections X U).rightDerivedFunctor

end AlgebraicGeometry.RingedSpace
