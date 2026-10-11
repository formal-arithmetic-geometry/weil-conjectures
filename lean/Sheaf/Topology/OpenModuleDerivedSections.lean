/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
import Sheaf.Topology.OpenModuleCohomology
import Sheaf.AlgebraicGeometry.RingedSpaceDerivedDirectImage
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # Unbounded derived sections of modules over an open

Source: Stacks Project, Cohomology, Tag 0D60 and Injectives, Tag 079P
(blueprint: def-pc-open-module-derived-sections).
-/

universe a b c

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

/-- `RΓ(U,-)` is the unbounded right derived functor of sections over `U`, computed
by K-injective resolutions: on a K-injective complex it is represented by its
termwise sections (`Functor.rightDerivedFunctorObjQIso`). The K-injective resolutions
of module sheaves come from `moduleGrothendieckAbelian` (as for
`derivedModuleDirectImage`) through
`Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian`. Cohomology over `U` in
integer degree `m` is the composite with `DerivedCategory.homologyFunctor`.
Source: Stacks Project, Cohomology, Tag 0D60
(blueprint: def-pc-open-module-derived-sections). -/
noncomputable abbrev openModuleDerivedSections (X : RingedSpace.{a}) (U : Opens X)
    [HasDerivedCategory.{b} (SheafOfModules.{a} (moduleRings X))]
    [HasDerivedCategory.{c} AddCommGrpCat.{a}] :
    DerivedCategory (SheafOfModules.{a} (moduleRings X)) ⥤
      DerivedCategory AddCommGrpCat.{a} :=
  (openModuleSections X U).rightDerivedFunctor

end AlgebraicGeometry.RingedSpace
