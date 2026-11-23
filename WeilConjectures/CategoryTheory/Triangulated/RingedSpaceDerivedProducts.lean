/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution

/-!
# Products in the derived category of a ringed space

Source: Stacks Project, Injectives, Tag 07D9.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicGeometry Opposite

namespace AlgebraicGeometry.RingedSpace

/-- The derived category of modules on a ringed space has products indexed by every set
(the abelian structure is Mathlib's `SheafOfModules.instAbelian`).
Source: Stacks Project, Injectives, Tag 07D9. -/
theorem derivedProducts (X : RingedSpace.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X))] :
    HasProducts.{u} (DerivedCategory (SheafOfModules.{u} (moduleRings X))) := by
  have : IsGrothendieckAbelian.{u} (SheafOfModules.{u} (moduleRings X)) :=
    (SheafOfModules.grothendieckAbelian_and_functorial_kInjective_resolutions
      (Opens.grothendieckTopology X) X.sheaf).1
  have : Abelian.HasKInjectiveResolutions (SheafOfModules.{u} (moduleRings X)) :=
    CategoryTheory.Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  intro J
  infer_instance

end AlgebraicGeometry.RingedSpace
