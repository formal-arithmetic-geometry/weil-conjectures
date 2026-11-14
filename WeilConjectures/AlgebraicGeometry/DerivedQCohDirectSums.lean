/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.CategoryTheory.Limits.FullSubcategory
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSumsAux


/-! # Direct sums in the quasi-coherent derived category -/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For every scheme `X`, the derived category of `𝒪_X`-modules whose cohomology
sheaves are quasi-coherent has all set-indexed direct sums. -/
theorem derivedQCohDirectSums (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    HasCoproducts.{u} (schemeDerivedQCohCategory X) := by
  let : HasCoproducts.{u} (schemeDerivedCategory X) :=
    derivedAmbientHasCoproducts X
  let (I : Type u) :
      (schemeDerivedQCohProperty X).IsClosedUnderColimitsOfShape (Discrete I) :=
    schemeDerivedQCohClosedUnderCoproducts X I
  intro I
  exact hasColimitsOfShape_of_closedUnderColimits (Discrete I) (schemeDerivedQCohProperty X)

end AlgebraicGeometry
