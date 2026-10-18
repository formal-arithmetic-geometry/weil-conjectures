/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q52
-/
module

public import Sheaf.RingTheory.DerivedCompleteModuleComplex
public import Sheaf.CategoryTheory.DerivedCategory.PerfectRingComplexGeneral
import Sheaf.CategoryTheory.DerivedCategory.PerfectRingClassicalGenerator
import Sheaf.RingTheory.DerivedCompleteProductsTriangles
import Sheaf.RingTheory.ModuleLocalizationTowerVanishing

/-!
# Perfect complexes over a derived-complete ring

Source: Stacks Project, More on Algebra, Tags 091S and 0ATI
(blueprint: lem-sf-perfect-over-derived-complete-ring).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- If the degree-zero complex of a commutative ring is derived complete for an ideal,
then every perfect complex over that ring is derived complete for the ideal.

Source: Stacks Project, More on Algebra, Tags 091S and 0ATI
(blueprint: lem-sf-perfect-over-derived-complete-ring).

Proof: The derived-complete objects form a strictly full triangulated subcategory by
`lem-weil-pbc-module-derived-complete-products-triangles` and the triangulated axioms;
the zero object is complete. The localization-tower vanishing criterion
`lem-weil-pbc-module-localization-tower-vanishing` shows that this subcategory is closed
under retracts, hence saturated. The hypothesis puts the degree-zero ring object in
this subcategory. The classical-generator statement
`lem-sf-perfect-ring-classical-generator` says that the perfect objects are the smallest
strictly full, saturated, triangulated subcategory containing that object, so every
perfect object is derived complete.
-/
theorem perfect_of_derivedComplete
    {A : Type u} [CommRing A]
    [HasDerivedCategory.{w} (ModuleCat.{u} A)]
    (I : Ideal A)
    (hA : IsDerivedComplete I
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A))) :
    ∀ (P : DerivedCategory (ModuleCat.{u} A)),
      IsPerfectRingComplex P → IsDerivedComplete I P := by
  sorry

end DerivedCategory
