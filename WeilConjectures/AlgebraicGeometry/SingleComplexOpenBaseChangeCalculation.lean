/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenBaseChangeComparisons
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenCounitCompatibility
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPullbackCube

/-! # Residual calculation for explicit open base-change comparisons

Source: Stacks Project, Tags 08FE, 08HY and 0DJ9.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

-- Use the constructed functors through their interfaces during the mate calculation.
attribute [local irreducible] singleComplexOpenDirectImageIso singleComplexOpenPullbackIso
  CategoryTheory.Functor.mapDerivedCategory CategoryTheory.Functor.rightDerivedFunctor
  singleComplexRestrictedCoefficient singleComplexOpenBaseChangeSourceIso
  singleComplexOpenPullbackSquareIso schemeDerivedBaseChangeMap singleComplexOpenSquareComparison

private theorem compose_of_equal
    {C : Type*} [Category* C] {A B D E H : C}
    {x x' : A ⟶ H} {u u' : A ⟶ B} {v v' : B ⟶ D}
    {w w' : D ⟶ E} {z : E ⟶ H}
    (hx : x = x') (hu : u = u') (hv : v = v') (hw : w = w')
    (h : x' = u' ≫ v' ≫ w' ≫ z) : x = u ≫ v ≫ w ≫ z := by
  rw [hx, hu, hv, hw]
  exact h

attribute [local irreducible] CategoryTheory.Adjunction.homEquiv

end AlgebraicGeometry
