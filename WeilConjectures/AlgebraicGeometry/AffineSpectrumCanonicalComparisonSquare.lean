/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineSpectrumDerivedCoordinates
public import WeilConjectures.AlgebraicGeometry.IsoPullbackStalkCohomology
public import WeilConjectures.AlgebraicGeometry.StalkComparisonPullbackNaturality
public import Mathlib.CategoryTheory.Comma.Arrow
import WeilConjectures.AlgebraicGeometry.AffineSpectrumOrdinaryComparisonSquare
import WeilConjectures.AlgebraicGeometry.AffineSpectrumCounitSquare

/-! # The affine spectrum counit square on the canonical representative

Source: Stacks Project, Tag 0DJ8, affine reduction; Tags 0098 and 0D5S.
(blueprint: lem-pc-affine-spectrum-canonical-comparison-square).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.SingleComplexBaseChange

private theorem comparisonIntoPullback_eq
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X X' S S' : Scheme.{u}}
    (f : X ⟶ S) (f' : X' ⟶ S') (g : S' ⟶ S) (g' : X' ⟶ X)
    (sq : IsPullback g' f' f g) (z : X')
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hc : IsIso ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P)))
    (i : ℤ) :
    comparisonIntoPullback f f' g g' sq z P hc i =
      comparisonIntoTensorPullback f f' g g' sq z P i ≫
        (comparisonStalkCohomology X' z i).map
          (inv ((counit g').app ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) := by
  simp only [comparisonIntoPullback, comparisonIntoTensorPullback, Category.assoc]

end AlgebraicGeometry.SingleComplexBaseChange
