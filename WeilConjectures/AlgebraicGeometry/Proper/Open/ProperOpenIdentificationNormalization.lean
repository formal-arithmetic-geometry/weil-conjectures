/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparison
import WeilConjectures.CategoryTheory.Derived.DerivedExactSquareSupplement
import WeilConjectures.SixFunctors.BaseChange.DerivedComparison
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc

/-!
# Unit normalization of the proper/open restriction identification

Source: blueprint thm-cbc-finite-torsion, refinement comparison argument;
Stacks Project, More on Etale Cohomology, Tags 0F7B and 0F7I
(blueprint: lem-weil-pbc-proper-open-identification-unit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategoryPlus
  openImmersionLowerShriekBaseChangeMap
  upperStar lowerStar openImmersionLowerShriek openImmersionLowerShriekUpperStarAdjunction
  derivedOpenImmersionLowerShriekUpperStarAdjunctionPlus
  CategoryTheory.Adjunction.mapDerivedCategoryPlusAdjunction
  pullbackSquareComparison squareUpperStarIso
  CategoryTheory.Functor.mapDerivedCategoryPlusSquareIso
  extensionZeroBaseChangeDerivedPlusIso

attribute [local irreducible] CategoryTheory.Adjunction.derivedPlus
  upperStarLowerStarAdjunction upperStarCompDerivedPlus

end AlgebraicGeometry.Etale
