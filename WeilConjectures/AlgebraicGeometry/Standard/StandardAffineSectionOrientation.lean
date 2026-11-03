/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows
public import WeilConjectures.AlgebraicGeometry.SectionCoordinateChartMaps.SectionCoordinateChartMaps
import WeilConjectures.AlgebraicGeometry.Coordinate.CoordinateTowerAdjointIsIso
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Unique
import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChange
import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows
import WeilConjectures.AlgebraicGeometry.SectionLocalDualizingComparisons.SectionLocalComparisonData

/-! # Restriction of the normalized standard affine orientation at one

Source: sk-thm-dnc, Local construction, standard model, ordered trace base change.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
open SectionComparisonArrows SectionLocalDualizingComparisons

open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Functor

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

attribute [local irreducible] Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors upperStar

end AlgebraicGeometry.Etale
