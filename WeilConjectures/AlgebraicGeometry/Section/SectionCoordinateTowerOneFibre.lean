/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoordinateCounitArrows.CoordinateCounitArrows
public import WeilConjectures.AlgebraicGeometry.NoetherianSectionSpecialization.NoetherianEtaleSectionSpecialization
public import WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale
public import WeilConjectures.AlgebraicGeometry.Vector.VectorBundleIntegrationCharts
import WeilConjectures.AlgebraicGeometry.Ordered.OrderedTateSectionPullback
import WeilConjectures.AlgebraicGeometry.DeformationSpace.AffineSpace
import WeilConjectures.AlgebraicGeometry.Section.SectionTowerCounitBaseChange
import WeilConjectures.AlgebraicGeometry.Section.SectionLocalityBaseChange
import all WeilConjectures.AlgebraicGeometry.SectionReesBaseChange.SectionReesBaseChangeEtale
import all WeilConjectures.AlgebraicGeometry.Vector.VectorIntegrationOverlapCoordinates

/-! # The fibre at one of the ordered coordinate-counit orientations

Source: sk-thm-dnc, Local construction, and orientation-charts Step 3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option linter.all false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
open NoetherianSectionSpecialization

attribute [local irreducible] upperStar Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  rightDerivedUpperShriek rightDerivedUpperShriekAdjunction

attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option maxHeartbeats 1000000

end AlgebraicGeometry.Etale
