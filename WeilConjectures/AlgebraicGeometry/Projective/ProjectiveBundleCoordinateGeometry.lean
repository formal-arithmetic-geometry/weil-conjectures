/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleTautologicalData

import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveBundleCoordinateSubschemes
import Mathlib.RingTheory.MvPolynomial.Ideal
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.CoordinateSectionChart
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.ChartPolynomial
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical

/-! # Coordinate geometry of projective space over a field

Source: Stacks Project, Tags 01NG, 01MS, 01WR, 01WX.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry

open ProjectiveSpace

attribute [local irreducible] coordinateSection twist Scheme.Modules.Hom.zeroLocus

end AlgebraicGeometry
