/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparison
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricFiberFinite
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-!
# Proper pushforward of extension by zero

Source: blueprint, sec-smooth-purity/sk-def-sf-operations,
lem-weil-pbc-proper-open-comparison-iso, order 1482
(blueprint: lem-weil-pbc-proper-open-comparison-iso).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

-- The fully faithful inclusion detects zero objects via cohomology.

-- Lift the existing disjoint-range vanishing to D⁺ using exactness.

-- The derived unit is invertible, so the right triangle makes the restricted counit
-- invertible. No computation of the construction of the specified identification is needed.

end AlgebraicGeometry.Etale
