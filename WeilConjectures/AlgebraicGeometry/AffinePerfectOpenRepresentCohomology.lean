/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.AffineKoszulCechDerivedComparison
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalence
import WeilConjectures.AlgebraicGeometry.AffinePerfectKoszulPrincipalUnit
import WeilConjectures.AlgebraicGeometry.KoszulComplex
import WeilConjectures.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyCore
import WeilConjectures.AlgebraicGeometry.AffinePerfectOpenRepresentCohomologyColimit

/-! # Koszul perfect objects represent cohomology classes on a principal open

Source: Stacks Project, Section 36.9, Tags 08CX, 08DC, and 08DD
(blueprint: lem-sc-affine-perfect-open-represent-cohomology).
-/

@[expose] public section

universe uMain wMain

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry
