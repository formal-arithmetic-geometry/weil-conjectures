/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.KoszulOpenSystem
import WeilConjectures.AlgebraicGeometry.AffineQCohDerivedEquivalenceCore
import WeilConjectures.AlgebraicGeometry.AffineKoszulCechDerivedComparison
import WeilConjectures.AlgebraicGeometry.KoszulOpenHomHomologyComparison
import WeilConjectures.Algebra.Homology.FilteredModuleComplexHomologyZero

/-! # Degree-zero consequences of the Koszul-to-Čech comparison

Source: Stacks Project, Tag 08DD, proof of Proposition 36.9.5.
-/

@[expose] public section

universe uMain wMain
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry
