/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
public import Mathlib.RingTheory.Spectrum.Prime.Module
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.Grp.Zero
/-! # Elementwise torsion for an affine model of a supported target

Source: Stacks Project, Tag 08EJ, affine support paragraph, and Tag 06Z0.
(blueprint: new-affine-restricted-homology-support).
-/
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits
set_option autoImplicit false
end AlgebraicGeometry.Scheme
