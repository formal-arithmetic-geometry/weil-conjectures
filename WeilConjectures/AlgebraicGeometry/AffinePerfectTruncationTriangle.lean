/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.AffineLiftEventualFreeKernels
import WeilConjectures.AlgebraicGeometry.FiniteFreeStupidTailPerfect
import WeilConjectures.AlgebraicGeometry.ExactFunctorStupidTailTriangle

/-! # Arbitrarily low perfect truncation triangles on affine schemes

Source: Stacks Project, Tag 08EG, proof of Lemma 36.13.6, finite-free lift and truncation
(blueprint: lem-sc-affine-perfect-low-truncation-triangle).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry.Scheme
