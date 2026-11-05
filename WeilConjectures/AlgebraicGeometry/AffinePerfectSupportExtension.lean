/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
import WeilConjectures.AlgebraicGeometry.AffinePerfectMapLift
import WeilConjectures.AlgebraicGeometry.AffinePerfectPlusShift
import WeilConjectures.AlgebraicGeometry.AffineSupportIteratedCones
import WeilConjectures.AlgebraicGeometry.AffineSupportPoweredGenerators
import WeilConjectures.AlgebraicGeometry.AffineBinomialProjectorCone
import WeilConjectures.AlgebraicGeometry.PerfectImpliesQCoh
import WeilConjectures.AlgebraicGeometry.PerfectTwoOutOfThree
import WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated

/-! # Affine perfect support extension

Source: Stacks Project, Derived Categories of Schemes, Tag 08EK (Lemma 36.13.10)
(blueprint: lem-sc-affine-perfect-support-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

end AlgebraicGeometry.Scheme
