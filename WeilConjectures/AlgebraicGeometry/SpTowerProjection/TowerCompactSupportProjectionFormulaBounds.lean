/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerProjection.TowerCompactSupportProjectionFormulaCore
import all WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerBound
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarExtensionFunctor
import WeilConjectures.Algebra.Homology.ProperBaseChange.KFlatResolutionGeneral
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel

/-! Uniform lower bounds for the two tensors occurring in compact support.

Source: blueprint paragraph (3), bounds part of
`lem-sp-tower-compact-support-projection-formula`.
(blueprint: lem-sp-tower-compact-support-projection-formula)

Use the uniform Tor interval of the first input and a cohomological lower bound
of the second input. Exact pullback preserves the latter bound. At each finite
level, compare the recorded tensor with the canonical derived tensor using K-flat
models, and apply the bounded-flat tensor estimate. Exact evaluation detects the
resulting tower bound. The open projection isomorphism and exact extension by zero
then give the same lower bound for the second tensor.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.SpTowerProjection

open SpTowerShriek

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

end AlgebraicGeometry.ProEtale.SpTowerProjection
