/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction
public import WeilConjectures.EtaleCohomology.Purity.Smooth.FrameIndependence
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
/-! # Universal invertible matrices for the affine trace action

Source: linear-trace invariance, proof paragraph 1.
(blueprint: def-amb-affine-linear-universal-action).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry

attribute [local irreducible] Etale.rightDerivedLowerShriek
  Etale.affineLinearCompactComparison Etale.affineLinearCoefficientDescent

namespace Etale

end Etale
end AlgebraicGeometry
