/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearTraceAction
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearActionFamily
import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearActionRigidity

/-! # Linear changes of coordinates preserve the affine-space counit trace

Source: blueprint sec-smooth-purity/sk-prop-an/lem-amb-linear-trace-invariance.md,
proof paragraphs 1 and 2 (blueprint: lem-amb-linear-trace-invariance).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
