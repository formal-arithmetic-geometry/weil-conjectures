/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Affine.Linear.AffineLinearUniversalAction
import WeilConjectures.SixFunctors.Etale.Derived.InvertibleRestriction
import WeilConjectures.SixFunctors.Etale.Derived.CoefficientsShift

/-! # Identity detection on the universal linear parameter scheme

Source: linear-trace invariance, proof paragraphs 1 and 2.
(blueprint: lem-amb-affine-linear-action-rigidity).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

end AlgebraicGeometry.Etale
