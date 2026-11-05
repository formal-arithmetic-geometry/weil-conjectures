/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import all WeilConjectures.AlgebraicGeometry.Curve.ReductionUnitsEpi

/-! # The image of nil-ideal units is the pushforward of the relative unit kernel.

Source: blueprint `lem-sc-brauer-zero-all-curves`, Proof, Step 1 and its Claim;
the affine argument in `lem-sc-nil-ideal-units-additive-image-comparison`.
(blueprint: lem-sc-nil-ideal-unit-image-relative-kernel)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
