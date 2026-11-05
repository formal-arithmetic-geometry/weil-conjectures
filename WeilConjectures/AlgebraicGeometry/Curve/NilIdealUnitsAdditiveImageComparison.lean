/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

import WeilConjectures.AlgebraicGeometry.Curve.NilIdealUnitImageRelativeKernel
import WeilConjectures.AlgebraicGeometry.Curve.IdealAdditiveImageRelativeKernel
import WeilConjectures.AlgebraicGeometry.Curve.SquareZeroRelativeUnitsAdditiveKernel

/-! # Linearizing the unit image into the additive image

Source: blueprint `lem-sc-brauer-zero-all-curves`, Proof, Step 1 and its Claim,
as expanded in `lem-sc-nil-ideal-units-image-linearization`, Steps 2 and 3.
(blueprint: lem-sc-nil-ideal-units-additive-image-comparison)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
