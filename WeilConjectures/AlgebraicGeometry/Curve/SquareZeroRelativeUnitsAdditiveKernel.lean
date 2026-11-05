/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import WeilConjectures.AlgebraicGeometry.Curve.SquareZeroRelativeSectionKernel
import WeilConjectures.AlgebraicGeometry.Curve.SquareZeroUnitsAdditiveKernelOfSections

/-! # A square-zero closed immersion identifies its unit and additive kernels.

Source: blueprint `lem-sc-brauer-zero-all-curves`, Proof, Step 1 and its Claim;
the affine argument in `lem-sc-nil-ideal-units-additive-image-comparison`.
(blueprint: lem-sc-square-zero-relative-units-additive-kernel)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
