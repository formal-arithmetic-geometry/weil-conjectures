/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
import WeilConjectures.AlgebraicGeometry.Curve.EtaleIdealKernelPresentation
import Mathlib.CategoryTheory.Abelian.Exact

/-! # The additive ideal image and tensor sections

Source: blueprint `lem-sc-brauer-zero-all-curves`, Proof, Step 1 and its Claim,
as expanded in `lem-sc-nil-ideal-units-image-linearization`, Step 1.
(blueprint: lem-sc-additive-ideal-image-tensor-comparison)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

end AlgebraicGeometry.Scheme
