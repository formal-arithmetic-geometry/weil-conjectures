/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffineAlternatingCechModel
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafTerms
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafLocalContraction
import WeilConjectures.AlgebraicGeometry.AlternatingCechSheafAffineComparison

/-! # Augmented increasing-tuple complex of module sheaves

Source: Stacks Project, Tags 01FM, 02KG, 02KH (only its Cech comparison),
and the construction paragraph of
`lem-pc-s3-affine-alternating-cech-resolution-core`.
(blueprint: lem-pc-s3-affine-alternating-cech-augmented-construction).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

end AlgebraicGeometry
