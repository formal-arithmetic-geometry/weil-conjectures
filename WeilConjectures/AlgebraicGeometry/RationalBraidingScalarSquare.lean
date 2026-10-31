/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteRationalDerivedOperations
public import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorConstraints
public import WeilConjectures.AlgebraicGeometry.SfRationalizationKaroubi
public import WeilConjectures.AlgebraicGeometry.AlgebraicallyClosedCoefficients

/-! # Rational braiding and scalar-extension square

Source: literature/stacks-project/sites-cohomology.tex, Tag 0FPQ
(blueprint: lem-pur-rational-braiding-scalar-extension-square).
-/
/- The unchanged scalar-square declaration lives beside the finite-stage braiding in
`DerivedPullbackTensorConstraintCore`, before its common-stage use. The public import
above preserves this module's interface without an import cycle. -/
