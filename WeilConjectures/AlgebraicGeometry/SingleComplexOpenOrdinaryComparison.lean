/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenTensorRestrictionIso
public import WeilConjectures.AlgebraicGeometry.OpenDerivedAdditiveStalkIso
public import WeilConjectures.AlgebraicGeometry.AffineSpectrumOrdinaryComparisonSquare
public import WeilConjectures.AlgebraicGeometry.StalkComparisonPullbackNaturality
import WeilConjectures.Algebra.Homology.BaseDerivedTensorRingTransport
import WeilConjectures.AlgebraicGeometry.OpenOrdinaryTensorGermTransport

/-! # Open restriction of the ordinary tensor comparison

Source: Stacks Project, perfect.tex, equation-bc before Tag 0DJ8 and Tag 0DJ9.
(blueprint: lem-pc-single-complex-open-ordinary-comparison).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace AlgebraicGeometry
open SingleComplexBaseChange
set_option synthInstance.maxSize 2048

end AlgebraicGeometry
