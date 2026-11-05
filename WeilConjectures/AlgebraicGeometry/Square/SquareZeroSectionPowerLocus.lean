/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
import WeilConjectures.AlgebraicGeometry.Square.SquareZeroSectionPowerLift
import WeilConjectures.AlgebraicGeometry.NonvanishingTensorPullback
import WeilConjectures.AlgebraicGeometry.SectionNonvanishingZeroLocus
import WeilConjectures.AlgebraicGeometry.Modules.AffineComplement

/-! # Lifting the nonvanishing open of a section across a square-zero immersion

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS, square-zero case,
from the tensor exact sequence through the lifting of a power of a section.
(blueprint: lem-sc-square-zero-section-power-locus).
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

end AlgebraicGeometry.Scheme.Modules
