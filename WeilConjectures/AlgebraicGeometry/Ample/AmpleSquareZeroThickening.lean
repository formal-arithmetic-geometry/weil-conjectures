/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.AlgebraicGeometry.FiniteSurjectiveAffineTargetNoetherian
import WeilConjectures.AlgebraicGeometry.Square.SquareZeroSectionPowerLocus
import WeilConjectures.AlgebraicGeometry.NonvanishingSectionTrivializes
import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula

/-! # Ampleness lifts along a square-zero thickening

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS, square-zero case
(blueprint: lem-sc-ample-square-zero-thickening).

The invertibility of the pullback `j^*L` is the first clause of the landed
`Scheme.Modules.invertible_pullback_tensor` (lem-weil-pbc-invertible-pullback-tensor);
it is not restated here.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

end AlgebraicGeometry.Scheme.Modules
