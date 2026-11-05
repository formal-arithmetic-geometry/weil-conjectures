/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.Ample
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.AlgebraicGeometry.Modules.InvertiblePullbackTensor
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
import Mathlib.RingTheory.Noetherian.Nilpotent
import WeilConjectures.AlgebraicGeometry.AmpleIso
import WeilConjectures.AlgebraicGeometry.AmplePullback
import WeilConjectures.AlgebraicGeometry.Ample.AmpleSquareZeroThickening

/-! # Ampleness on a Noetherian reduction

Source: Stacks Project, Cohomology of Schemes, Lemma 09MS
(blueprint: lem-sc-ample-on-reduction-noetherian).

The invertibility of the pullback `i^*L` (the node's parenthetical) is the first clause of
the landed `Scheme.Modules.invertible_pullback_tensor`
(lem-weil-pbc-invertible-pullback-tensor); it is not restated here.
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry

universe u

end AlgebraicGeometry
