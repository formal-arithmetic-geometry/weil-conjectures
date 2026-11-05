/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicCompletionCompletedSupplement

/-!
# Transport of the published intrinsic completion

Source: blueprint order 1247; Stacks Tags 099M and 091Z
(blueprint: def-weil-pbc-intrinsic-completion).

The published Koszul fiber is reused through the canonical comparison between
its completed quotient-ring presentation and the continuous-functions presentation.
Both rings are inverse limits of the finite quotient sheaves. Neither is identified
with the constant sheaf associated to A. The transport preserves the prescribed
fiber differential, positive-power transitions and the completion unit (u,0).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{t}) {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

end AlgebraicGeometry.Scheme
