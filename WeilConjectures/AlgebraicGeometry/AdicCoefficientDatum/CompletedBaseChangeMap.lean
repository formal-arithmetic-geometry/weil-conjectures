/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedTowerCorners

/-!
# The completed base-change map as the specified ordered composite

Source: blueprint proper base change, completed base-change map; Stacks Tags 09C9 and 099N
(blueprint: def-weil-pbc-completed-base-change-map).

## Main definitions

- `AlgebraicGeometry.Scheme.AdicCoefficientDatum.completedBaseChangeMap`:
  the recorded construction or statement of this node.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe t
open CategoryTheory
namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)
variable {X' X Y' Y : Scheme.{t}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (sq : ChosenCartesianSquare g' f' f g)

end AlgebraicGeometry.Scheme
