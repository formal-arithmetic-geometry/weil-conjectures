/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.Paper.ProductExchangeCoordinateDefinitions

/-! # Horizontal exchange factorization in product coordinates

Source: Stacks 0E47, horizontal base-change pasting
(blueprint: lem-pur-product-horizontal-exchange-factorization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.ProductExchangeCoordinates

/-- Factor the specified compactification-relative exchange through proper exchange,
sectionwise open restriction, and the canonical open base change.
Source: Stacks 0E47 and product-coordinate node Step 4
(blueprint: lem-pur-product-horizontal-exchange-factorization).

Proof: apply horizontal exchange pasting to the proper factor cf.g with successive
base maps cg.g and cg.i. The projection-preserving pullback identification identifies
the composite square with the base change by g, using cg.comm. The pasted exchange
is pullback of A0 followed by exchange across the open cg.i. Identify the latter
with sectionwise rho by the normalized restriction transpose. In the definition of
compactification-relative exchange the remaining factor is direct image of open
base change. The unit characterization of open base change identifies this factor
with beta, including its inverse-image compositor. This proves the displayed
factorization without inverting proper exchange. -/
theorem productHorizontalExchangeFactorization
    {B X Z : Scheme.{u}} {f : X ⟶ B} {g : Z ⟶ B}
    (cf : Compactification f) (cg : Compactification g)
    (A : Type u) [CommRing A] [Finite A]
    (M : ProperOpenDerived (ULift.{u + 1} A) X) :
    B0 cf cg A M =
      (ProperOpenPull (ULift.{u + 1} A) cg.i).map (A0 cf cg A M) ≫
        (rho A (pullback.snd cf.g g) (i cf cg) cg.i
          (pullback.snd cf.g cg.g) (square cf cg)).hom.app (F cf cg A M) ≫
        (ProperOpenPush (ULift.{u + 1} A) (pullback.snd cf.g g)).map
          (beta cf cg A M).hom := by sorry

end AlgebraicGeometry.ProEtale.ProductExchangeCoordinates
