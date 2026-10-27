/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K8
-/
module

public import Sheaf.Paper.FiniteFreeProjectionExchangeDefinitions

/-! Scalar compatibility for the specified finite-coefficient operations. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.Functor
open WeilConjectures.FiniteFreeCoefficients
namespace WeilConjectures.FiniteFreeProjectionExchange

/-- Scalar extension commutes with the proper and open exchange constituents.
Source: Stacks 0E47, 03S6 and 0GL6; blueprint main-20261015,
sk-thm-purity-transport proof Steps 1 and 3
(blueprint: lem-pur-scalar-exchange-constituents).

Proof: compute the scalar/inverse-image comparison on flat representatives. The
Cartesian inverse-image comparison and the scalar comparison both send a tensor
section to its inverse image with the same coefficient, so their cube commutes.
The direct-image comparison is the geometric adjunction mate of the scalar comparison.
Take mates of this cube, using the defining direct-image counit equation and the
triangle identities. Its two resulting faces are precisely ProperExchangeEquation;
this does not require the geometric map to be proper or either exchange to be invertible.
For open exchange take the adjunct under the pulled-back extension-by-zero adjunction.
The two transposes are the pulled-back open unit followed by the same scalar balancing
map. The unit normalization of scalarOpen identifies them. On the pro-etale site
insert the published exact/left-derived inverse-image identifications on both sides;
their naturality cancels the extra identifications in openExchange. -/
theorem scalar_exchange_constituents {A B : Type (u + 1)}
    [CommRing A] [CommRing B] [Finite A] [Finite B] (φ : A →+* B) :
    ∀ (pro : Bool) {X' X Y' Y : Scheme.{u}}
      {a : X' ⟶ X} {b : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}
      (sq : IsPullback a b f g) (M : Sites.D pro A X),
      ProperExchangeEquation pro φ sq M ∧
      (∀ [IsOpenImmersion f] [IsOpenImmersion b],
        OpenExchangeEquation pro φ sq M) := by
  sorry

end WeilConjectures.FiniteFreeProjectionExchange
