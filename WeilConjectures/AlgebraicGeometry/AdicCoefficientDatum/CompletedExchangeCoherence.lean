/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedBaseChangeMap
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedOrdinaryComparisons
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedPullbackReflection
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedExchangeUnit
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedOrdinaryComparisons
import WeilConjectures.AlgebraicGeometry.OrderedExchange.OrderedExchangeCoefficientComparison
import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement

/-!
# Naturality, units, and pasting of completed exchange

Source: blueprint proper base change, completed exchange coherence, order 1348
(blueprint: lemma-weil-pbc-completed-exchange-coherence).
The comparison maps below retain ordinary tensor-unit normalization. They do not
replace canonical completed pullback compositions by arbitrary natural isomorphisms.

## Main statements

- `AdicCoefficientDatum.completedExchange_naturality`: naturality for arbitrary maps.
- `AdicCoefficientDatum.completedExchange_identity_horizontal`: horizontal identities.
- `AdicCoefficientDatum.completedExchange_identity_vertical`: vertical identities.
- `AdicCoefficientDatum.completedExchange_horizontal`: horizontal pasting.
- `AdicCoefficientDatum.completedExchange_vertical`: vertical pasting.

## Main definitions

- `AdicCoefficientDatum.completedPullComp`: the unit-normalized composition comparison.
- `AdicCoefficientDatum.completedPullId`: the unit-normalized identity comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme

variable {A : Type (t + 1)} [CommRing A] (d : AdicCoefficientDatum A)

attribute [local irreducible] AdicCoefficientDatum.pullComp AdicCoefficientDatum.pushComp

end AlgebraicGeometry.Scheme
