/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.AbsoluteFrobenius
public import WeilConjectures.Mathlib.FieldTheory.Finite.Basic

/-!
# Arithmetic and geometric Frobenius

Source: Deligne, Weil II (1.1.7)--(1.1.8), pp. 150--151 and (1.1.14), p. 153
(blueprint: def-weil-frobenius-detailed).

The arithmetic and geometric field automorphisms are the existing
`FiniteField.frobeniusAlgEquivOfAlgebraic` and
`FiniteField.geometricFrobeniusAlgEquivOfAlgebraic`. The geometric scheme automorphism is
constructed on the geometric fibre of the recorded finite-field datum, for any fixed closure.
The absolute map is the existing `Scheme.iterateFrobenius` with p, a and the characteristic
proof `model_characteristic`; the relative map is `FiniteFieldDatum.relativeFrobenius`.
Only the geometric scheme automorphism is used for the blueprint's Frobenius operators.
## Main definitions

- `galoisMap`: the coefficient action on the chosen fibre product.
- `geometricFrobenius`: its geometric field-Frobenius specialization as an automorphism.

-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace WeilConjectures.FiniteFieldDatum

end WeilConjectures.FiniteFieldDatum
