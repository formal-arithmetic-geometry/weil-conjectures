/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek

/-!
# Legacy compactification upper-shriek imports

The unused `AlgebraicGeometry.Etale.CompactificationUpperShriek` API has been retired.
The active exceptional inverse image and its adjunction are provided by
`WeilConjectures.SixFunctors.Etale.Derived.UpperShriek`: existence is an explicit hypothesis
for general coefficients and is proved for finite module coefficients in
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`.

The two public imports are retained for compatibility with importers of this module.
No unconditional proper-pushforward adjoint or arbitrary-coefficient coproduct assertion
is exported here.
-/
