/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.DualityConjugate
public import WeilConjectures.WeilSheaf.VerdierExchangeNatural

/-!
# Inputs for the exceptional inverse image of Weil complexes

This file collects the inputs of `WeilConjectures.WeilSheaf.VerdierDual` on the exceptional
inverse image `Rf^!` of Weil complexes:

- `CategoryTheory.Adjunction.nonempty_iso_rightOp_comp_op_comp_of_duality`: conjugating an
  adjunction by dualities, which gives `Rf^! ≅ 𝔻_X f^* 𝔻_Y`;
- `AlgebraicGeometry.WeilComplex.nonempty_verdierDual_derivedLowerShriek_natIso`: the Verdier
  exchange `𝔻_Y Rf₀! ≅ Rf_* 𝔻_X`, natural in its argument.
-/
