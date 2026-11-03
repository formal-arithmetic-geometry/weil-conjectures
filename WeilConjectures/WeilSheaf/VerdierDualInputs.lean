/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.SmoothPurity
public import WeilConjectures.WeilSheaf.VerdierExchange

/-!
# Inputs of the duality theory of Weil complexes

This file collects the results from the chapters on the six operations and on smooth purity
that `WeilConjectures.WeilSheaf.VerdierDual` uses:

- `AlgebraicGeometry.WeilComplex.nonempty_iso_derivedLowerStar_of_adjunction`: the Verdier
  exchange `RHom(Rf₀! M, ω_Y) ≅ Rf_* RHom(M, ω_X)` (`fix-cor-verdier-exchange`);
- `AlgebraicGeometry.WeilComplex.nonempty_rightAdjoint_obj_adicConstant_iso_of_smooth`: the
  dualizing complex of a smooth scheme (`cor-pur-adic-and-rational-smooth-dualizing-complexes`).
-/
