/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenComparison
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenIdentificationNormalization
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarCompAssoc

/-!
# Composition and identity of proper-open comparison maps

Source: blueprint main-20261015, sec-proetale-coefficients/sk-def-sf-operations,
lem-weil-pbc-proper-open-comparison-composition, order 1842
(blueprint: lem-weil-pbc-proper-open-comparison-composition).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

-- Naturality and the right triangle turn conjugate unit equations into counit equations.

-- The canonical restriction map, expressed entirely through the derived counit.

-- Associativity of pullback and the conjugate counit equation give composition of restriction.

-- The adjunction calculation applies to any natural restriction maps with these normalizations.

end AlgebraicGeometry.Etale
