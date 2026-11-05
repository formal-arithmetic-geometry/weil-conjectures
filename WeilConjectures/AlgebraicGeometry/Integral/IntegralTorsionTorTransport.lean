/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
import all WeilConjectures.AlgebraicGeometry.Perfect.PerfectChartTensorComparison

/-!
# Inverse image of the consecutive-quotient Tor sheaf

The consecutive-quotient Tor sheaf of the degree-`q` cohomology of a reduction commutes
with inverse image: its inverse image only depends on the inverse image of the complex.

Source: Stacks Tags 0D6D and 06YY
(blueprint: lem-weil-pbc-integral-cohomology-torsion-normal-form).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

variable {A : Type (u + 1)} [CommRing A] (d : AdicCoefficientDatum A)
  {T S : Scheme.{u}} (g : S ⟶ T) (q : ℤ) (n : ℕ)

end AlgebraicGeometry.Scheme
