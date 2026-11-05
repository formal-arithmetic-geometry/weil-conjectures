/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Integral.IntegralStratifiedPerfectModelsSupplement
import all WeilConjectures.AlgebraicGeometry.Perfect.PerfectChartTensorComparison
import all WeilConjectures.AlgebraicGeometry.SmoothPurity.ExtensionZeroPerfectModelTransport
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleAmbientRingedExchange

/-!
# Stratified perfect models on covering schemes

The stratified-perfect condition gives perfect constant models on the slices of a
covering sieve of each stratum. Choosing a covering family generating the sieve turns
them into perfect constant models after inverse image to the covering schemes.

Source: Bhatt--Scholze, Proposition 6.6.11 and Lemma 6.5.8
(blueprint: lem-weil-pbc-adic-unlifted-perfect-charts).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

-- `surjectiveTower_wEqualsLocallyBijective` leaves its coefficient universe free
attribute [-instance] AlgebraicGeometry.ProEtale.surjectiveTower_wEqualsLocallyBijective

end AlgebraicGeometry.Scheme
