/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.PurIntegralTower.PurStrictIntegralExchangeData
import all WeilConjectures.AlgebraicGeometry.Strict.Tower.StrictTowerExchangeMateNormalization
import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum.CompletedExchangeUnit
import WeilConjectures.AlgebraicGeometry.Pur.PurIntegralGeometricInputNormalization
import WeilConjectures.AlgebraicGeometry.Pur.PurIntegralStrictCalculus
import WeilConjectures.AlgebraicGeometry.Pur.PurIntegralStrictReduction
import WeilConjectures.AlgebraicGeometry.Pur.PurIntegralCompletedCoherence
import WeilConjectures.AlgebraicGeometry.Pur.PurIntegralTotalUnitEquation

/-! # Strict integral exchange normalization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
attribute [local irreducible] cbcDerivedOpenShriek cbcDatumCompletedExchange
  cbcDatumOrdinaryExchange cbcBeta
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

attribute [local irreducible] pbcIntegralDatum
attribute [local irreducible] PurIntegralStrictMapNormalization PurIntegralStrictHorizontal
  PurIntegralStrictVertical PurIntegralStrictReduction PurIntegralCompletedCoherence
  PurIntegralSupportNormalization

end AlgebraicGeometry.Scheme
