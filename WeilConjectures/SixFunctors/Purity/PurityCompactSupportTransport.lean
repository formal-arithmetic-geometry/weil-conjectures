/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityFiniteSetting
public import WeilConjectures.SixFunctors.Finite.FiniteTorAmplitude
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenSquareExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantOpenSquareExchange
public import WeilConjectures.SmoothPurity.PurityFiniteSetting.SchemeGeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.ProEtale.Direct.ProEtaleDirectImageGlobalEvaluation
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Condensed.CondensedAmbientExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Derived.ProEtaleDerivedExtensionZeroBaseChange
public import WeilConjectures.AlgebraicGeometry.Completed.CompletedCompactSupportExchange
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingPullbackComparison
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite

/-! # Compact-support transport of strict Weil data

Source: current blueprint, sec-six-functors/sk-thm-sf-package,
`def-pur-compact-support-transport` (blueprint: def-pur-compact-support-transport).

The finite construction uses the ambient ringed mate and canonical open base change.
The integral construction uses the specified completed exchange. At higher stages the
same ordered composite uses the supplied domains and comparisons of def-exchange-projection.
The scheme-Frobenius form precomposes the datum with kappa, including for Rf_! M.
No preservation or invertibility assertion is included.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u uX uB uY uB' vX vB vY vB' uC vC uD vD

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Functor

namespace WeilConjectures.Purity

/-- Finiteness of the conventions' coefficient ring A = O_E/(varpi^n), supplied by its
published quotient construction; the global evaluation now takes an arbitrary finite ring.
Source: blueprint def-pur-conventions (blueprint: def-pur-compact-support-transport). -/
instance compactSupportTransport_finiteRing (P : PurityFiniteSetting.{u}) :
    Finite P.Ring :=
  Padic.finite_coefficientExtensionRing P.coefficients.l P.extension P.level P.level_pos

section SuppliedStage

variable {DX : Type uX} {DB : Type uB} {DY : Type uY} {DB' : Type uB'}
  [Category.{vX} DX] [Category.{vB} DB] [Category.{vY} DY] [Category.{vB'} DB']

end SuppliedStage

end WeilConjectures.Purity
