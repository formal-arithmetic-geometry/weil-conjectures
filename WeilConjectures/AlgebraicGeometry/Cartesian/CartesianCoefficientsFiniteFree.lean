/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.NumberTheory.Padics.IntegersFinite
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMapCondensedRingSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars
public import Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.RingTheory.Localization.Module
import WeilConjectures.CategoryTheory.ProEtaleCoefficients.MonoidalFiniteFreeTransport
import all WeilConjectures.CategoryTheory.ModuleObjects.ProEtaleCoefficients.FiniteFreeScalarCoordinates
import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits
import all WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedSubfieldBasis
import WeilConjectures.NumberTheory.Padics.IntegersAlgebra
import Mathlib.RingTheory.Valuation.LocalSubring

/-!
# Finite free integral and rational pro-etale coefficients

Source: blueprint main-20261015, sec-proetale-coefficients,
sk-prop-sfb-cartesian-coefficients-finite-free.md
(blueprint: det-prop-sfb-cartesian-coefficients-finite-free).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

variable (ℓ : ℕ) [Fact ℓ.Prime]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] upperStarFromPoint Mod.extendScalars

end AlgebraicGeometry.ProEtale
