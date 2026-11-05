/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFgCompleteComplexes
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdComplexes
import WeilConjectures.SmoothPurity.Point.PointSectionsIntegralCohomologyControl
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.FlatScalarExtensionFiniteCohomology
import WeilConjectures.Algebra.Homology.Derived.DerivedCompleteModuleFinite
import WeilConjectures.CategoryTheory.DerivedCategory.SmoothPurity.DerivedCompleteHomology
import WeilConjectures.NumberTheory.Padics.AdicLimitFiniteModulesSupplement
import WeilConjectures.NumberTheory.Padics.IntegersLocalizationUniformizer
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.AdicCompletion.Topology
import Mathlib.RingTheory.Noetherian.Basic

/-! Source: Weil blueprint, `def-weil-finite-coefficient-point`, order 1509
(blueprint: lem-weil-point-sections-integral-finiteness). -/
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
  AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

end WeilConjectures
