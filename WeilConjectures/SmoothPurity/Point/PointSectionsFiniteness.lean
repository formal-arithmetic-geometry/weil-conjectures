/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.SixFunctors.PointProEtaleSectionsExact
public import WeilConjectures.AlgebraicGeometry.Intrinsic.IntrinsicFiniteTorsionConstructibility
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFiniteCohomologyComplexes
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFgCompleteComplexes
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdComplexes
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Field.ULift
import WeilConjectures.SmoothPurity.Point.PointSectionsFinitenessFiniteTorsion
import WeilConjectures.SmoothPurity.Point.PointSectionsFinitenessIntegral

/-!
# Finiteness of sections over the algebraically closed coefficient point

Source: Weil blueprint, `def-weil-finite-coefficient-point`, order 1509,
its finite, integral and rational evaluation assertions
(blueprint: lem-weil-point-sections-finiteness).

All assertions are made for every complex representative of the derived object.
Sections are evaluated at the final small pro-etale object. The scalar maps are
actual constant-section maps, and rationalization is termwise scalar extension.
The section-exactness dependency makes these formulas independent of the representative.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale

namespace WeilConjectures

end WeilConjectures
