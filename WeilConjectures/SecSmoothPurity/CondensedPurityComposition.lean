/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SecSmoothPurity.Transport
public import WeilConjectures.SecSmoothPurity.SpecifiedAdjunctionFamily

/-! # Native all-coefficient purity composition

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-prop-sp-composition/
_section.md (blueprint: prop-pur-condensed-purity-composition).

The coefficient cases are supplied separately so the family cannot be an
arbitrary function.  The finite case is the diagonal/DNC normalized
finite-ring adjunction, the integral case is the realized tower adjunction,
and the rational and closure cases are the scalar-localized and
finite-subextension adjunctions.  Their names and source declarations are
recorded in the family fields below.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.PurityTransport

/-- The specified native coefficient family has counit-compatible composition.

Proof steps from the source: (1) compose smooth dimensions and the canonical
compact-support compositor; (2) transpose twice and reduce to counit equation
(T); (3) use finite diagonal/DNC tensor transitivity; (4) normalize at
`Z/ell^n`; (5) extend to every finite ring by actual scalar extension;
(6) substitute the unit equation for every finite object; (7) realize the
whole integral tower and identify its counits by right-adjoint uniqueness;
(8) localize an integral model to finite coefficient fields; (9) descend to
one finite subextension of the algebraic closure and use its cocycle.
All nine steps use the coefficientwise fields of `N`; no arbitrary family is
admitted.  The finite, integral, rational, closure, dimension-zero, and empty
scheme cases are all retained. -/
theorem condensed_purity_composition
    (ell : ℕ) [Fact ell.Prime]
    (D : WeilConjectures.FiniteFieldDatum.{u}) (hEll : ell ≠ D.p) :
    ∃ N : NativeSpecifiedAdjunctionFamily ell D,
      BrownComparison ell D N.family ∧
      ScalarCompatible ell D N.family ∧
      BaseChangeCompatible ell D N.family ∧
      CompositionCompatible ell D hEll N.family ∧
      AffineNormalized ell D N.family := by
  sorry

end AlgebraicGeometry.ProEtale.PurityTransport
