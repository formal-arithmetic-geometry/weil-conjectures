/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CondensedOpenProperPasting

/-!
# The condensed open/proper definition package

Source: `literature/blueprint/latest/blueprint/sec-smooth-purity/`
`sk-prop-sp-purity-bc/det-prop-sf-cbc.md`
(blueprint: def-fd-condensed-open-proper-calculus).

This module records the existing definitions used together by the compact-support statement:
the total pullback `P`, derived direct image `R` and open extension `J` on the full derived
module categories `D`; the compositors and identity comparisons `pComp`, `pId`, `rComp`, `rId`,
`jComp` and `jCongr`; the normalized open units `OpenUnits`; the open restriction
`restriction` (Lambda_Q), the total inverse `comparisonInverse`, and the forward comparison
`gamma` (Gamma_Q), the open-adjunction transpose of the inverse of Lambda_Q. All are defined in
`WeilConjectures.AlgebraicGeometry.CondensedOpenProperPasting`; none is duplicated here.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
open AlgebraicGeometry

namespace AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The carrier of the canonical condensed open/proper definition package is the existing
full derived module category `D`; the accompanying definitions are the existing `P`, `R`, `J`,
`pComp`, `pId`, `rComp`, `rId`, `jComp`, `jCongr`, `OpenUnits`, `restriction`,
`comparisonInverse`, and `gamma` declarations in this namespace.
Source: `det-prop-sf-cbc` (blueprint: def-fd-condensed-open-proper-calculus). -/
abbrev condensedOpenProperDefinitions (X : Scheme.{u}) := D Λ X

end AlgebraicGeometry.ProEtale.CondensedRing.CondensedOpenProper
