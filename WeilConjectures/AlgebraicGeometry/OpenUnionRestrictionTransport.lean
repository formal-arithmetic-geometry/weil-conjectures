/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
import WeilConjectures.AlgebraicGeometry.OpenUnionRestrictionComparisonDiagram

/-! # Transport the restriction diagram to covering opens of an open union

Source: Stacks Project, Tag 08BW, restriction to the union before applying exactness.
(blueprint: lem-sc-open-union-restriction-transport).
-/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] Functor.mapDerivedCategory schemeDerivedOpenRestrictionCompIso

-- Keep the isomorphism-component calculation abstract so it never unfolds derived restrictions.

-- The existential localization data must remain inline for the following let-bound functors.

end AlgebraicGeometry.Scheme
