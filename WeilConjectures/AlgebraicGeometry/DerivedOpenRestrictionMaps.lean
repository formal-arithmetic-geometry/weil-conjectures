/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage

/-! # Canonical derived restriction and its adjoint maps on opens

Source: Stacks Project, Cohomology, Tag 08BV
(blueprint: def-pc-derived-open-restriction-maps).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

set_option autoImplicit false

noncomputable section

namespace AlgebraicGeometry

set_option synthInstance.maxSize 2048

/-- Exact restriction from a scheme to an open subscheme.
Source: Stacks Project, Tag 08BV (blueprint: def-pc-derived-open-restriction-maps). -/
abbrev schemeOpenRestriction (X : Scheme.{u}) (U : X.Opens) :=
  (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U))

/-- Exactness structure of canonical open restriction.
Source: Stacks Project, Tag 08BV (blueprint: def-pc-derived-open-restriction-maps). -/
instance schemeOpenRestriction_preservesFiniteLimits (X : Scheme.{u}) (U : X.Opens) :
    PreservesFiniteLimits (schemeOpenRestriction X U) :=
  comp_preservesFiniteLimits _ _

/-- Exactness structure of canonical open restriction.
Source: Stacks Project, Tag 08BV (blueprint: def-pc-derived-open-restriction-maps). -/
instance schemeOpenRestriction_preservesFiniteColimits (X : Scheme.{u}) (U : X.Opens) :
    PreservesFiniteColimits (schemeOpenRestriction X U) :=
  comp_preservesFiniteColimits _ _

/-- Additivity structure of canonical open restriction.
Source: Stacks Project, Tag 08BV (blueprint: def-pc-derived-open-restriction-maps). -/
instance schemeOpenRestriction_additive (X : Scheme.{u}) (U : X.Opens) :
    (schemeOpenRestriction X U).Additive :=
  Functor.additive_of_preserves_binary_products _

end AlgebraicGeometry
