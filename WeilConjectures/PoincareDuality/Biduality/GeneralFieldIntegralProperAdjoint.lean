/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ProfiniteCondensedRing
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import
  WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.CategoryTheory.Adjunction.Basic


/-! # The precise proper integral adjoint obligation for general-field consumers

Source: current blueprint, `sk-thm-existence`,
`lem-sfb-dc-proper-pushforward-left-adjoint-oe.md` and its proof companion;
the proof order follows Wei Yang #1412. Houyi DM #1449 requires general-field
consumers to use the exact named obligation, rather than an arbitrary-field instance.
(blueprint: lem-sfb-dc-proper-pushforward-left-adjoint-oe-general-field)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Scheme
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj

end AlgebraicGeometry.ProEtale.CondensedRing.PadicIntegersRingObj
