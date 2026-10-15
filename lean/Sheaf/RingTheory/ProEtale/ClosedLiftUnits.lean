/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NS
-/
module

public import Sheaf.RingTheory.ProEtale.ClosedLiftMap
import Mathlib.Algebra.Category.Ring.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Etale.Basic
import WeilConjectures.RingTheory.ProEtale.ClosedLift

/-! # Units of the ind-etale closed lift

Source: blueprint, smooth purity, `sk-prop-sf-open-closed-triangle`,
`lem-exc-closed-lift-units` (blueprint: lem-exc-closed-lift-units).
-/

@[expose] public section

universe u

namespace Algebra.ClosedLift

/-- An element of the closed lift is a unit if its image in the input algebra is a unit.
Source: blueprint `lem-exc-closed-lift-units`, statement and proof
(blueprint: lem-exc-closed-lift-units).

Proof: use the small presentation indexing category of `def-exc-ind-etale-closed-lift`.
It is filtered by `lem-exc-closed-lift-filtered`. The algebra colimit is also a ring colimit:
a compatible family of ring maps has a common restriction to A, by filteredness, so the
algebra-colimit universal property applies. By `lem-pc-filtered-colimit-commrings-elementwise`,
choose a representative b in an etale finitely presented stage B mapping to the element h.
Its image in C is a unit. By `def-weil-ring-localization-away` and
`lem-weil-pbc-ring-localization-universal-property`, the map B to C extends to B[1/b],
and this extension is an A-algebra map. By
`lem-weil-pbc-etale-algebra-finite-presentation-localization`, B[1/b] is again etale and
finitely presented over A, hence another index, with transition B to B[1/b]. Cocone
compatibility identifies the image of b/1 with h. The image of 1/b is an inverse for h,
since applying the cocone ring map to both inverse identities preserves them. -/
theorem isUnit_of_isUnit_toAlgHom
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    (I : Ideal A) [Algebra (A ⧸ I) C] [IsScalarTower A (A ⧸ I) C]
    [Algebra.IndEtale (A ⧸ I) C] (h : Algebra.ClosedLift A C)
    (hh : IsUnit (toAlgHom A C h)) : IsUnit h := sorry

end Algebra.ClosedLift
