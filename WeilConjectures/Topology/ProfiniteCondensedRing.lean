/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientCommRing

/-!
# Arbitrary condensed rings in the profinite-site universe convention

A condensed ring is a ring object of abelian sheaves on the coherent profinite site.

## Implementation details

The existing continuous-function, adic and subfield constructions are publicly reexported. The
abbreviation also admits condensed rings not presented by a topological ring.

## References

* Hemo, Richarz, Scholbach, *Constructible sheaves on schemes*, Section 3.
-/

@[expose] public section

universe u

open CategoryTheory

namespace Profinite

/-- A condensed ring is a ring object of abelian sheaves on the coherent profinite site,
equivalently a sheaf of rings. Multiplication is tensor multiplication, with integer unit. -/
abbrev CondensedRing : Type (u + 2) := Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})

end Profinite
