/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.TorsorAssociatedModule

/-!
# The associated module sheaf with general commutative coefficients

Source: Stacks Project, Tags 0DV5 (3), 0DV6, 04TR and 04TS.
The existing prime-coefficient construction stays unchanged. This variant uses the
same equivariant locally constant formulas directly over the specified coefficient ring.
(blueprint: def-weil-pbc-finite-ring-torsor-associated-module)
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u r
open CategoryTheory Limits Opposite
namespace AlgebraicGeometry.Scheme.GaloisCover

variable {V : Scheme.{u}} {P : Type u} [Group P] [Finite P]
  (c : Scheme.GaloisCover (ULift.{u + 1} P) V)

section GenericRing

variable (R : Type r) [CommRing R]

end GenericRing

section LargeRing

variable (R : Type (u + 1)) [CommRing R]

end LargeRing

end AlgebraicGeometry.Scheme.GaloisCover
