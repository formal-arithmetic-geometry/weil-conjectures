/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q97
-/
module

public import Sheaf.RingTheory.HenselizationAtPrime

/-!
# Universe-polymorphic ordinary henselization predicate

Source: Stacks Project, Algebra, Tags 04GN and 04GQ
(blueprint: def-weil-pbc-henselization-at-prime).

This is the universe-generalized interface. The recorded declaration fixes the
source and target ring universes, which is unusable when the two rings occur
in a tensor product with independently-sized factors.
-/

@[expose] public section
set_option autoImplicit false

universe u v

namespace Algebra

/-- Universe-polymorphic form of the ordinary henselization universal property.
Test rings live in the common universe of the base and the henselization.
Source: Stacks Project, Algebra, Tags 04GN and 04GQ
(blueprint: def-weil-pbc-henselization-at-prime).
-/
def IsHenselizationAtPrime' (A : Type u) [CommRing A] (p : Ideal A) (H : Type v)
    [p.IsPrime] [CommRing H]
    [Algebra (Localization.AtPrime p) H] [HenselianLocalRing H] : Prop :=
  IsLocalHom (algebraMap (Localization.AtPrime p) H) ∧
    ∀ (T : Type (max u v)) [CommRing T] [HenselianLocalRing T]
      (g : Localization.AtPrime p →+* T),
      IsLocalHom g →
      ∃! h : H →+* T,
        IsLocalHom h ∧ h.comp (algebraMap (Localization.AtPrime p) H) = g

end Algebra
