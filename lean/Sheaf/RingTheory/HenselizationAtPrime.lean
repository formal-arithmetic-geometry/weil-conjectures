/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q132
-/
module

public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.Mathlib.RingTheory.Henselian

/-!
# Ordinary henselization at a prime

Source: Stacks Project, Algebra, Tags 04GN and 04GQ
(blueprint: def-weil-pbc-henselization-at-prime).
-/

@[expose] public section

universe u

namespace Algebra

/-- The local henselian ring `H` is a henselization of `A` at the prime `p` when its
structural map from `Aₚ` is local and has the universal property for local maps from
`Aₚ` to henselian local rings. Source: Stacks Project, Algebra, Tags 04GN and 04GQ
(blueprint: def-weil-pbc-henselization-at-prime). -/
def IsHenselizationAtPrime (A : Type u) [CommRing A] (p : Ideal A) (H : Type u)
    [p.IsPrime] [CommRing H]
    [Algebra (Localization.AtPrime p) H] [HenselianLocalRing H] : Prop :=
  IsLocalHom (algebraMap (Localization.AtPrime p) H) ∧
    ∀ (T : Type u) [CommRing T] [HenselianLocalRing T]
      (g : Localization.AtPrime p →+* T),
      IsLocalHom g →
      ∃! h : H →+* T,
        IsLocalHom h ∧ h.comp (algebraMap (Localization.AtPrime p) H) = g

end Algebra
