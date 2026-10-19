/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NU
-/
module

public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Smooth.Basic
public import WeilConjectures.FieldTheory.SeparableExtension
import Sheaf.AlgebraicGeometry.FlatSmoothFibreSmoothAtPrime
import Sheaf.AlgebraicGeometry.GenericLocallyOfFinitePresentation
import Sheaf.RingTheory.SmoothAtGenericPointOverField
import WeilConjectures.RingTheory.SingularIdeal

/-!
# Generic smoothness for a separable extension of fraction fields

Source: Stacks Project, Algebra, Lemma 10.42.2 (Tag 07ND), implication from
separable fraction fields to smoothness at the generic point (blueprint:
lem-exc-generic-smooth-domain).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Algebra

/-- If an injective finite type map of integral domains induces a separable extension
of fraction fields, a nonzero principal localization of the target is smooth over the
source. This is the affine ring formulation of generic smoothness.
Source: Stacks Project, Algebra, Lemma 10.42.2 (Tag 07ND).
(blueprint: lem-exc-generic-smooth-domain)

Proof: pass to the generic fibre `Frac(R) ⊗[R] S`, which is a finite type domain
with fraction field `Frac(S)`. The separable field case gives smoothness at its
zero prime. The flat smooth-fibre criterion transports this to smoothness at the
zero prime of `S`; unpacking the definition of smoothness at a prime yields a
nonzero element whose principal localization is smooth over `R`.
-/
theorem exists_smooth_localization_of_separable_fractionRing
    (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [IsDomain R] [IsDomain S] [Algebra R S] [Algebra.FiniteType R S]
    (hinj : Function.Injective (algebraMap R S))
    (hsep : @IsSeparableExtension (FractionRing R) (FractionRing S) _ _
      (IsFractionRing.map (K := FractionRing R) (L := FractionRing S) hinj).toAlgebra) :
    ∃ g : S, g ≠ 0 ∧ Algebra.Smooth R (Localization.Away g) := by
  sorry

end Algebra
