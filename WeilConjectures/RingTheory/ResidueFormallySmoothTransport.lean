/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import WeilConjectures.RingTheory.FormallySmoothAdic
import WeilConjectures.RingTheory.FormallySmoothAdicRingEquiv

/-!
# Transport of adic formal smoothness along residue field isomorphisms

If a local homomorphism `A₀ → A` induces an isomorphism of residue fields, then adic formal
smoothness of an algebra over the residue field of `A` implies adic formal smoothness over the
residue field of `A₀`.

## Implementation details

The algebra structure over the residue field of `A₀` is the one explicitly induced by the
residue map, rather than an unspecified existential algebra structure.

## References

* [Stacks, Tag 07NS]
-/

@[expose] public section

universe u v w

namespace RingHom

/-- Adic formal smoothness over the residue field of `A` restricts to adic formal smoothness over
the residue field of `A₀`, along a local homomorphism `A₀ → A` inducing a bijection of residue
fields, with the algebra structure induced by that map. -/
theorem residue_formallySmooth_transport
    {A₀ : Type u} {A : Type v} {E : Type w}
    [CommRing A₀] [CommRing A] [CommRing E]
    [IsLocalRing A₀] [IsLocalRing A]
    [Algebra (IsLocalRing.ResidueField A) E]
    (n : Ideal E) (α : A₀ →+* A) [IsLocalHom α]
    (hres : Function.Bijective (IsLocalRing.ResidueField.map α))
    (hfs : Algebra.FormallySmoothAdic (IsLocalRing.ResidueField A) E n) :
    letI : Algebra (IsLocalRing.ResidueField A₀) E :=
      ((algebraMap (IsLocalRing.ResidueField A) E).comp
        (IsLocalRing.ResidueField.map α)).toAlgebra
    Algebra.FormallySmoothAdic (IsLocalRing.ResidueField A₀) E n := by
  let e : IsLocalRing.ResidueField A₀ ≃+* IsLocalRing.ResidueField A :=
    RingEquiv.ofBijective (IsLocalRing.ResidueField.map α) hres
  exact Algebra.FormallySmoothAdic.of_ringEquiv e n hfs

end RingHom
