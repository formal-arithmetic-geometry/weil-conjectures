/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.RingTheory.N2AscendsFiniteDomainExtension

/-!
# A Nagata domain is Japanese

A Nagata domain is N-2 (Japanese).

## Implementation details

The Nagata hypothesis applied to the zero prime makes `S/(0)` N-2, and N-2 ascends along the
isomorphism `S/(0) ≃ S`, viewed as a finite extension of domains (Stacks 032I).

## References

* [Stacks, Tag 032R]
* [Stacks, Tag 0334] ((2) implies (3))
* [Stacks, Tag 032I]
-/

@[expose] public section

universe u

/-- A Nagata domain is N-2. -/
theorem isN2_of_isNagataRing_domain (S : Type u) [CommRing S] [IsDomain S]
    (hS : IsNagataRing S) : IsN2 S (FractionRing S) := by
  let e := RingEquiv.quotientBot S
  let : Algebra (S ⧸ (⊥ : Ideal S)) S := e.toRingHom.toAlgebra
  let : Module.Finite (S ⧸ (⊥ : Ideal S)) S :=
    Module.Finite.of_surjective (Algebra.linearMap _ _) e.surjective
  let : IsNoetherianRing S := hS.1
  let : IsNoetherianRing (S ⧸ (⊥ : Ideal S)) :=
    isNoetherianRing_of_ringEquiv S e.symm
  exact isN2_of_finite_domain_extension (S ⧸ (⊥ : Ideal S)) S
    (FractionRing (S ⧸ (⊥ : Ideal S))) (FractionRing S) e.injective (hS.2 ⊥)

