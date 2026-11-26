/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.FiniteType

/-!
# Quasi-finiteness of a ring map at a prime

A finite-type ring map `R → S` is quasi-finite at a prime `q` if the corresponding prime of the
fibre ring is an isolated point of its spectrum.

## Implementation details

The fibre prime is supplied canonically by `PrimeSpectrum.preimageHomeomorphFiber`;
its source point lies over `p` by the definition of `p`.

## References

* [Stacks, Tag 00PL]
* [Stacks, Tag 00PK] (condition (1))
-/

@[expose] public section

universe u v

namespace Algebra

/-- For a finite-type map of commutative rings `R → S`, quasi-finiteness at a prime `q` means
that the prime of the fibre ring `κ(p) ⊗[R] S` corresponding to `q`, where `p` is the
contraction of `q`, is an isolated point of its spectrum. -/
def IsQuasiFiniteAtPrime (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] (q : PrimeSpectrum S) : Prop :=
  let p := q.comap (algebraMap R S)
  let e := PrimeSpectrum.preimageHomeomorphFiber R S p
  IsOpen ({e ⟨q, rfl⟩} : Set (PrimeSpectrum (p.asIdeal.Fiber S)))

end Algebra
