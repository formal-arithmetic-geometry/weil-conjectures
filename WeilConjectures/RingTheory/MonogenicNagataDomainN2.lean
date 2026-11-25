/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.RingTheory.NagataRing
import WeilConjectures.RingTheory.AlgebraicMonogenicNagataDomainN2
import WeilConjectures.RingTheory.NagataDomainN2
import WeilConjectures.RingTheory.PolynomialRingN2
import WeilConjectures.RingTheory.N2AscendsFiniteDomainExtension
import Mathlib.RingTheory.Algebraic.Basic

/-!
# Monogenic extensions of Nagata domains are Japanese

An injective monogenic extension `B = A[x]` of a Nagata domain `A`, with `B` a domain, is N-2.

## Implementation details

If `x` is transcendental, `B ≅ A[X]` is N-2 by Stacks 032O. Otherwise, for a finite extension
`M` of `L = Frac(B)`, the integral closure `A'` of `A` in `M` is finite, normal and Nagata, and
`T = A'[x]` is finite over `B` with fraction field `M`. Claim (***) of Stacks 0334 makes the
integral closure of `T` in `M`, which is the integral closure of `B`, finite over `T`. No nonzero
or transcendence hypothesis on `x` is required.

## References

* [Stacks, Tag 0334] (claim (*) and steps 3–4)
* [Stacks, Tags 032O, 032T]
-/

@[expose] public section

universe u

/-- An injective monogenic extension of Nagata domains is N-2. -/
theorem isN2_of_monogenic_nagata_domain (A B : Type u) [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [Algebra A B] (hA : IsNagataRing A)
    (hinj : Function.Injective (algebraMap A B)) (x : B)
    (hgen : Algebra.adjoin A ({x} : Set B) = ⊤) : IsN2 B (FractionRing B) := by
  classical
  by_cases hx : IsAlgebraic A x
  · exact isN2_of_algebraic_monogenic_nagata_domain A B hA hinj x hgen hx
  · have hi : Function.Injective (Polynomial.aeval x : Polynomial A →ₐ[A] B) :=
      transcendental_iff_injective.mp hx
    have hs : Function.Surjective (Polynomial.aeval x : Polynomial A →ₐ[A] B) := by
      rw [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval]
      exact hgen
    have hpoly : IsN2 (Polynomial A) (FractionRing (Polynomial A)) := by
      let : IsNoetherianRing A := hA.1
      exact isN2_polynomial A (isN2_of_isNagataRing_domain A hA)
    let : Algebra (Polynomial A) B := (Polynomial.aeval x).toRingHom.toAlgebra
    let : Module.Finite (Polynomial A) B :=
      Module.Finite.of_surjective (Algebra.linearMap _ _) hs
    let : IsNoetherianRing A := hA.1
    exact isN2_of_finite_domain_extension (Polynomial A) B
      (FractionRing (Polynomial A)) (FractionRing B) hi hpoly

