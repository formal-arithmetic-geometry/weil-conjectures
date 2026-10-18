/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.RingTheory.FiniteType
public import Mathlib.Topology.NoetherianSpace

import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Finite type algebras preserve Noetherian spectra

Source: J. Ohm and R. L. Pendleton, *Rings with Noetherian spectrum*,
Theorem 2.5 and Corollary 2.6 (the paper is not in the local collection).
The proof below is the independent agent proof recorded in the DAG, serving paragraph (2) of
`det-lem-coefficient-heart-closure` in the main-20261015 blueprint
(blueprint: lem-sfb-finite-type-noetherian-spectrum).
-/

@[expose] public section

universe u v

open TopologicalSpace

namespace AlgebraicGeometry

/-- A finite type algebra over a ring with Noetherian spectrum has Noetherian spectrum.

Source: J. Ohm and R. L. Pendleton, *Rings with Noetherian spectrum*, Theorem 2.5 and
Corollary 2.6 (original paper unavailable locally). The following is the independent agent
proof recorded in the DAG for paragraph (2) of `det-lem-coefficient-heart-closure`.

1. Work with descending chains of closed sets, equivalently ascending chains of opens.
   Closed subspaces of Noetherian spaces are Noetherian. A union of two Noetherian subspaces
   is Noetherian: restrict a descending closed chain to both pieces and take the larger
   stabilization index. Noetherian induction on closed sets is valid, since a nonempty
   family with no minimal member would produce a strictly descending closed chain.
2. First handle one variable. Set X = Spec R, Y = Spec R[T], with the continuous contraction
   map pi : Y → X. Continuity follows from pi⁻¹(V(J)) = V(JR[T]). Induct on closed subsets
   Z of X with claim P(Z): pi⁻¹(Z) is Noetherian. The empty case is immediate. If Z is
   reducible, write it as the union of two proper closed subsets; induction and step 1
   apply. It remains to treat nonempty irreducible Z.
3. Write Z = V(J). By `lem-weil-pbc-spec-quotient-homeomorphism-zero-locus`, Spec(R/J)
   is homeomorphic to Z. By `lem-weil-pbc-spec-irreducible-components-minimal-primes`, its
   irreducible whole space is V(q) for a minimal prime q. Pulling q back gives a prime p
   of R with Z = V(p). Thus C = R/p is a domain. The coefficientwise surjection R[T] → C[T]
   has kernel pR[T]: coefficients in p give precisely finite sums of constants in p times
   powers of T. The quotient-spectrum result identifies pi⁻¹(Z) with Spec C[T], compatibly
   with contraction to Z = Spec C.
4. For a nonzero ideal I of C[T], choose nonzero f in I of least degree n and leading
   coefficient a ≠ 0. In C_a, the localization of `def-weil-ring-localization-away`,
   h = a⁻¹f is monic of degree n. By `lem-weil-pbc-monic-quotient-free`, division modulo h
   expresses each g in I as qh + r, with r zero or of degree less than n. Choose N ≥ 1
   large enough to clear the finitely many denominators in a^N r and a^(N-1) q. Then
   a^N r = a^N g - (a^(N-1) q) f lies in I in C[T]. Localization is injective because C is
   a domain and a ≠ 0. If r were nonzero, a^N r would contradict the minimal degree of f.
   Hence r = 0 and I C_a[T] = (h). If n = 0 the quotient basis is empty and r is zero.
5. Given a descending closed chain F_i in Spec C[T], let I_i be the intersection of its
   primes (the whole ring for the empty set). Then I_i is increasing and V(I_i) = F_i:
   writing F_i = V(K_i) gives K_i ⊆ I_i, and each prime in F_i contains I_i. Their union
   I is an ideal. If I = 0 all F_i agree. Otherwise choose f, a, h as in step 4, and i₀
   with f in I_i₀. For i ≥ i₀, (h) ⊆ I_i C_a[T] ⊆ I C_a[T] = (h). Coefficientwise
   localization identifies (C[T])_a with C_a[T], since finitely many coefficients have a
   common denominator and equality is coefficientwise. By clause (ii) of
   `lem-weil-pbc-spec-localization-away-basic-open`, its spectrum is D(a). Containment of
   I_i in a contracted prime is equivalent to containment of its extension in that prime.
   Thus all F_i ∩ D(a) agree for i ≥ i₀.
6. The zero prime of C does not contain a, so V(a) is a proper closed subset of Spec C.
   Its image Z' in Z is proper closed, hence closed in X. Induction P(Z') says its inverse
   image is Noetherian; under step 3 this is V(a) in Spec C[T], by contraction of primes.
   The restrictions F_i ∩ V(a) therefore stabilize. Combining this with step 5 and
   D(a) ∪ V(a) = Spec C[T] proves stabilization of F_i. This proves P(Z) in the irreducible
   case, completing the induction and proving the one-variable assertion.
7. Induct on the finite number d of generators to obtain Noetherianity of the spectrum of
   R[x₁, …, x_d], with d = 0 the given hypothesis. Finite type gives a surjection from
   this polynomial ring to B. By `lem-weil-pbc-spec-quotient-homeomorphism-zero-locus`,
   Spec B is homeomorphic to the closed zero locus of the kernel, so is Noetherian by
   step 1. For B = 0 this is empty; if R = 0, unitality forces B = 0.
(blueprint: lem-sfb-finite-type-noetherian-spectrum) -/
theorem noetherianSpace_primeSpectrum_of_finiteType
    (R : Type u) (B : Type v) [CommRing R] [CommRing B]
    (f : R →+* B) [NoetherianSpace (PrimeSpectrum R)]
    (hf : f.FiniteType) : NoetherianSpace (PrimeSpectrum B) := by
  sorry

end AlgebraicGeometry
