/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.RingTheory.EtalePolynomialCertificate
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Polynomial witnesses for an inverse conormal differential

Source: Stacks Project, Algebra, proof of Tag 07RI, inverse differential calculation.
(blueprint: lem-weil-pbc-conormal-polynomial-inverse).
-/

@[expose] public section

universe u

namespace Algebra

/-- A differential on a finitely generated relation ideal is bijective precisely when
its two inverse identities have finite polynomial witnesses.

Source: Stacks Project, Algebra, proof of Tag 07RI, lines 47654-47662.
(blueprint: lem-weil-pbc-conormal-polynomial-inverse).

Proof: write J = ker α = (f_j). If d is bijective, lift each inverse image of the
coordinate vector e_k to an element g_k of J. Express g_k = sum_j c_jk f_j using
finite ideal generation. The equality d([g_k]) = e_k says exactly that the first
certificate expressions lie in J. Applying injectivity of d to the relation
classes gives [sum_k (∂_k f_j)g_k] = [f_j]. Equality in J/J² is precisely the
second certificate membership.
Conversely, given c, put g_k = sum_j c_jk f_j and define the S-linear map
h(v) = sum_k v_k [g_k]. The first certificate gives d(h(e_k)) = e_k, hence
d composed with h is the identity on the free module. The second gives
h(d([f_j])) = [f_j]. The classes [f_j] generate J/J² over S, since α is
surjective and f_j generate J. Thus h composed with d is also the identity.
The two identities imply bijectivity. No independence of the relations is
assumed. If n or m is zero the corresponding generator check is empty;
if S is the zero ring both modules vanish and the same argument applies. -/
theorem conormal_bijective_iff_polynomialCertificate
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    {n m : ℕ} (α : MvPolynomial (Fin n) R →ₐ[R] S)
    (hα : Function.Surjective α) (f : Fin m → MvPolynomial (Fin n) R)
    (hker : RingHom.ker α.toRingHom = Ideal.span (Set.range f)) :
    let J := RingHom.ker α.toRingHom
    let e := RingHom.quotientKerEquivOfSurjective hα
    letI : Module S J.Cotangent := Module.compHom J.Cotangent e.symm.toRingHom
    ∀ (d : J.Cotangent →ₗ[S] (Fin n → S)),
      (∀ (g : J) (i : Fin n),
        d (Ideal.toCotangent J g) i = α (MvPolynomial.pderiv i g.1)) →
      (Function.Bijective d ↔ EtalePolynomialCertificate f) := by
  sorry

end Algebra
