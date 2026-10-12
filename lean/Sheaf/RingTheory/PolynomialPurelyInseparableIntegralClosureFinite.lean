/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F2
-/
module

public import Sheaf.RingTheory.JapaneseDomain
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Purely inseparable integral closures over polynomial rings

Source: Stacks Project, Algebra, Lemma 10.161.13 (Tag 032O), positive-characteristic
part of the second assertion.
(blueprint: lem-weil-pbc-polynomial-purely-inseparable-closure-finite).
-/

@[expose] public section

universe u

set_option autoImplicit false

/-- For a Noetherian normal Japanese domain, the integral closure of its polynomial
ring in a finite purely inseparable extension of its fraction field is finite.
Source: Stacks Project, Algebra, Lemma 10.161.13 (Tag 032O), proof of the second assertion.
(blueprint: lem-weil-pbc-polynomial-purely-inseparable-closure-finite).

Proof: Write K = Frac(R) and x for the polynomial variable. Clearing coefficient
denominators identifies Frac(R[x]) with K(x): multiply a polynomial in K[x] by the
product of denominators of its finitely many coefficients to put it in R[x]. The
inclusion K → K(x) makes K have characteristic p as well. In an algebraic closure of
L choose a common q = p^e such that the q-th powers of a K(x)-basis of L lie in K(x).
Write those powers as quotients of polynomials. Adjoin to K the q-th roots of all
coefficients in these finitely many numerators and denominators, obtaining K'. The
monomials in these roots with exponents below q span K' over K: the corresponding
finite-dimensional subalgebra is a domain and thus a field: multiplication by a nonzero
element is an injective endomorphism of a finite-dimensional K-vector space, hence
surjective and takes some element to 1. Choose t with t^q = x.
The injectivity of the iterated Frobenius shows that every basis element lies in K'(t),
so L embeds in K'(t) over K(x). This last extension is finite by the tower law.
Let A be the integral closure of R in K'. It is finite over R by the Japanese hypothesis,
and is normal with fraction field K'. The element t is transcendental over K', since
otherwise x would be algebraic over K. Hence A[t] is a normal polynomial ring with
fraction field K'(t). The elements of A and t are integral over R[x], so A[t] is contained
in the integral closure C of R[x] in K'(t). Conversely each element of C is integral over
A[t], and normality forces it into A[t]. Thus C = A[t]. If a_j generate A over R, then
a_j t^r, for 0 ≤ r < q, generate C over R[x], by writing each exponent as qs+r and using
t^q = x. Finally the integral closure in L embeds as an R[x]-submodule of C; R[x] is
Noetherian, so that submodule is finite. This includes q = 1 and the trivial extension. -/
theorem finite_polynomial_purelyInseparable_integralClosure
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (hR : IsN2 R (FractionRing R)) (p : ℕ) [Fact p.Prime]
    [CharP (FractionRing (Polynomial R)) p]
    (L : Type u) [Field L] [Algebra (FractionRing (Polynomial R)) L]
    [Algebra (Polynomial R) L] [IsScalarTower (Polynomial R) (FractionRing (Polynomial R)) L]
    [FiniteDimensional (FractionRing (Polynomial R)) L]
    [IsPurelyInseparable (FractionRing (Polynomial R)) L] :
    Module.Finite (Polynomial R) (integralClosure (Polynomial R) L) := by sorry
