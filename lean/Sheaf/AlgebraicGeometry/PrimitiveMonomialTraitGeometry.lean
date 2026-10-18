/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q106
-/
module

-- Existing definitions recorded by def-per-monomial-trait-model.
public import Sheaf.AlgebraicGeometry.RegularLogSmoothMonomialChart
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.DiscreteValuationRing.Basic

import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Polynomial.Eisenstein.Criterion
import Mathlib.Algebra.MvPolynomial.PDeriv
import Sheaf.RingTheory.HypersurfaceDerivationRegular
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Geometry of a primitive monomial model over a trait

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVI,
Definition 3.5.11 and Lemma 3.5.13(i), printed pp.250--251
(blueprint: lem-per-primitive-monomial-trait-geometry).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A monomial trait model with an exponent invertible in the fraction field is
Noetherian, integral and regular, and its generic fibre is smooth. Zero exponents
are allowed. The model and its coefficient map are the literal quotient and map
`monomialTraitAlgebra` and `monomialTraitAlgebraMap`, from Definition 3.5.11.
Source: ILO, Expose XVI, Lemma 3.5.13(i), printed pp.250--251
(blueprint: lem-per-primitive-monomial-trait-geometry).

Proof (the source leaves (i) as an exercise; this follows the node's solution):
1. The trait hypotheses identify R as a DVR, hence a PID. Its local rings are R
and its fraction field, both regular local, so R is a regular ring.
2. Polynomial regularity (`lem-trf-polynomial-ring-regular-base`) makes
P = R[T_1,...,T_n] regular and Noetherian. Its quotient B by f = product(T_i^a_i)-pi
is Noetherian by taking the images of finite generators of inverse-image ideals.
3. Choose j with a_j > 0, set A = R[T_i : i != j], and write f = v X^a_j - pi.
The polynomial UFD lemma makes A and P UFDs. The ideal pi A is prime because its
quotient is a polynomial ring over the residue field. The monomial v is outside
pi A and pi is outside pi^2 A by comparing constant coefficients and cancelling.
A common divisor of v and pi is a unit since pi is prime and does not divide v.
Thus f is primitive. The prime-ideal Eisenstein criterion makes f irreducible,
and `lem-per-polynomial-ufd-prime-quotient` makes B a domain.
4. On the generic fibre, product(T_i^a_i) = pi is a unit. Every positive-exponent
coordinate is a unit. Choose j with a_j invertible in the fraction field. The
partial derivative satisfies T_j D_j(f) = a_j pi, so D_j(f) is a unit, using
`def-weil-pbc-polynomial-partial-derivative`.
5. The generic coordinate algebra is finitely presented. For a square-zero ideal
J in a test algebra, lift coordinates of a map to its quotient. The lifted f lies
in J; the lifted D_j(f) is a unit, since a lift of an inverse has product 1+e with
e in J and inverse 1-e. Replace t_j by t_j-f(t)/D_j(f)(t). Taylor expansion modulo
J^2 gives f=0. This is formal smoothness, hence smoothness by finite presentation.
6. For a prime q of P containing f, put L = P_q. If pi is outside q, q contracts
to zero in R. Thus L/(f) is a prime localization of the generic coordinate ring.
Polynomial regularity over the fraction field and the unit derivative make that
ring regular by `lem-weil-pbc-hypersurface-derivation-regular`.
7. If pi is in q, L/(pi) is a prime localization of a polynomial ring over the
residue field, hence regular local. The independent-generators quotient lemma
`lem-weil-pbc-regular-local-quotient-independent-generators` implies pi is outside
the maximal-ideal square: otherwise every independent generator class vanishes,
forcing (pi)=0, impossible in the localization of the polynomial domain.
8. Let I be the positive-exponent coordinates in q. It is nonempty. If the sum
of their exponents is at least two, the monomial is in the maximal-ideal square,
so f is outside it by step 7. Otherwise I consists of a single coordinate of
exponent one. Its partial derivative on f is a unit in L; extend this derivation
to L by the quotient rule. Leibniz sends the maximal-ideal square into the
maximal ideal, so f is again outside the square. The regular-local hypersurface
criterion `lem-weil-pbc-regular-local-hypersurface-criterion` makes L/(f) regular
local. These and step 6 are all prime localizations of B, proving regularity.
-/
theorem primitive_monomial_trait_geometry
    (R : Type u) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    (hdim : ringKrullDim R = 1) (π : R)
    (hπ : IsLocalRing.maximalIdeal R = Ideal.span {π})
    (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ℕ)
    (ha : ∃ i : Fin n, a i ≠ 0 ∧ IsUnit (a i : FractionRing R)) :
    IsNoetherianRing (monomialTraitAlgebra R π n a) ∧
      IsDomain (monomialTraitAlgebra R π n a) ∧
      IsRegularRing (monomialTraitAlgebra R π n a) ∧
      Smooth (pullback.snd
        (Spec.map (CommRingCat.ofHom (monomialTraitAlgebraMap R π n a)))
        (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R))))) := by
  sorry

end AlgebraicGeometry
