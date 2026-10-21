/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Sheaf.AlgebraicGeometry.StrictNormalCrossingsBoundary
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import WeilConjectures.RingTheory.RegularLocalLocalization
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs
import WeilConjectures.RingTheory.RootAlgebraRegularAtRoot
import WeilConjectures.RingTheory.LocalizationOfRegularRing
import WeilConjectures.RingTheory.HypersurfaceDerivationRegular

/-!
# Regularity of coordinate faces of finite SNC root algebras

Source: ILO, Travaux de Gabber, Expose IX, Proposition 2.1 proof, printed p.133;
Stacks Project, Tag 0BIA, `lemma-strict-normal-crossings`.
(blueprint: lem-sfb-snc-finite-root-face-regular).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- Every coordinate face of a simultaneous root algebra along the distinct reduced
branches of an SNC boundary on a regular affine scheme is a regular Noetherian ring.
The second quotient kills exactly the images of the coordinates indexed by J.
Empty or disconnected intersections, the empty tuple, and the zero ring are allowed.

Source: ILO IX, Proposition 2.1 proof, printed p.133; Stacks Tag 0BIA.
(blueprint: lem-sfb-snc-finite-root-face-regular).

Proof:
1. Setting the coordinates indexed by J to zero identifies the face ring E_J with
   (A/(t_j : j in J))[x_i : i outside J]/(x_i^n-t_i). The mutually inverse maps
   send coefficients and surviving roots to their classes. Since n is positive,
   the killed root relations impose exactly t_j = 0. Local Noetherianity of A's
   spectrum gives Noetherianity of A by `pqf-lem-affine-open-locnoeth`, and finite
   presentation gives Noetherianity of E_J by
   `lem-weil-pbc-finite-type-algebra-noetherian`.
2. For a prime q of E_J contract to p in A, put R = A_p, and let S index the
   equations belonging to p; J is contained in S. For every L contained in S,
   R_L = R/(t_l : l in L) is regular local, of dimension dim(R)-card(L), by the
   SNC intersection criterion, `lem-weil-pbc-affine-open-stalk-localization`, and
   `lem-weil-pbc-localization-at-prime-of-quotient`. Equations outside S are units.
3. For every L contained in S and K disjoint from L, form B_{L,K} by adjoining the
   roots indexed by K over R_L. Induct simultaneously over L on card(K). These
   rings are Noetherian by `lem-weil-pbc-finite-type-algebra-noetherian`.
   Iterating `lem-weil-pbc-monic-quotient-free` gives the free monomial basis with
   all exponents less than n. Reordering the presentations fixes every generator.
   For empty K regularity follows from `lem-weil-pbc-regular-local-localization`.
4. Choose i in nonempty K, put D = B_{L,K minus i}, and B = D[T]/(T^n-t_i), with
   root u. D is regular by induction. If a prime Q contains u, then i belongs
   to S minus L. The dimension equalities for L and L union i imply t_i is
   nonzero in R_L. The regular local ring R_L is a domain by
   `lem-sc-regular-local-domain`, so t_i acts injectively on R_L and hence on
   its free module D, coefficient by coefficient in the monomial basis.
5. Quotienting D by t_i gives B_{L union i,K minus i}; the inverse presentation
   maps fix coefficients and surviving roots, as also follows from the quotient
   compatibility in `lem-weil-pbc-monic-quotient-free`. This is regular by the
   smaller-root induction. Apply `lem-sbc-root-algebra-regular-at-root` using
   Noetherianity, injective multiplication by t_i, and this regular quotient.
   It gives regularity of B_Q at primes containing u.
6. At a prime Q missing u, also t_i is outside Q. F = D[1/t_i] is regular by
   `lem-weil-pbc-localization-of-regular-ring`, and F[T] is regular by
   `lem-trf-polynomial-ring-regular-base`. In F[T]/(T^n-t_i), T has inverse
   T^(n-1)/t_i, and the derivative n*T^(n-1) is a unit. Thus
   `lem-weil-pbc-hypersurface-derivation-regular` makes this ring regular.
   It is B[1/t_i], and its localization at Q is B_Q by inverse fraction maps.
   This proves the simultaneous induction step at every prime.
7. Take L = J and K the complementary indices. The presentation in step 1
   identifies B_{J,K} with the localization of E_J away from p, by inverse maps
   fixing coefficients and roots. Localizing further at q gives (E_J)_q.
   Every prime localization is therefore regular local; E_J is Noetherian by
   step 1, so it is regular in the sense of `def-weil-regular-scheme`.
   For an empty stratum E_J is zero and has no primes. The argument also covers
   disconnected strata, J empty, r = 0, A = 0, and n = 1.
-/
theorem isRegularRing_snc_finiteRoot_face
    (A : Type u) [CommRing A] (hA : IsRegularScheme (Spec (.of A)))
    (r : ℕ) (t : Fin r → A) (H : (Spec (.of A)).IdealSheafData)
    (hH : IsStrictNormalCrossingsBoundary H)
    (hreduced : ∀ i : Fin r, _root_.IsReduced (A ⧸ Ideal.span ({t i} : Set A)))
    (hdistinct : Function.Injective
      (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({t i} : Set A)))
    (hbranches : Set.range (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({t i} : Set A)) =
      Set.image (Set.image Subtype.val) (irreducibleComponents (H.support : Set (Spec (.of A)))))
    (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : A)) (J : Set (Fin r)) :
    IsRegularRing ((MvPolynomial (Fin r) A ⧸
      Ideal.span (Set.range (fun i : Fin r ↦
        (MvPolynomial.X i : MvPolynomial (Fin r) A) ^ n - MvPolynomial.C (t i)))) ⧸
      Ideal.map (Ideal.Quotient.mk
        (Ideal.span (Set.range (fun i : Fin r ↦
          (MvPolynomial.X i : MvPolynomial (Fin r) A) ^ n - MvPolynomial.C (t i)))))
        (Ideal.span ((fun j : Fin r ↦ (MvPolynomial.X j : MvPolynomial (Fin r) A)) '' J))) := by
  sorry

end AlgebraicGeometry
