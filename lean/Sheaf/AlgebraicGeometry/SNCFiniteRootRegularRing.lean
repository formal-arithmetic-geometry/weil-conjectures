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
# Regularity of finite simultaneous roots along strict normal crossings

Source: ILO, Travaux de Gabber, Expose IX, Proposition 2.1 proof, printed p.133;
Stacks Project, Tag 0BIA, `lemma-strict-normal-crossings`.
(blueprint: lem-sfb-snc-finite-root-regular-ring).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- Adjoining simultaneous roots of the distinct reduced branches of an SNC boundary
on a regular affine scheme gives a regular Noetherian ring. The equations define reduced
closed subschemes, their zero loci are distinct, and these zero loci are precisely all
irreducible components of the boundary. No nontriviality assumption is imposed.

Source: ILO IX, Proposition 2.1 proof, printed p.133; Stacks Tag 0BIA.
(blueprint: lem-sfb-snc-finite-root-regular-ring).

Proof:
1. Local Noetherianity of the regular scheme gives Noetherianity of A by
   `pqf-lem-affine-open-locnoeth`. The finite polynomial quotient is Noetherian by
   `lem-weil-pbc-finite-type-algebra-noetherian`. The zero ring has no primes.
   For a prime q of the quotient, contract to p in A and identify the stalk with A_p
   using `lem-weil-pbc-affine-open-stalk-localization`.
2. Let S index the equations in p. For J contained in S put R_J = A_p/(t_j : j in J).
   The SNC regular-intersection condition, the stalk identification, and
   `lem-weil-pbc-localization-at-prime-of-quotient` make each R_J regular local with
   dim(R_J) + card(J) = dim(A_p). Equations not in S are units in all these rings.
3. For J contained in S and K disjoint from J, form B_{J,K} by adjoining the roots
   indexed by K over R_J. Iterating `lem-weil-pbc-monic-quotient-free` gives the finite
   free monomial basis with exponents less than n. The presentations can be reordered
   by maps fixing their generators. Induct simultaneously over J on card(K).
   The empty K case follows from `lem-weil-pbc-regular-local-localization`.
4. Choose i in K and set D = B_{J,K\{i}}, B = D[T]/(T^n-t_i), with root u.
   The induction makes D regular. At a prime Q containing u, i belongs to S.
   The dimension equalities show t_i is nonzero in R_J; this regular local ring is a
   domain by `lem-sc-regular-local-domain`, so t_i acts injectively on the free D.
5. Quotienting D by t_i gives B_{J union {i},K\{i}}: the two maps fix coefficients
   modulo t_i and the remaining roots, and their composites fix all generators.
   The induction makes this quotient regular. Apply
   `lem-sbc-root-algebra-regular-at-root` to obtain regularity of B_Q.
6. At a prime Q missing u, t_i is also outside Q. The ring E = D[1/t_i] is regular
   by `lem-weil-pbc-localization-of-regular-ring`, and E[T] is regular by
   `lem-trf-polynomial-ring-regular-base`. In E[T]/(T^n-t_i), T is invertible with
   inverse T^(n-1)/t_i. Thus the derivative n*T^(n-1) is a unit, and
   `lem-weil-pbc-hypersurface-derivation-regular` gives regularity of this quotient.
   Its localization at the extended prime is B_Q, since t_i is already invertible
   there. This completes the induction.
7. Take J empty and K all indices. Localization of the displayed presentation
   from A to A_p commutes with the quotient: mutually inverse maps fix coefficients
   and roots. Localizing further at q gives exactly the original prime localization.
   Thus every prime localization is regular local. For r = 0 the polynomial ring
   in no variables and its quotient by the empty relation ideal identify with A;
   this is the induction base. The argument also includes n = 1.
-/
theorem isRegularRing_snc_finiteRoot
    (A : Type u) [CommRing A] (hA : IsRegularScheme (Spec (.of A)))
    (r : ℕ) (t : Fin r → A) (H : (Spec (.of A)).IdealSheafData)
    (hH : IsStrictNormalCrossingsBoundary H)
    (hreduced : ∀ i : Fin r, _root_.IsReduced (A ⧸ Ideal.span ({t i} : Set A)))
    (hdistinct : Function.Injective
      (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({t i} : Set A)))
    (hbranches : Set.range (fun i : Fin r ↦ PrimeSpectrum.zeroLocus ({t i} : Set A)) =
      Set.image (Set.image Subtype.val) (irreducibleComponents (H.support : Set (Spec (.of A)))))
    (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : A)) :
    IsRegularRing (MvPolynomial (Fin r) A ⧸
      Ideal.span (Set.range (fun i : Fin r ↦
        (MvPolynomial.X i : MvPolynomial (Fin r) A) ^ n - MvPolynomial.C (t i)))) := by
  sorry

end AlgebraicGeometry
