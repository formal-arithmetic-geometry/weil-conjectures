/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.RegularLogSmoothMonomialChart
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.RegularLocalRing.Defs

import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Sheaf.AlgebraicGeometry.AffineFormallySmooth
import Sheaf.RingTheory.SmoothOverFieldRegularLocal
import WeilConjectures.AlgebraicGeometry.Regular
import WeilConjectures.Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Geometry of a monomial trait model

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVI,
Lemma 3.5.13(i), printed pp.250--251
(blueprint: lem-per-primitive-monomial-trait-geometry).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A monomial hypersurface over a trait is Noetherian, integral and regular, with smooth
 generic fibre, if some nonzero exponent is invertible in the fraction field. Zero
 exponents are permitted. The quotient and coefficient map are the existing
 `monomialTraitAlgebra` and `monomialTraitAlgebraMap`; the generic fibre is the actual
 scheme pullback along `Spec (FractionRing R) → Spec R`.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Expose XVI,
Lemma 3.5.13(i), printed pp.250--251
(blueprint: lem-per-primitive-monomial-trait-geometry).

Proof (the source leaves (i) as an exercise; this is the DAG's reconstruction):
1. Put P = R[T_1,...,T_n], M = product(T_i^a_i), f = M - pi and B = P/(f).
   Finite type over the Noetherian ring R makes B Noetherian
   (lem-weil-pbc-finite-type-algebra-noetherian). The dimension-one local ring R has
   principal maximal ideal, so is regular; pi is nonzero and is not in (pi)^2.
   Krull intersection (lem-weil-pbc-krull-intersection-jacobson) shows that every
   nonzero element of R is a power of pi times a unit. Hence R[1/pi] is its fraction field K.
2. The generic fibre has ring C = K[T_1,...,T_n]/(f), by the maps on generators.
   Choose j with a_j nonzero and invertible in K. The equation M = pi makes every T_i
   with a_i > 0 a unit in C. Thus the j-th derivative is the unit a_j*pi/T_j.
   This is a standard smooth presentation (def-weil-pbc-standard-smooth-algebra), so C
   is smooth (lem-weil-pbc-standard-smooth-is-smooth), and its prime localizations
   are regular (lem-weil-pbc-smooth-over-field-regular-local).
3. To obtain scheme smoothness, the presentation is finite. For a square-zero ideal J
   in a K-algebra D, lift the coordinates of C → D/J to elements t_i. The derivative d
   at the lifts is invertible: inverses lift across J since (1+z)(1-z) = 1 for z in J.
   Replace t_j by t_j - d⁻¹*f(t). Polynomial expansion kills f since J^2 = 0.
   The affine lifting criterion (lem-weil-pbc-affine-formally-smooth-iff-ring-lifting)
   and finite presentation give a smooth generic-fibre morphism.
4. For a prime q of P containing f and pi, choose i with a_i > 0 and T_i in q.
   The polynomial-localization order-reflection lemma
   (lem-trf-polynomial-localization-order-reflection) makes P_q regular local.
   Apply it again after killing T_i: pi is not in the squared maximal ideal of the
   resulting localization of R[T_h : h ≠ i]. Since f maps to -pi, f is not in the
   squared maximal ideal of P_q. The hypersurface criterion
   (lem-weil-pbc-regular-local-hypersurface-criterion) and localization of quotients
   (lem-weil-pbc-localization-at-prime-of-quotient) make the corresponding B-localization
   regular. Primes avoiding pi are covered by step 2. Thus B is a regular ring.
5. The monomials with exponent vector b not componentwise at least a form an R-basis
   (lem-per-monomial-quotient-normal-basis). Membership in pi^r B means each coefficient
   lies in pi^r R. Krull intersection for the finite R-module R therefore gives
   intersection_r pi^r B = 0, without assuming B finite as an R-module.
6. Modulo pi the ring is k[T_1,...,T_n]/(M), graded with degree-zero part the field k.
   An idempotent with zero constant term cannot have a least positive nonzero degree:
   its square has zero component in that degree. Thus the only idempotents are 0 and 1.
   Replace an idempotent e of B by 1-e if necessary so e is in pi B. Then e = e^r is in
   every pi^r B, and step 5 gives e = 0. Hence B also has only trivial idempotents.
7. Sending all T_i to zero gives a surjection B → k because some a_i is positive.
   Consequently Spec B is nonempty. Its global sections are B, so the idempotent
   criterion (lem-pc-scheme-connected-iff-idempotents) makes it connected. Step 4 makes
   it regular. A connected regular locally Noetherian scheme is integral
   (lem-sc-regular-connected-integral), and the definition of an integral scheme on
   the affine open Spec B (def-pc-integral-scheme) makes B an integral domain.
-/
theorem monomialTraitAlgebra_geometry
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
