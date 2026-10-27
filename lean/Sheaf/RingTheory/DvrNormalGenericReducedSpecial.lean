module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Spectrum.Maximal.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal
import WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions

/-!
# Normality over a DVR with reduced special fibre

Source: Prasad--Yu, On quasi-reductive group schemes, Appendix by Brian Conrad,
Remark A.3, printed p.27 (blueprint: lem-sfb-dvr-normal-generic-reduced-special).

The generic algebra is written as `T[1/pi]`, using the identification in the node
with `T ⊗[R] Frac(R)`. The special algebra is `T / pi T`. Normality is the inline
prime-localization condition of `def-weil-pbc-normal-ring`; in particular, it
allows the zero ring and does not require the algebra to be a domain.
-/

@[expose] public section

universe u v

namespace Algebra

/-- A finite-type flat algebra over a DVR is normal if its generic algebra is normal
and its special algebra is reduced. Its localization map into the generic algebra
is injective, and every integral element of that algebra comes from the original
algebra. The special fibre need not be normal, and may be empty.

Source: Prasad--Yu, Appendix Remark A.3, printed p.27; Stacks Project, Tags 055J,
034M and 030C (blueprint: lem-sfb-dvr-normal-generic-reduced-special).

Proof plan (the six steps of the node):
1. Put t = pi * 1 in T and B = T[1/t]. The DVR uniformizer is nonzero in the domain R.
   Tensoring multiplication by pi with the flat R-module T shows that multiplication
   by t is injective (def-sc-discrete-valuation-ring, def-weil-pbc-flat-ring-map).
   The localization zero criterion (def-weil-pbc-module-localization) now makes
   T -> B injective.
2. If z in B is integral over T (def-weil-pbc-integral-closure), write z = a/t^n
   with n minimal. If n > 0, multiply a monic equation of degree d by t^(n*d).
   Injectivity gives an equation in T whose reduction modulo t is a^d = 0.
   Reducedness gives a = t*b, contradicting minimality. Hence z comes from T.
   This extends the least-denominator argument in Stacks 055J to monic equations.
3. Normality of B (def-weil-pbc-normal-ring) makes all its prime localizations
   reduced domains. By lem-weil-pbc-prime-localizations-jointly-injective, B is
   reduced; injectivity of T -> B then makes T reduced.
4. R is Noetherian since every ideal is principal (def-weil-pbc-noetherian-ring).
   Apply lem-weil-pbc-finite-type-algebra-noetherian and then
   lem-weil-pbc-noetherian-finitely-many-minimal-primes to T.
5. Every nonzerodivisor of T remains one in B: clear a power of t in an equation
   (s/1)*(a/t^n) = 0. Thus fractions give an injective map Q(T) -> Q(B).
   An element of Q(T) integral over T maps to an element integral over B.
   By lem-weil-pbc-normal-ring-integrally-closed-total it belongs to B.
   Since B -> Q(B) is injective, its original monic equation holds in B;
   step 2 puts it in T. The injections identify the original fraction with it.
6. Apply lem-weil-pbc-reduced-normal-iff-integrally-closed-total-fractions to the
   reduced ring T with finitely many minimal primes and integral closedness from
   step 5. This gives normality. Step 2 gives the extra integral-element clause.
   For T = 0 there are no prime ideals and all image assertions hold. If the
   special fibre is empty, t is a unit and the same argument applies.
-/
theorem normal_of_normal_generic_reduced_special
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (pi : R) (hpi : IsLocalRing.maximalIdeal R = Ideal.span {pi})
    (T : Type v) [CommRing T] [Algebra R T] [FiniteType R T] [Module.Flat R T]
    (hgeneric : ∀ (p : Ideal (Localization.Away (algebraMap R T pi))) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p))
    (hspecial : IsReduced (T ⧸ Ideal.span {algebraMap R T pi})) :
    (∀ (p : Ideal T) [p.IsPrime],
      IsDomain (Localization.AtPrime p) ∧ IsIntegrallyClosed (Localization.AtPrime p)) ∧
    Function.Injective (algebraMap T (Localization.Away (algebraMap R T pi))) ∧
    (∀ z : Localization.Away (algebraMap R T pi), IsIntegral T z →
      ∃ a : T, algebraMap T (Localization.Away (algebraMap R T pi)) a = z) := by
  sorry

end Algebra
