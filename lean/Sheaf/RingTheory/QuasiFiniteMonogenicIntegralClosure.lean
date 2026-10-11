/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.RingTheory.Localization.Away.Basic
import Sheaf.RingTheory.QuasiFiniteAtPrime

/-!
# Integral closure of a monogenic algebra near a quasi-finite prime

Source: Stacks Project, Algebra, Lemma Tag 00Q8
(blueprint: lem-weil-pbc-quasi-finite-monogenic-integral-closure).
-/

universe u

namespace Algebra

/-- Stacks Project, Algebra, Lemma Tag 00Q8:
(blueprint: lem-weil-pbc-quasi-finite-monogenic-integral-closure).
The canonical inclusion of the integral closure becomes an isomorphism after localizing
at an integral element outside a quasi-finite prime of a polynomial quotient.

Proof plan (the nine steps of the node):
1. Write `x` for the image of `X`. Every quotient element is a polynomial in `x`.
   Constants belong to the integral closure. A good relation in `x` has coefficients
   in that closure and at least one coefficient outside `q`.
2. The closure is integrally closed in the quotient: adjoining an element integral
   over it gives a finite module (lem-weil-pbc-finite-of-integral-generators), hence
   an integral algebra (lem-weil-pbc-finite-algebra-is-integral); transitivity
   (lem-weil-pbc-integral-transitive) shows that the element is integral over `R`.
3. The leading coefficient times `x` is integral over the closure by
   lem-weil-pbc-leading-coefficient-times-root-integral (Stacks Tag 00PQ), hence
   belongs to the closure by step 2.
4. If every polynomial in `I` has coefficients in the contraction of `q`, the fibre
   is the polynomial ring over its residue field. Coefficient reduction and evaluation
   give mutually inverse maps, using lem-weil-pbc-algebra-tensor-pushout-universal-property.
5. That fibre cannot have an isolated prime: apply
   lem-weil-pbc-reduced-strongly-transcendental-not-quasi-finite to the indeterminate
   over the residue field (the polynomial ring is a domain by
   lem-weil-pbc-polynomial-ring-domain). Quasi-finiteness contradicts step 4.
   Thus a polynomial in `I` has a coefficient outside the contraction, giving a good relation.
6. Induct on the length of a good relation. Length zero is impossible since its sole
   coefficient is zero and lies in `q`.
7. If the leading coefficient `b` is outside `q`, use `g = b`. Step 3 gives `b*x`
   in the closure. The localized inclusion is injective by the fraction-zero criterion;
   it is surjective by substituting `x = (b*x)/b` into every polynomial numerator.
8. If `b` lies in `q`, combine `b*x` with the next coefficient. Step 3 makes the
   shortened relation a relation over the closure, still good since `b*x` lies in `q`.
   Apply the induction hypothesis.
9. Apply this induction to the good relation of step 5 to obtain the required `g`. -/
theorem quasiFiniteAtPrime_monogenic_integralClosure
    (R : Type u) [CommRing R] (I : Ideal (Polynomial R))
    (q : PrimeSpectrum (Polynomial R ⧸ I))
    (hq : IsQuasiFiniteAtPrime R (Polynomial R ⧸ I) q) :
    ∃ g : integralClosure R (Polynomial R ⧸ I), (g : Polynomial R ⧸ I) ∉ q.asIdeal ∧
      Function.Bijective
        (Localization.awayMap (integralClosure R (Polynomial R ⧸ I)).val.toRingHom g) := by
  sorry

end Algebra
