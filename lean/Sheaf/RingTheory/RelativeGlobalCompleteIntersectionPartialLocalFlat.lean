/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.Paper.RelativeGlobalCompleteIntersectionPresentation
public import Mathlib.RingTheory.RingHom.Flat
import Sheaf.Paper.NoetherianApproximation
import Sheaf.Paper.RelativeGlobalCompleteIntersectionBaseChange
import Sheaf.RingTheory.DirectedUnionSubringsFlatModule
import Sheaf.RingTheory.FibreLocalRingNaturalIso
import Sheaf.RingTheory.GlobalCompleteIntersectionLocalRegularSequence
import Sheaf.RingTheory.RegularSequenceFlatClosedFiber

/-!
# Flatness of successive localized complete-intersection quotients

Source: Stacks Project, Algebra, Lemma 00SV (2)
(blueprint: lem-weil-pbc-relative-global-complete-intersection-partial-local-flat).
-/

@[expose] public section

universe v

namespace Algebra

/-- Every initial quotient of the polynomial local ring at a prime of a relative global
complete intersection is flat over the base.
Source: Stacks Project, Algebra, Lemma 00SV (2)
(blueprint: lem-weil-pbc-relative-global-complete-intersection-partial-local-flat).

Proof (the seven steps of the DAG node):
1. For Noetherian `R`, put `p = q' ∩ R`. The polynomial ring is free over `R`, hence flat,
   and is Noetherian by the finite-type algebra theorem. The flat-local-ring-maps lemma
   gives a flat local map `R_p → P_q'`, whose extended maximal ideal is `p P_q'`.
2. Polynomial scalar extension and fibre-prime correspondence identify the closed fibre
   with a localization of `κ(p)[x]`. Relative-global-complete-intersection base change
   gives dimension `n-c`. The global-complete-intersection-local-regular-sequence lemma
   makes the equations regular there. Transport them through the natural fibre-local-ring
   isomorphism to `P_q'/p P_q'`.
3. Grothendieck's regular-sequence-flat lemma makes each initial quotient flat over `R_p`;
   flat-over-localization makes it flat over `R`. This proves the Noetherian case.
4. Relative-global-complete-intersection Noetherian approximation supplies a finite-type
   integer subring containing the coefficients. Its finite-type over-subrings form a
   directed union equal to `R`; each is Noetherian and base change preserves the condition.
5. Contract `q'` to each polynomial subring and pass to its localization and initial
   quotient. The Noetherian case gives flatness there. The inclusions induce compatible
   transition maps and maps to the required quotient.
6. Every fraction comes from a stage by including its finitely many coefficients. If its
   image vanishes, express its numerator in the initial ideal after clearing denominators;
   including those finitely many coefficients makes it vanish at a later stage.
7. The directed-union-subrings-flat-module lemma applies to these compatible modules and
   the two conditions of step 6, proving flatness over `R` for every prime and every index. -/
theorem relativeGlobalCompleteIntersection_partial_local_flat
    (R : Type v) [CommRing R] (n c : ℕ) (f : Fin c → MvPolynomial (Fin n) R)
    (h : IsRelativeGlobalCompleteIntersectionPresentation f)
    (q : PrimeSpectrum (MvPolynomial (Fin n) R ⧸ Ideal.span (Set.range f)))
    (i : ℕ) (hi : i ≤ c) :
    Module.Flat R
      (Localization.AtPrime
        (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span (Set.range f))) q).asIdeal ⧸
          Ideal.map
            (algebraMap (MvPolynomial (Fin n) R)
              (Localization.AtPrime
                (PrimeSpectrum.comap (Ideal.Quotient.mk (Ideal.span (Set.range f))) q).asIdeal))
            (Ideal.span (f '' {j : Fin c | j.val < i}))) := by
  sorry

end Algebra
