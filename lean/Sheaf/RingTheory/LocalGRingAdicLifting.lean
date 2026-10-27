module

public import WeilConjectures.RingTheory.GRing
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
import WeilConjectures.RingTheory.FiniteModuleComplete
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import WeilConjectures.RingTheory.IntegralExtensionDimension
import Mathlib.RingTheory.Finiteness.Ideal
import WeilConjectures.RingTheory.CompletionFiniteExtension
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.RingTheory.AdicCompletion.LocalRing
import WeilConjectures.RingTheory.FiniteTypeGRing
import Sheaf.RingTheory.QuasiExcellentNagata
import WeilConjectures.RingTheory.NagataLocalization
import WeilConjectures.RingTheory.IsAnalyticallyUnramifiedOfIsNagataRing
import WeilConjectures.RingTheory.QuotientGRing
import Mathlib.RingTheory.AdicCompletion.Exactness
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Filtration

/-!
# Ideal-adic lifting of the G-ring property for local rings

Source: Kurano–Shimomoto, Ideal-adic completion of quasi-excellent rings (after Gabber),
Theorem 5.1, Step 2, equation (5.1), p.9, and Appendix A, Definition A.1(2), pp.14–15;
Rotthaus (1979), Theorem 3, pp.176–179.
(blueprint: lem-per-local-g-ring-adic-lifting)
-/

@[expose] public section

universe u

namespace IsLocalRing

/-- A Noetherian local ring complete along an ideal in its maximal ideal is a G-ring
if its quotient by that ideal is a G-ring. No characteristic, dimension, or universal
catenarity hypothesis is needed.

Source: Kurano–Shimomoto, Theorem 5.1, Step 2, equation (5.1), p.9, and Appendix A,
Definition A.1(2), pp.14–15; Rotthaus (1979), Theorem 3, pp.176–179.
(blueprint: lem-per-local-g-ring-adic-lifting)

Proof, following the twelve steps of the node:
1. By lem-per-g-ring-finite-domain-generic-test reduce to an arbitrary finite A-algebra
   domain B; its structure map need not be injective. It is Noetherian and semilocal.
   Put J = IB and r = Jac(B). By lem-weil-pbc-finite-module-complete-over-complete-noetherian,
   B is J-adically complete.
2. By lem-weil-pbc-finite-algebra-is-integral and lem-weil-pbc-integral-extension-dimension,
   maximal ideals of B lie over the maximal ideal m of A and r is the radical of mB.
   By lem-weil-pbc-fg-ideal-radical-power their powers are cofinal. By
   lem-weil-pbc-completion-finite-extension, the r-adic completion C of B is both
   the tensor product of the m-adic completion of A with B and the product of the
   completed maximal localizations of B. By lem-weil-pbc-adic-completion-noetherian
   and lem-weil-pbc-local-completion-local-ring, C is Noetherian and rC = Jac(C).
3. B/J is finite type over A/I, so lem-weil-pbc-finite-type-over-g-ring makes it a G-ring.
   By lem-per-semilocal-g-ring-j2 and lem-exc-quasi-excellent-nagata it is Nagata.
   By lem-per-adic-nagata-lifting B is Nagata. By lem-weil-pbc-nagata-localization and
   lem-weil-pbc-local-nagata-domain-analytically-unramified, each completed maximal
   localization of B is reduced, hence C is reduced.
4. For every nonmaximal prime Q of C above J, put p = Q ∩ B. By
   lem-per-g-quotient-completed-local-comparison there is a canonical regular faithfully
   flat map from the completed localization U_p of B to the completed localization T_Q
   of C. This does not assume that B is a G-ring.
5. For every prime p of B above J, lem-weil-pbc-g-ring-quotient makes B/p a G-ring.
   By the semilocal G-ring, Nagata, and localization inputs in step 3 its completed maximal
   localizations are reduced. By lem-weil-pbc-completion-finite-extension,
   lem-weil-pbc-completion-exact-finite-modules, and
   lem-weil-pbc-completion-finite-module-tensor their product is C/pC. Thus pC is radical.
6. It suffices to show each singular prime P of C contracts nontrivially to B.
   By lem-per-formal-singular-ideal-patching there is a nonzero radical ideal D of C
   whose extension to T_Q is the extension of the singular ideal of U_p above J;
   every singular P of C is nonzero.
7. Fix P. If a nonmaximal prime contains P + JC, the same patching theorem gives D ≤ P;
   take E = D and the singular ideal of U_p as its compatible ideal for each p.
   Otherwise take E = P and the unit ideal in each U_p: every nonmaximal Q above J
   avoids an element of P, so E extends to the unit ideal in T_Q. In both cases 0 ≠ E ≤ P.
8. By lem-per-compatible-formal-ideal-adic-descent, for a_n = (E + J^n C) ∩ B,
   a_n C = E + J^n C and a_(n+1) + J^n = a_n for n ≥ 1. Steps 4 and 5 verify faithful
   flatness and radical prime extensions; step 7 supplies one compatible ideal per p.
9. By lem-weil-pbc-krull-intersection-jacobson choose r ≥ 1 with E not contained in
   Jac(C)^r, then f_r in a_r whose image lies outside that power. Using the second
   identity in step 8 choose f_(n+1) in a_(n+1) with f_(n+1) - f_n in J^n.
10. J-adic completeness of B gives f in B with f - f_n in J^n for all n ≥ r. Its image
    modulo Jac(C)^r is that of f_r, since JC ≤ Jac(C), so f ≠ 0.
11. For fixed n ≥ r, later f_k lie in a_n. By
    lem-weil-pbc-krull-intersection-jacobson applied to B/a_n, f lies in a_n.
    Applying it again to C/E gives f in E ∩ B, hence in P ∩ B. Thus P ∩ B ≠ 0.
12. Consequently every localization of C at a prime contracting to zero in B is regular.
    Since B was arbitrary, lem-per-g-ring-finite-domain-generic-test proves A is a G-ring.
-/
theorem isGRing_of_isAdicComplete_quotient
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (I : Ideal A) (hI : I ≤ maximalIdeal A) [IsAdicComplete I A]
    (hquot : IsGRing (A ⧸ I)) : IsGRing A := by
  sorry

end IsLocalRing
