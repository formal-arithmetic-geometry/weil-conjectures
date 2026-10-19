/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N3
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Sheaf.RingTheory.ExcellentRing
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.FiniteType
import Sheaf.RingTheory.RegularLocusOpenFromPrimeQuotients
import Sheaf.RingTheory.RegularRingUniversallyCatenary
import Sheaf.RingTheory.CohenStructurePowerSeriesSurjection
import Sheaf.RingTheory.CompleteLocalGRing
import Sheaf.RingTheory.FiniteOverCompleteLocalProduct
import Sheaf.RingTheory.PowerSeriesFieldCohenRegularComplete
import Sheaf.RingTheory.RegularLocalLocalization
import Sheaf.RingTheory.CompleteLocalDomainRegularOpen
import Sheaf.RingTheory.JTwoFiniteAlgebraCriterion

/-!
# Complete Noetherian local rings are excellent

Source: Stacks Project, More on Algebra, Tag 07QW, proposition-ubiquity-excellent,
clause (2); Algebra, Remark 032C (blueprint: lem-per-complete-local-excellence).
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- Every Noetherian local ring complete for its maximal-ideal-adic topology is excellent.

Source: Stacks Project, More on Algebra, Tag 07QW, proposition-ubiquity-excellent,
clause (2) (blueprint: lem-per-complete-local-excellence).

Proof (the eight steps of the node):
1. Write m for the maximal ideal. Completeness includes separatedness. Apply
   lem-weil-pbc-complete-local-g-ring to obtain the G-ring condition.
2. For any finite A-algebra B, lem-weil-pbc-finite-over-complete-local-product makes
   B Noetherian. Each prime quotient D = B/q is a domain and remains finite over A:
   reduce a finite module generating family modulo q. The domain clause of the same
   lemma makes D Noetherian, local and complete. Apply
   lem-per-complete-local-domain-regular-open to obtain a nonempty regular open in Spec D.
3. Apply lem-exc-regular-locus-open-from-prime-quotients to B, obtaining its open
   regular locus. This includes the zero finite algebra, whose spectrum is empty.
4. Apply lem-per-j2-finite-algebra-criterion: every finite type A-algebra has open
   regular locus. This is the J-2 condition, without assuming A reduced or a domain.
5. Noetherianity makes m finitely generated. Apply
   lem-weil-pbc-cohen-structure-power-series-surjection to present A as a quotient
   of S = Lambda[[x_1,...,x_n]], with Lambda a field or a Cohen ring. By
   lem-weil-pbc-power-series-field-cohen-regular-complete, S is Noetherian regular
   local. This covers n = 0 and both residue-characteristic cases.
6. By lem-weil-pbc-regular-local-localization, every prime localization of S is
   regular local. Apply lem-trf-regular-ring-universally-catenary to S.
7. Every finite type A-algebra T is finite type over S: lift its polynomial
   coefficients along the surjection S -> A. Universal catenarity of S makes T
   catenary. Thus A is universally catenary, including both the finite bound on
   prime-chain lengths in each interval and equality of saturated-chain lengths.
8. Noetherianity, the G-ring condition and J-2 make A quasi-excellent. Together
   with universal catenarity this is IsExcellent A, by def-exc-excellent-ring. -/
theorem isExcellent_of_isNoetherianRing_of_isAdicComplete
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] : IsExcellent A := by
  sorry
