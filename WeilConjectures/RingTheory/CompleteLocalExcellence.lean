/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import WeilConjectures.RingTheory.ExcellentRing
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.RegularLocusOpenFromPrimeQuotients
import WeilConjectures.RingTheory.RegularRingUniversallyCatenary
import WeilConjectures.RingTheory.CohenStructurePowerSeriesSurjection
import WeilConjectures.RingTheory.CompleteLocalGRing
import WeilConjectures.RingTheory.FiniteOverCompleteLocalProduct
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.RegularLocalLocalization

/-!
# Excellence of complete Noetherian local rings

Source: Stacks Project, More on Algebra, Tag 07QW, proposition-ubiquity-excellent,
clause (2) (blueprint: lem-per-complete-local-excellence).
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- Every complete Noetherian local commutative ring is excellent.

Source: Stacks Project, More on Algebra, Tag 07QW, proposition-ubiquity-excellent,
clause (2), with Tags 07PX, 07PS, 07PJ, 07PI, 07P9, 07PC, and Algebra Tag 032C
(blueprint: lem-per-complete-local-excellence).

Proof:
1. Write m for the maximal ideal. Completeness includes separatedness. Apply
   `lem-weil-pbc-complete-local-g-ring` to obtain the G-ring condition.
2. For any module-finite A-algebra B, `lem-weil-pbc-finite-over-complete-local-product`
   gives Noetherianity. For each prime q, the quotient D = B/q is a domain, and the
   images of module generators of B generate D. Thus D is module-finite over A.
   The domain clause of the same theorem makes D Noetherian, complete and local.
   Apply `lem-per-complete-local-domain-regular-open` to obtain a nonempty regular open.
3. Apply `lem-exc-regular-locus-open-from-prime-quotients` to B. Its regular locus is
   open. This includes the zero algebra, whose spectrum and regular locus are empty.
4. By `lem-per-j2-finite-algebra-criterion`, every finite type A-algebra has open
   regular locus. Hence A is J-2, without assuming that A is reduced or a domain.
5. Noetherianity makes m finitely generated. The Cohen structure theorem
   `lem-weil-pbc-cohen-structure-power-series-surjection` presents A as a quotient of
   a finite-variable power series ring S over a field or Cohen ring. By
   `lem-weil-pbc-power-series-field-cohen-regular-complete`, S is Noetherian regular
   local. Zero variables and both residue-characteristic cases are included.
6. By `lem-weil-pbc-regular-local-localization`, all prime localizations of S are
   regular local. Apply `lem-trf-regular-ring-universally-catenary` to S.
7. Every finite type A-algebra T is finite type over S: lift the finitely many
   coefficients in each polynomial expression along S → A. Universal catenarity of S
   makes T catenary, with bounded prime-chain lengths in each interval and equal
   saturated-chain lengths. These are intrinsic properties of T. Thus A is universally
   catenary, using `def-weil-pbc-finite-type-algebra` and `def-exc-excellent-ring`.
8. Noetherianity, the G-ring condition and J-2 give quasi-excellence. Combine this
   with universal catenarity using `def-exc-excellent-ring` to obtain excellence.
-/
theorem isExcellent_of_isNoetherianRing_of_isAdicComplete
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A] : IsExcellent A := by
  sorry
