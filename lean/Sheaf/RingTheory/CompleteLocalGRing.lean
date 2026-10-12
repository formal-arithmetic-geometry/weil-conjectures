/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Sheaf.RingTheory.GRing
import Sheaf.AlgebraicGeometry.QuasiFiniteMorphism
import Sheaf.RingTheory.AdicCompletionNoetherian
import Sheaf.RingTheory.CompleteLocalDomainFiniteOverRegular
import Sheaf.RingTheory.CompleteLocalQuotient
import Sheaf.RingTheory.CompletionRegularLocal
import Sheaf.RingTheory.FibreRingNoetherian
import Sheaf.RingTheory.FormalFibreQuasiFiniteAscent
import Sheaf.RingTheory.GRingPairsOfPrimes
import Sheaf.RingTheory.PowerSeriesPolynomialFormalFiber
import Sheaf.RingTheory.RegularLocalLocalization

/-!
# Complete local Noetherian rings are G-rings

Source: Stacks Project, More on Algebra, Proposition 07PS (blueprint:
lem-weil-pbc-complete-local-g-ring).
-/

@[expose] public section

universe u

/-- A Noetherian complete local ring is a G-ring. Source: Stacks Project,
More on Algebra, Proposition 07PS (blueprint: lem-weil-pbc-complete-local-g-ring).
Proof (Stacks 07PS, following the seven steps of the node):
1. By lem-weil-pbc-g-ring-check-pairs-of-primes, reduce to the formal fibres over the zero
prime of B = S/q. Quotients and localizations are Noetherian; their completions and
fibres are Noetherian by lem-weil-pbc-adic-completion-noetherian and
lem-weil-pbc-fibre-ring-noetherian. It remains to check geometric regularity.
2. By lem-weil-pbc-complete-local-quotient, B is a complete Noetherian local domain.
Thus reduce to a complete local domain A, its fraction field K, and the fibres of
completed prime localizations over K.
3. By lem-weil-pbc-complete-local-domain-finite-over-regular, choose a regular complete
local subring A₀ over which A is finite. It is a power series ring over a field or a
Cohen ring. Since it is a subring of a domain, it has a fraction field K₀.
4. Finiteness implies quasi-finiteness: each fibre is finite-dimensional over its
residue field; its prime quotients are fields, and the Chinese remainder theorem
bounds the number of maximal ideals by that dimension. Apply
lem-weil-pbc-formal-fibre-quasi-finite-ascent to reduce geometric regularity of the
formal fibre of A to that of A₀.
5. By lem-weil-pbc-regular-local-localization and lem-weil-pbc-completion-regular-local,
the completed prime localization of A₀ is regular. Its tensor product with K₀ is a
localization, hence regular; it is Noetherian by the completion and fibre lemmas.
6. In characteristic zero every finite purely inseparable field extension is trivial,
so this regular fibre is geometrically regular by the definition in def-weil-pbc-g-ring.
7. In positive characteristic A₀ cannot be a power series ring over a Cohen ring:
a Cohen ring has characteristic zero, as its nonzero prime-number uniformizer is
not a unit. Thus A₀ is a power series ring over a field. Apply
lem-weil-pbc-helper-g-ring-char-p with m = 0, and transport along the power-series
isomorphism. Combining both characteristics with the preceding reductions proves
geometric regularity of every required formal fibre, hence the G-ring condition. -/
theorem isGRing_of_isNoetherianRing_of_isAdicComplete
    (S : Type u) [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    [IsAdicComplete (IsLocalRing.maximalIdeal S) S] : IsGRing S := by
  sorry
