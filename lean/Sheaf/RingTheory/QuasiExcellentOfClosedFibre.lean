/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q78
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import WeilConjectures.RingTheory.GRing
public import Sheaf.RingTheory.ExcellentRing
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.AlgebraicGeometry.GenericFlatness
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Proper
import WeilConjectures.RingTheory.FiniteTypeGRing
import WeilConjectures.RingTheory.FlatUnderRegular
import WeilConjectures.RingTheory.RegularLocalLocalization
import Sheaf.RingTheory.JTwoFiniteAlgebraCriterion
import Sheaf.RingTheory.RegularLocusOpenFromPrimeQuotients

/-!
# Quasi-excellence from a Jacobson closed fibre

Source: Kurano--Shimomoto, Ideal-adic completion of quasi-excellent rings (after Gabber),
Theorem 4.1, printed pp.4--7 (blueprint: lem-per-g-ring-quasi-excellent-closed-fibre).
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- A Noetherian G-ring is quasi-excellent if its quotient by an ideal contained in
all maximal ideals is quasi-excellent. No completeness or characteristic assumption is needed.

Source: Kurano--Shimomoto, Ideal-adic completion of quasi-excellent rings (after Gabber),
Theorem 4.1, printed p.4, proof pp.6--7
(blueprint: lem-per-g-ring-quasi-excellent-closed-fibre).

Proof (the seven steps of the node):
1. It suffices to find a nonempty regular open in each nonzero module-finite domain
   algebra B over A. Indeed, finite algebras are Noetherian by
   lem-weil-pbc-finite-algebra-noetherian, and their prime quotients are again finite
   A-modules. Apply lem-exc-regular-locus-open-from-prime-quotients, followed by
   lem-per-j2-finite-algebra-criterion, to obtain J-2 for A. With the given G-ring
   condition this is quasi-excellence by def-exc-excellent-ring.
2. For such B set J = IB. By lem-weil-pbc-finite-type-over-g-ring, B is a G-ring.
   The algebra B/J is finite type over A/I, so it is J-2 by composing finite sets
   of algebra generators and using the J-2 clause of def-exc-excellent-ring.
   If some maximal ideal m of B did not contain J, then I(B/m) = B/m. This finite
   A-module would vanish by lem-weil-pbc-nakayama-jacobson, a contradiction.
3. Apply lem-per-g-ring-alteration-closed-fibre-neighbourhood at every prime q of B.
   It gives a basic neighbourhood D(b_q), alteration covers regular above V(J),
   and their proper surjective witnesses. The b_q generate the unit ideal:
   otherwise a maximal ideal containing them contradicts its own chosen b_q.
   A finite linear combination expressing 1 therefore gives a finite basic cover.
4. Apply lem-sbc-generic-flatness to the finitely many finite-type alteration maps.
   By lem-weil-pbc-spec-localization-away-basic-open shrink each flat open to a
   nonempty basic open D(a/b^n). The product c of its nonzero numerators is nonzero
   because B is a domain (the empty product is 1). Every alteration map is flat
   over D(c) intersected with its base D(b).
5. For p in D(c), choose a maximal ideal m containing p, hence containing J.
   Choose D(b) containing m and therefore p. Lift p to v1 in the proper surjective
   witness. By pqf-lem-proper-closed-map the image of the closure of v1 is the
   closure of p, so m lifts to a specialization v2 of v1. A witness chart containing
   v2 also contains v1. Its images x1 and x2 in the alteration lie over p and m,
   respectively, with x2 specializing x1.
6. The closed-fibre clause of lem-per-g-ring-alteration-closed-fibre-neighbourhood
   makes the stalk at x2 regular local. An affine open around x2 also contains x1.
   By lem-weil-pbc-affine-open-stalk-localization its stalk at x1 is a further prime
   localization of its stalk at x2. Apply lem-weil-pbc-regular-local-localization.
7. By Step 4 and def-weil-flat-morphism the local map from B_p to the stalk at x1
   is flat. Identify the base stalk by lem-weil-pbc-affine-open-stalk-localization.
   The source is Noetherian by lem-weil-pbc-localization-noetherian, and the target
   is regular local by Step 6. Apply lem-weil-pbc-flat-under-regular to obtain
   regularity of B_p. Thus D(c) is regular, and it is nonempty since the zero prime
   of B lies in it. This proves Step 1. Zero rings have empty spectra and cause no
   exception to the regular-locus conditions. -/
theorem isQuasiExcellent_of_quotient_of_isGRing
    (A : Type u) [CommRing A] [IsNoetherianRing A] (hG : IsGRing A)
    (I : Ideal A) (hI : ∀ m : Ideal A, m.IsMaximal → I ≤ m)
    (hquot : IsQuasiExcellent (A ⧸ I)) : IsQuasiExcellent A := by
  sorry
