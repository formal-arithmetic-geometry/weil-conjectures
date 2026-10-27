/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q38
-/
module

public import Sheaf.RingTheory.ExcellentRing
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Algebra.Rat
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.Topology.Inseparable
import WeilConjectures.RingTheory.FiniteTypeGRing
import WeilConjectures.RingTheory.RegularLocalOfFlatWithRegularClosedFiber
import WeilConjectures.RingTheory.FlatUnderRegular
import WeilConjectures.RingTheory.RegularLocalLocalization

/-! # Quasi-excellence of complete pairs in characteristic zero

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé I, Théorème 9.2,
printed p.17; Temkin, arXiv:0904.1592v2, Theorem 2.1.6 and Remark 2.1.7,
printed p.9 (blueprint: lem-per-qe-complete-pair-lifting).
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- A Noetherian rational algebra complete along an ideal is quasi-excellent exactly
when its quotient by that ideal is quasi-excellent.
Source: Travaux de Gabber, Exposé I, Théorème 9.2, printed p.17; Temkin,
Theorem 2.1.6 and Remark 2.1.7, printed p.9
(blueprint: lem-per-qe-complete-pair-lifting).

Proof (Kurano--Shimomoto, Ideal-adic completion of quasi-excellent rings,
Theorem 5.1, Steps 1--3; converse: Stacks Tags 07PV, 07QT, 07P7):
1. If A is quasi-excellent, its quotient is a finite type A-algebra, hence a G-ring
   by lem-weil-pbc-finite-type-over-g-ring. Every finite type algebra over A/J is
   finite type over A, so its regular locus is open. Thus A/J is quasi-excellent.
2. For the converse, suppose A/J is quasi-excellent but A is not. Apply
   lem-per-qe-normal-counterexample-reduction to obtain the normal Nagata universally
   catenary rational domain R and nonzero nonunit x, with quasi-excellent nonzero
   quotients and the specified finite-extension integral-closure properties.
3. By lem-per-qe-minimal-formal-defect choose a least-height formal singular prime,
   of height h at least two, in the ring C attached to an integral closure B and a
   maximal ideal. All localizations of B at height at most h are excellent.
   The comparisons of lem-per-qe-semilocal-defect-height give height h contracted
   singular primes and height h+1 boundary primes in its normalized Delta(x).
4. Apply lem-per-qe-alteration-regular-neighbourhood at every prime of B of height
   at most h, using B/xB quasi-excellent. The resulting distinguished opens form
   an open Omega containing all such primes, with proper surjective witnesses
   and covers mapping to schemes regular above V(x).
5. If Q belongs to Delta(x) and Omega, choose its semilocal lift over the contracted
   singular prime. Pull back the witness along the localized completion map.
   It stays surjective by lem-weil-pbc-surjective-base-change and closed by
   def-weil-proper-morphism.
6. Lift the singular prime to the witness. By lem-trf-closed-map-specializing its
   specialization over Q lifts as well. An open chart containing this specialization
   also contains its generalization. The specialization maps to a regular point
   of the original alteration since x belongs to Q.
7. The resulting local map is flat by lem-weil-pbc-flat-ring-map-iff-flat-affine,
   lem-weil-pbc-flat-morphism-base-change and def-weil-flat-morphism. The completion
   modulo x agrees with the semilocal ring modulo x, so its closed fibre is a field.
   The rings are Noetherian by lem-weil-pbc-finite-type-algebra-noetherian. Apply
   lem-weil-pbc-flat-over-regular-with-regular-fibre to obtain regularity upstairs.
8. Regularity passes to the generalization by lem-weil-pbc-regular-local-localization.
   Its map from the singular local ring of the completion is flat because it lies
   over the generic point of B, hence is a localization of a base change from a
   field. By lem-weil-pbc-flat-under-regular that singular local ring is regular,
   a contradiction. Therefore Delta(x) is disjoint from Omega.
9. Write the complement of Omega as V(H). It has finitely many minimal primes by
   lem-sc-finite-minimal-primes-over-ideal. Every prime in it has height at least
   h+1, and a height h+1 prime must be minimal over H, since a strict inclusion
   above another such prime increases height. Thus Delta(x) is finite.
10. Apply lem-per-qe-rotthaus-finite-boundary to B, x and the chosen formal prime.
    Its Noetherian, Nagata and completeness hypotheses come from the reduction,
    its singularity and contraction hypotheses from the two defect lemmas, and
    its finite boundary hypothesis from Step 9. Its nonzero contraction conclusion
    contradicts the chosen zero contraction. Hence A is quasi-excellent. -/
theorem isQuasiExcellent_iff_quotient_of_isAdicComplete
    (A : Type u) [CommRing A] [Algebra ℚ A] [IsNoetherianRing A]
    (J : Ideal A) [IsAdicComplete J A] :
    IsQuasiExcellent A ↔ IsQuasiExcellent (A ⧸ J) := by
  sorry
