/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q81
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Sheaf.RingTheory.ExcellentRing
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.Topology.Inseparable
import WeilConjectures.RingTheory.RegularLocalOfFlatWithRegularClosedFiber
import WeilConjectures.RingTheory.FlatUnderRegular
import WeilConjectures.RingTheory.RegularLocalLocalization

/-! # Gabber's lifting of quasi-excellence through an adic quotient

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé I, Théorème 9.2,
printed p.17, PDF p.23 (blueprint: lem-per-gabber-adic-quasi-excellence).
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- A commutative Noetherian ring complete for an ideal is quasi-excellent if its
quotient by that ideal is quasi-excellent. There is no characteristic, universal
catenarity or dimension hypothesis.

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé I, Théorème 9.2,
printed p.17, PDF p.23 (blueprint: lem-per-gabber-adic-quasi-excellence).

Proof: Kurano--Shimomoto, Ideal-adic completion of quasi-excellent rings (after
Gabber), Theorem 5.1, Steps 1--3, with its normalized boundary:
1. Suppose R is not quasi-excellent. Apply
   lem-per-gabber-normal-counterexample-reduction to the given complete pair.
   It yields a normal Nagata universally catenary domain A and a nonzero nonunit
   x, complete for (x), not quasi-excellent, with all nonzero quotients quasi-excellent.
   Its finite-extension normalizations have the stated finiteness, completeness
   and normal-completion properties. This reduction has no characteristic restriction.
2. By lem-per-gabber-minimal-formal-defect choose a triple (L, n, s) of least
   formal singular height h at least two. Write B for the normalization and C for
   its localized x-adic completion. The minimal singular prime s contracts to zero;
   every localization of B at height at most h is excellent. By
   lem-per-gabber-semilocal-defect-height the semilocal completions D_gamma are
   Noetherian and flat over B; their contracted singular primes s_gamma have
   height h, and all primes in the normalized Delta_gamma(x) have height h+1.
3. Apply lem-per-qe-alteration-regular-neighbourhood with J = xB at each prime
   q of B of height at most h. Its hypotheses follow from Step 2 and B/xB being
   quasi-excellent. Obtain distinguished opens D(b_q), schemes regular above V(x),
   and proper surjective witnesses with open covers mapping to those schemes.
   Their union Omega contains every prime of height at most h.
4. If Q belongs to Delta(x) and Omega, use
   lem-per-gabber-semilocal-defect-height to lift Q to a prime Q_tilde containing
   s_gamma + xD_gamma. Choose D(b_q) containing Q. Both Q_tilde and s_gamma
   survive inversion of b_q. Base change the proper witness and its open cover
   to this localized semilocal completion. The witness remains surjective by
   lem-weil-pbc-surjective-base-change and closed by def-weil-proper-morphism.
5. Lift s_gamma to a point xi_2 of this witness. By
   lem-trf-closed-map-specializing a specialization xi_1 lies over Q_tilde.
   An open chart containing xi_1 also contains xi_2. Their images eta_1 and eta_2
   in the base-changed regular-neighbourhood scheme satisfy eta_2 specializing
   to eta_1. The original image zeta_1 of eta_1 lies over Q containing x, so its
   local ring is regular by lem-per-qe-alteration-regular-neighbourhood.
6. By lem-weil-pbc-flat-ring-map-iff-flat-affine,
   lem-weil-pbc-flat-morphism-base-change and def-weil-flat-morphism, the map
   from the local ring at zeta_1 to the local ring at eta_1 is flat local.
   Its closed fibre is exactly the residue field at zeta_1: modulo x the
   completion equals the semilocal quotient, and all inverted elements avoid Q,
   hence are already units in that residue field. All chart rings and stalks are
   Noetherian by lem-weil-pbc-finite-type-algebra-noetherian and
   lem-weil-pbc-localization-noetherian. Since a field is regular, apply
   lem-weil-pbc-flat-over-regular-with-regular-fibre to get regularity at eta_1.
7. By lem-weil-pbc-regular-local-localization the local ring at eta_2 is regular.
   The point s_gamma lies over the generic point of B. Its local map to this
   regular stalk is a base change, followed by localization, of the generic
   fibre over the fraction field. It is flat by lem-pc-flat-field,
   lem-weil-pbc-flat-morphism-base-change and def-weil-flat-morphism.
   Its source and target are Noetherian as above. By
   lem-weil-pbc-flat-under-regular the local ring at s_gamma is regular,
   contradicting lem-per-gabber-semilocal-defect-height. Thus Delta(x) avoids Omega.
8. Write the complement of Omega as V(H). By lem-sc-finite-minimal-primes-over-ideal,
   H has finitely many minimal primes. Every prime in V(H) has height at least h+1.
   A height h+1 prime in V(H) is minimal over H: a strict inclusion above another
   prime containing H would increase height. Each member of Delta(x) has height
   h+1 by lem-per-gabber-semilocal-defect-height, so Delta(x) is finite.
9. Apply lem-per-qe-rotthaus-finite-boundary to B, x, n and s. Noetherianity,
   the Nagata property and completeness come from the reduction; minimal
   singularity comes from the minimal-defect lemma, positive contracted height
   from the semilocal-defect lemma, and finiteness of the same normalized boundary
   from Step 8. The resulting nonzero contraction contradicts s contracting to
   zero. This disproves the original supposition and proves quasi-excellence of R. -/
theorem isQuasiExcellent_of_quotient_of_isAdicComplete
    (R : Type u) [CommRing R] [IsNoetherianRing R]
    (J : Ideal R) [IsAdicComplete J R] (hquot : IsQuasiExcellent (R ⧸ J)) :
    IsQuasiExcellent R := by
  sorry
