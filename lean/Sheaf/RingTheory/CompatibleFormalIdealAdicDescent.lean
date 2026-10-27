/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q120
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Spectrum.Maximal.Defs
public import Sheaf.RingTheory.FormalLocalPresentation
public import WeilConjectures.RingTheory.CompletionAtQuasiFinitePrimeMap
import Mathlib.RingTheory.Lasker
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Finiteness.Ideal
import Mathlib.RingTheory.Localization.Submodule
import WeilConjectures.RingTheory.AdicCompletionNoetherian

/-!
# Adic descent of compatible formal ideals

Source: Rotthaus, Komplettierung semilokaler quasiausgezeichneter Ringe (1979),
Theorem 3, Claim 4 and equations (4.1)--(4.3), pp.178--179, extracted for a
compatible ideal without a singular-locus interpretation
(blueprint: lem-per-compatible-formal-ideal-adic-descent).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

namespace Algebra

/-- The canonical map of completed prime localizations. The chosen witness of
`exists_completion_map_atPrime` is specified on every quotient coordinate, hence
is unique as a ring map. This is a choice of the uniquely determined inverse-limit
map, not a choice of an unspecified homomorphism.
Source: Rotthaus (1979), diagram before (4.1), p.178; construction in Stacks Tag 07NC
(blueprint: lem-per-compatible-formal-ideal-adic-descent). -/
def completedLocalizationMap
    (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
    (q : PrimeSpectrum S) :
    LocalCompletion (Localization.AtPrime (q.comap (algebraMap R S)).asIdeal) →+*
      LocalCompletion (Localization.AtPrime q.asIdeal) :=
  Classical.choose (exists_completion_map_atPrime R S q)

/-- The contraction `a_n = (E + J^n C) ∩ B`, for the Jacobson-adic completion `C`.
The sum of ideals is their lattice supremum; extension and contraction are
Mathlib's `Ideal.map` and `Ideal.comap`.
Source: Rotthaus (1979), final paragraph of Claim 4, p.179
(blueprint: lem-per-compatible-formal-ideal-adic-descent). -/
def formalIdealAdicContraction (B : Type u) [CommRing B] (J : Ideal B)
    (E : Ideal (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B)) (n : ℕ) : Ideal B :=
  Ideal.comap (algebraMap B (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B))
    (E ⊔ (J ^ n).map (algebraMap B (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B)))

/-- Compatible formal ideals descend modulo every positive power of `J`.
The existential ideal in `hcompatible` is chosen once for each base prime `p`,
not separately for each prime `Q` over it. The equality `hp` only transports that
same ideal between definitionally indexed completed localization types.
Source: Rotthaus (1979), Theorem 3, Claim 4 and (4.1)--(4.3), pp.178--179
(blueprint: lem-per-compatible-formal-ideal-adic-descent).

Proof:
1. Completion is Noetherian (lem-weil-pbc-adic-completion-noetherian) and faithfully
   flat (lem-per-jacobson-adic-completion-faithfully-flat). Finite quotients agree
   (lem-weil-pbc-adic-completion-mod-power). The geometric series in the inverse
   limit proves that every maximal ideal of C contains the extended Jacobson
   radical. Consequently nonmaximal primes of C contract to nonmaximal primes of B.
2. Fix n >= 1 and decompose K = E + J^n C into finitely many primary ideals Q_i
   (lem-per-noetherian-primary-decomposition). Their contractions q_i are primary,
   with radicals p_i; every radical contains JC. Include the empty decomposition K=C.
3. If the radical P_i is maximal, a power of the Jacobson radical lies in Q_i
   (lem-weil-pbc-fg-ideal-radical-power). Finite-quotient comparison gives Q_i=q_i C.
4. Otherwise localize and complete at P_i. Primaryness and faithfully flat
   contraction show Q_i T intersects C in Q_i. Its radical is the maximal ideal of T.
   Use lem-weil-pbc-localization-noetherian, lem-weil-pbc-adic-completion-noetherian,
   lem-weil-pbc-local-completion-local-ring, lem-weil-pbc-local-completion-faithfully-flat,
   lem-weil-pbc-faithfully-flat-ideal-contraction and the radical-power bound.
5. Contract Q_i T to U, obtaining A with radical p_i U. Its contraction to B_{p_i}
   is q_i B_{p_i}. A contains a maximal-ideal power, so finite-quotient comparison
   gives A=q_i U (lem-weil-pbc-local-completion-local-ring,
   lem-weil-pbc-fg-ideal-radical-power, lem-weil-pbc-adic-completion-mod-power).
6. Compatibility at P_i yields e_{p_i}+J^n U contained in q_i U. Extend this inclusion
   at every other prime over p_i using the SAME e_{p_i}. Faithfully flat contraction
   from each completed localization gives K C_{P'} contained in q_i C_{P'}
   (lem-weil-pbc-local-completion-faithfully-flat,
   lem-weil-pbc-faithfully-flat-ideal-contraction).
7. Flat-primary fibre recovery gives K contained in q_i C
   (lem-per-flat-primary-fibre-recovery). The retained radicality and faithful
   flatness hypotheses on the completed comparison maps are not needed by this
   whole-fibre version of the argument, but are kept in the statement.
8. Contraction preserves intersections, and flat extension preserves finite
   intersections (lem-per-flat-ideal-finite-intersection). Therefore
   a_n C = intersection(q_i C) = K, also for the empty decomposition.
9. Extension of a_{n+1}+J^n equals E+J^{n+1}C+J^n C = a_n C. Contract by faithful
   flatness to get a_{n+1}+J^n=a_n (lem-weil-pbc-faithfully-flat-ideal-contraction).
No J-adic completeness, nonzero E, or singular-locus condition is used. -/
theorem compatible_formal_ideal_adic_descent
    (B : Type u) [CommRing B] [IsNoetherianRing B] [Finite (MaximalSpectrum B)]
    (J : Ideal B) (hJ : J ≤ Ideal.jacobson (⊥ : Ideal B))
    (E : Ideal (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B))
    (hflat : ∀ Q : PrimeSpectrum (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B),
      ¬ Q.asIdeal.IsMaximal →
      J.map (algebraMap B (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B)) ≤ Q.asIdeal →
      RingHom.FaithfullyFlat
        (completedLocalizationMap B (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B) Q))
    (hradical : ∀ p : PrimeSpectrum B, J ≤ p.asIdeal →
      (p.asIdeal.map
        (algebraMap B (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B))).IsRadical)
    (hcompatible : ∀ p : PrimeSpectrum B, J ≤ p.asIdeal →
      ∃ e : Ideal (LocalCompletion (Localization.AtPrime p.asIdeal)),
        ∀ (Q : PrimeSpectrum (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B)),
          ¬ Q.asIdeal.IsMaximal →
          J.map (algebraMap B (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B)) ≤ Q.asIdeal →
          ∀ hp : p = Q.comap (algebraMap B (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B)),
            E.map (algebraMap (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B)
              (LocalCompletion (Localization.AtPrime Q.asIdeal))) =
            Ideal.map
              (completedLocalizationMap B (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B) Q)
              (hp ▸ e)) :
    ∀ n : ℕ, 1 ≤ n →
      (formalIdealAdicContraction B J E n).map
          (algebraMap B (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B)) =
        E ⊔ (J ^ n).map (algebraMap B (AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B)) ∧
      formalIdealAdicContraction B J E (n + 1) ⊔ J ^ n =
        formalIdealAdicContraction B J E n := by
  sorry

end Algebra
