/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q77
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.RingTheory.GRing
public import WeilConjectures.RingTheory.CompletionMapForLocalHom
import Mathlib.GroupTheory.MonoidLocalization.Away
import Mathlib.RingTheory.AdicCompletion.Completeness
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Mathlib.Algebra.Category.Ring.FinitePresentation
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.AlgebraicGeometry.OpenImmersion
import WeilConjectures.RingTheory.GRingCompletionRegular
import Sheaf.RingTheory.PopescuSmoothing
import Sheaf.Paper.SmoothSectionEtaleLift
import WeilConjectures.RingTheory.PrimeLocalizationEtaleAlgebraModel

/-!
# Artin approximation by an étale local algebra

Source: Stacks Project, `smoothing.tex`, Tag 0CAR, lemma-approximation-property-variant
(blueprint: lem-trf-artin-approximation-etale-local-map).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warn.sorry false

@[expose] public noncomputable section

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/--
Let `A` be Noetherian, `p` a prime ideal, and `f` a finite family of polynomials over `A`.
A solution in the completion of `A` localized at `p` can be approximated to every positive
adic order by a solution in an étale `A`-algebra with the same residue field at a prime over
`p`.  The completion map and the congruence are expressed using the canonical local-map
construction of `RingHom.exists_adicCompletion_map_of_local`.
Source: Stacks Project, `smoothing.tex`, Tag 0CAR, lemma-approximation-property-variant.
Proof:
1. Put `R = A_p` and `H` equal to its maximal-ideal completion. Localization and
   completion preserve Noetherianity. Completion regularity for a G-ring and Popescu
   smoothing express `H` as a filtered colimit of smooth `R`-algebras
   (`lem-weil-pbc-localization-noetherian`, `lem-weil-pbc-adic-completion-noetherian`,
   `lem-weil-pbc-g-ring-completion-regular`, `lem-weil-pbc-popescu-smoothing`).
2. The given solution gives a map from the finitely presented polynomial quotient to `H`.
   Factor it through a smooth stage `B`, obtaining elements `z_i` satisfying every equation
   and mapping to `a_i` (`lem-weil-pbc-finite-presentation-algebra-factors-filtered-colimit`).
3. Reduce `B → H` modulo the N-th maximal-ideal power. Smooth section lifting gives an
   étale `R`-algebra `E`, the same quotient modulo that power, and a map `B → E` with
   solutions `c_i` agreeing with `a_i` modulo that power
   (`lem-weil-pbc-adic-completion-mod-power`, `lem-weil-pbc-smooth-section-etale-lift`).
4. The maximal ideal of `R` extends to a maximal ideal `q` of `E` with unchanged residue
   field. In `T = E_q`, coordinate compatibility of the local completion map and the
   completion kernel formula give the required congruence for `c_i`
   (`lem-weil-pbc-fs-adic-completion-map-local`, `lem-weil-pbc-adic-completion-mod-power`).
5. Descend `E` to an étale `A`-algebra `C` with `E` a localization of `C`, using
   `new-lem-sbc-prime-localization-etale-algebra-model`.
6. Clear the finitely many denominators of `c_i` and then those killing the finitely many
   equation errors. A principal localization `A' = C_h` has actual solutions `b_i`.
7. Principal localization is an open immersion, hence étale, and étale maps compose
   (`lem-weil-pbc-principal-localization-open-immersion`,
   `lem-weil-pbc-etale-composition-cancellation`).
8. Contract `q` to `p'` in `A'`. Both `A'_{p'}` and `E_q` identify with the localization
   of `C` at the contracted prime. These identifications preserve residue fields,
   completion coordinates, and solutions, giving the stated congruence.
(blueprint: lem-trf-artin-approximation-etale-local-map)
-/
theorem artin_approximation_etale_local_map
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (p : Ideal A) [hp : p.IsPrime]
    (m n : ℕ) (f : Fin m → MvPolynomial (Fin n) A)
    (a : Fin n →
      AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
        (Localization.AtPrime p))
    (ha : ∀ j : Fin m, MvPolynomial.aeval a (f j) = 0)
    (hG : IsGRing (Localization.AtPrime p)) :
    ∀ N : ℕ, 1 ≤ N →
      ∃ (A' : CommAlgCat.{u} A),
        Etale (Spec.map (CommRingCat.ofHom (algebraMap A A'))) ∧
        ∃ (p' : PrimeSpectrum A')
          (hcomp : p = p'.asIdeal.comap (algebraMap A A')),
          ∃ (b : Fin n → A'),
            (∀ j : Fin m, MvPolynomial.aeval b (f j) = 0) ∧
              Function.Bijective
                (IsLocalRing.ResidueField.map
                  (Localization.localRingHom p p'.asIdeal (algebraMap A A') hcomp)) ∧
              (∀ i : Fin n,
                Classical.choose (RingHom.exists_adicCompletion_map_of_local
                    (Localization.localRingHom p p'.asIdeal (algebraMap A A') hcomp)) (a i) -
                    AdicCompletion.of (IsLocalRing.maximalIdeal (Localization.AtPrime p'.asIdeal))
                      (Localization.AtPrime p'.asIdeal)
                      (algebraMap A' (Localization.AtPrime p'.asIdeal) (b i)) ∈
                  Ideal.map
                    (algebraMap (Localization.AtPrime p'.asIdeal)
                      (AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p'.asIdeal))
                        (Localization.AtPrime p'.asIdeal)))
                    ((IsLocalRing.maximalIdeal (Localization.AtPrime p'.asIdeal)) ^ N)) := by
  sorry

end AlgebraicGeometry
