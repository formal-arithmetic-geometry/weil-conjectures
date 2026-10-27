/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q57
-/
module

public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.AlgebraicGeometry.IsRegularScheme
public import WeilConjectures.RingTheory.NagataRing
public import WeilConjectures.RingTheory.GRing
public import Sheaf.AlgebraicGeometry.FormalCompletionGeometry
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.Jacobson.Ideal
public import Mathlib.RingTheory.Spectrum.Maximal.Basic

import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.KrullDimension.Zero
import Mathlib.RingTheory.Localization.Submodule
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Spectrum.Prime.Topology
import WeilConjectures.Mathlib.RingTheory.Flat.Equalizer
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import WeilConjectures.RingTheory.CompleteLocalGRing
import WeilConjectures.RingTheory.IsAnalyticallyUnramifiedOfIsNagataRing
import WeilConjectures.RingTheory.LocalizationPrimeResidueFieldIso
import WeilConjectures.RingTheory.LocalizationRegular
import WeilConjectures.RingTheory.NagataLocalization

/-! # Patching formal singular ideals

Source: Rotthaus (1979), proof of Theorem 3, Claims 1--3, pp.176--178
(blueprint: lem-per-formal-singular-ideal-patching).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

namespace FormalSingularPatching

/-- The Jacobson-adic completion in Rotthaus, Theorem 3, pp.176--178
(blueprint: lem-per-formal-singular-ideal-patching). -/
abbrev completion (B : Type u) [CommRing B] :=
  AdicCompletion (Ideal.jacobson (⊥ : Ideal B)) B

/-- Completed localization at a point, with its maximal-ideal filtration.
Source: Rotthaus, Theorem 3, pp.176--178
(blueprint: lem-per-formal-singular-ideal-patching). -/
abbrev completedLocalization (R : Type u) [CommRing R] (q : PrimeSpectrum R) :=
  AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal))
    (Localization.AtPrime q.asIdeal)

/-- The canonical map from the Jacobson completion to its completed localization.
Source: Rotthaus, Theorem 3, p.176, displayed diagram
(blueprint: lem-per-formal-singular-ideal-patching). -/
def beta (B : Type u) [CommRing B] (q : PrimeSpectrum (completion B)) :
    completion B →+* completedLocalization (completion B) q :=
  (algebraMap (Localization.AtPrime q.asIdeal) _).comp
    (algebraMap (completion B) (Localization.AtPrime q.asIdeal))

/-- Completion of the canonical local map at a prime and its contraction.
At each quotient level, apply the local map to representatives and assemble these
compatible maps with `AdicCompletion.liftRingHom`.
Source: Rotthaus, Theorem 3, p.176, displayed diagram; Stacks Project, Tag 07ED
(blueprint: lem-per-formal-singular-ideal-patching). -/
def alpha (B : Type u) [CommRing B] (q : PrimeSpectrum (completion B)) :
    completedLocalization B (PrimeSpectrum.comap (algebraMap B (completion B)) q) →+*
      completedLocalization (completion B) q := by
  let p := PrimeSpectrum.comap (algebraMap B (completion B)) q
  let A := Localization.AtPrime p.asIdeal
  let T := Localization.AtPrime q.asIdeal
  let φ : A →+* T :=
    Localization.localRingHom p.asIdeal q.asIdeal (algebraMap B (completion B)) rfl
  let mA := IsLocalRing.maximalIdeal A
  let mT := IsLocalRing.maximalIdeal T
  have hmap : mA.map φ ≤ mT :=
    Ideal.map_le_iff_le_comap.mpr (fun x hx => map_nonunit φ x hx)
  have hpow (n : ℕ) : (mA ^ n).map φ ≤ mT ^ n := by
    rw [Ideal.map_pow]
    exact pow_le_pow_left' hmap n
  let qmap (n : ℕ) : A ⧸ mA ^ n →+* T ⧸ mT ^ n :=
    Ideal.Quotient.lift (mA ^ n) ((Ideal.Quotient.mk (mT ^ n)).comp φ) (by
      intro x hx
      change Ideal.Quotient.mk (mT ^ n) (φ x) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      exact hpow n (Ideal.mem_map_of_mem φ hx))
  let f (n : ℕ) := (qmap n).comp (AdicCompletion.evalₐ mA n).toRingHom
  have hf {m n : ℕ} (hmn : m ≤ n) :
      (Ideal.Quotient.factorPow mT hmn).comp (f n) = f m := by
    ext x
    induction x using AdicCompletion.induction_on with
    | _ x =>
      simpa [f, qmap] using congrArg (qmap m) (AdicCompletion.Ideal.mk_eq_mk mA hmn x)
  exact AdicCompletion.liftRingHom mT f (fun hmn => hf hmn)

/-- The specified intersection of contracted extended absolute singular ideals.
Empty intersections are the unit ideal. Source: Rotthaus, Theorem 3, pp.176--177
(blueprint: lem-per-formal-singular-ideal-patching). -/
def patchedIdeal (B : Type u) [CommRing B] (J : Ideal B) : Ideal (completion B) :=
  ⨅ (q : PrimeSpectrum (completion B)) (_ : ¬ q.asIdeal.IsMaximal)
    (_ : J.map (algebraMap B (completion B)) ≤ q.asIdeal),
    Ideal.comap (beta B q)
      ((AlgebraicGeometry.absoluteSingularIdeal
        (completedLocalization B (PrimeSpectrum.comap (algebraMap B (completion B)) q))).map
          (alpha B q))

/-- Patching formal singular ideals under regular completed comparison maps.
Source: Rotthaus (1979), Theorem 3, Claims 1--3, pp.176--178
(blueprint: lem-per-formal-singular-ideal-patching).

Proof:
1. Localization and completion preserve Noetherianity. The semilocal completion product
   (lem-per-semilocal-jacobson-completion-product) writes C as a finite product of
   completed Nagata local domains. Nagata localization and analytic unramifiedness
   make each factor reduced; its residue field makes it nonzero. Thus C is reduced
   and nonzero (lem-weil-pbc-local-nagata-domain-analytically-unramified).
2. Complete-local J-2 (lem-per-complete-local-j2), completion modulo the ideal, and
   the local completion description give closed singular loci in every factor and U_p.
   Product-prime localization gives closed Sing(C). Complete-local G-ring regularity
   (lem-weil-pbc-complete-local-g-ring) also makes C_q to its completion regular.
3. Put I = s(C). The radical/zero-locus theorem identifies V(I) with Sing(C).
   Apply lem-per-regular-map-singular-ideal to localization, local completion and alpha.
   It gives s(U_p)T_q = I T_q. Faithfully flat ideal contraction identifies each
   contracted ideal defining D with the contraction of I C_q.
4. Noetherianity gives finitely many minimal primes P_a over I, with I their intersection
   (lem-sc-finite-minimal-primes-over-ideal and prime-contains-minimal-prime).
   Flat finite-intersection preservation (lem-per-flat-ideal-finite-intersection) and
   localization prime correspondence show that D is the intersection of those P_a
   lying in some eligible q. A factor outside q becomes the unit ideal. This argument
   uses only finite intersections before extending any ideal.
5. At each eligible q, exactly the same factors survive for D and I. Hence D T_q = I T_q
   = s(U_p)T_q; D is radical and contains I. Empty intersections give the unit ideal.
6. A minimal prime of the nonzero reduced C has field localization, hence is regular
   (lem-weil-pbc-minimal-prime-reduced-localization-field and field-regular-ring).
   It lies outside V(I), so I and D are nonzero. The zero prime, when prime, is minimal
   and regular. For singular P with P + JC contained in an eligible q, choose P_a over I
   inside P; this P_a occurs in D's intersection. Thus D is contained in P. -/
theorem formal_singular_ideal_patching
    (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B]
    [Finite (MaximalSpectrum B)] (hNagata : IsNagataRing B)
    (J : Ideal B) (hJ : J ≤ Ideal.jacobson (⊥ : Ideal B))
    (hRegular : ∀ q : PrimeSpectrum (completion B),
      ¬ q.asIdeal.IsMaximal → J.map (algebraMap B (completion B)) ≤ q.asIdeal →
        (alpha B q).IsRegular) :
    patchedIdeal B J ≠ ⊥ ∧ (patchedIdeal B J).IsRadical ∧
      (∀ q : PrimeSpectrum (completion B),
        ¬ q.asIdeal.IsMaximal → J.map (algebraMap B (completion B)) ≤ q.asIdeal →
          (patchedIdeal B J).map (beta B q) =
            (AlgebraicGeometry.absoluteSingularIdeal
              (completedLocalization B
                (PrimeSpectrum.comap (algebraMap B (completion B)) q))).map (alpha B q)) ∧
      (∀ p : PrimeSpectrum (completion B),
        ¬ IsRegularLocalRing (Localization.AtPrime p.asIdeal) →
          p.asIdeal ≠ ⊥ ∧
            ((∃ q : PrimeSpectrum (completion B), ¬ q.asIdeal.IsMaximal ∧
              p.asIdeal ⊔ J.map (algebraMap B (completion B)) ≤ q.asIdeal) →
                patchedIdeal B J ≤ p.asIdeal)) := by
  sorry

end FormalSingularPatching
