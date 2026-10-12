/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T2
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.Mathlib.RingTheory.Henselian
import Sheaf.AlgebraicGeometry.ZariskiCohomologyLocallyZero
import Sheaf.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Sheaf.Paper.StrictHenselianZariskiEtaleComparison

/-! # GabberPrincipalClassLocallyZero

Source: Stacks Project, Tag 0GY0.
(blueprint: lem-weil-pbc-gabber-principal-class-locally-zero) -/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- Local comparison makes every positive-degree class locally zero on principal opens.

Source: Stacks Project, Etale Cohomology, Lemma 0GY0, label lemma-gabber-criterion,
proof's local triviality paragraph; Lemma 09AX and Cohomology on Sites Lemma 01FW.
(blueprint: lem-weil-pbc-gabber-principal-class-locally-zero)

Proof: identify the local rings on D(h) with the prime localizations of R. They
are strictly henselian by hR, so 09AX compares etale and Zariski cohomology on
D(h) and its open subschemes. A positive-degree Zariski class vanishes near each
point by 01FW. The principal opens D(fh) form a basis of D(h), so choose one
containing the prime p within this vanishing neighborhood. Then f is outside p.
Naturality of comparison identifies zero restrictions with the displayed map.
This works also for h = 0: there are no primes avoiding h. -/
theorem gabber_principal_class_locally_zero
    (R : Type u) [CommRing R]
    (hR : ∀ (p : Ideal R) [p.IsPrime],
      IsStrictlyHenselianLocalRing (Localization.AtPrime p))
    (F : Sheaf (Spec (CommRingCat.of R)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (hq : 0 < q)
    (h : R) (ξ : Sheaf.H
      (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
      (PrimeSpectrum.basicOpen h))^*[AddCommGrpCat.{u + 1}]).obj F) q) :
    ∀ (p : Ideal R) [p.IsPrime], h ∉ p →
      ∃ f : R, (cohomologyMap
      (Scheme.homOfLE (X := Spec (CommRingCat.of R))
        (PrimeSpectrum.basicOpen_mul_le_right f h))
      (((Scheme.Opens.ι (X := Spec (CommRingCat.of R))
      (PrimeSpectrum.basicOpen h))^*[AddCommGrpCat.{u + 1}]).obj F) q ξ) = 0 ∧ f ∉ p := by
  sorry

end AlgebraicGeometry.Etale
