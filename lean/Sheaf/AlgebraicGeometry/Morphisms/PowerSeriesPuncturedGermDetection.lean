/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G2
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.RingTheory.Depth
import Sheaf.RingTheory.MvPowerSeriesFlat
import Sheaf.RingTheory.AnnihilatorAssociatedPrimesFlatBaseChange
import Sheaf.RingTheory.DepthLeDimAssociatedPrime
import Sheaf.RingTheory.InjectivePiLocalizationAssociatedPrimes

/-!
# Detecting sections at the punctured zero section

Source: Stacks Project, Tag 0EY9, injectivity detail, expanded by Tags 0312 and 0311.
(blueprint: lem-sbc-power-series-punctured-germ-detection)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A section on V vanishing as a germ at every point of the punctured zero
section is zero.

Source: Stacks Project, Tag 0EY9, the omitted injectivity detail; Tags 0312,
0BK4 and 0311. (blueprint: lem-sbc-power-series-punctured-germ-detection)

Proof: The constants map A to B is flat. Flat base change of associated primes
says that every associated prime of B is pB for p associated to A: the quotient
by pB is the power-series ring over the domain A/p, and hence is a domain.
The depth bound by dim(A/p) excludes p equal to the maximal ideal. The prime
pB specializes to pB+I, whose zero-section point lies in V by hV. Thus pB is
in V too. A zero germ at pB+I maps to a zero germ at pB under the specialization
map of stalks. All associated germs of s on V therefore vanish. Cover V by
affine opens. Localization of associated primes identifies the associated
points in each such open with the associated points of B lying there.
The injection of a module into the product of its localizations at associated
primes makes the section on each affine open zero. Sheaf separatedness gives
s = 0. This argument allows nilpotents and does not use formal approximation. -/
theorem eq_zero_of_powerSeries_punctured_germs
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin d)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A)
    (s : Γ(V.toScheme, ⊤))
    (hs : ∀ x :
      ((Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))) ⁻¹ᵁ V).toScheme,
      (V.toScheme.presheaf.Γgerm
        ((Spec.map (CommRingCat.ofHom
          (MvPowerSeries.constantCoeff (σ := Fin d) (R := A))) ∣_ V) x)).hom s = 0) :
    s = 0 := by sorry

end AlgebraicGeometry.Scheme
