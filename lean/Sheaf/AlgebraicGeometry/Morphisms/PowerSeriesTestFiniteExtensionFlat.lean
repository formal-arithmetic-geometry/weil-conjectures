/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U3
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.RingTheory.Depth

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.MvPowerSeries.Equiv
import Sheaf.AlgebraicGeometry.Morphisms.PowerSeriesFiniteEtaleExtension
import Sheaf.AlgebraicGeometry.Morphisms.DepthTwoFiniteExtensionUniqueness

/-!
# Flatness of a finite depth-two extension on a power-series spectrum

Source: Stacks Project, Tag 0EYA and the last completion step of Tag 0EYB.
(blueprint: lem-sbc-power-series-test-finite-extension-flat)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A finite depth-two extension on a power-series spectrum is flat.

Source: Stacks Project, Tag 0EYA; Tag 0EY6(2),(a),(b); Tag 0337.
(blueprint: lem-sbc-power-series-test-finite-extension-flat)

Proof: Put T = Spec B[[X_1,...,X_n]]. At every point of T outside V the map from
B is flat and local. The flat local depth formula (0337) gives depth at least two
on T there. The two assumptions on V are exactly those of 0EYA: V contains all primes
not over the maximal ideal of B and the prime extended from that maximal ideal.
That lemma extends r restricted to V to a finite etale scheme over T. Uniqueness of
the finite depth-two extension (0EY6(2)) identifies this etale extension with F:
both restrict to the same cover and have depth at least two at boundary points.
For the etale extension this depth bound follows again from the flat local depth
formula. Thus r is etale, hence flat.
This calculation does not use smoothness, a closed fibre point, or a section.
If the cover is empty so is F; if V is all of T no extension is needed. -/
theorem flat_of_power_series_depth_two_finite_extension
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := B) B)
    (n : ℕ) (hn : 0 < n)
    (V : (Spec (.of (MvPowerSeries (Fin n) B))).Opens)
    {F : Scheme.{u}} (r : F ⟶ Spec (.of (MvPowerSeries (Fin n) B)))
    [IsFinite r] [Etale (r ∣_ V)]
    (hboundary : ∀ w : F, r w ∉ V →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := F.presheaf.stalk w) (F.presheaf.stalk w))
    (haway : ∀ v, (Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n)))) v ≠
      IsLocalRing.closedPoint B → v ∈ V)
    (hgeneric : ∃ v, v ∈ V ∧ v.asIdeal =
      (IsLocalRing.maximalIdeal B).map (MvPowerSeries.C (σ := Fin n))) :
    Flat r := by
  obtain ⟨E, p, hp, het, hE, e, he⟩ :=
    exists_finite_etale_extension_of_power_series_open B hdepth n hn V haway hgeneric (r ∣_ V)
  have : IsFinite p := hp
  have : Etale p := het
  obtain ⟨i, hi⟩ := iso_of_finite_depth_two_extensions V r p hboundary hE e he
  rw [← hi]
  infer_instance

end AlgebraicGeometry.Scheme
