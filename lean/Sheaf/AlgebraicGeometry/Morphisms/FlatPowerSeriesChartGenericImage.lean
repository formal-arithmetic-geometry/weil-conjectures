/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Generic image of the extended maximal ideal under a flat power-series chart

Source: Stacks Project, Tag 0EYB, the image of the extended maximal ideal.
(blueprint: lem-sbc-flat-power-series-chart-generic-image)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- The extended maximal ideal in a flat power-series chart maps to a generic point
of a component in an affine neighbourhood of the original closed fibre.

Source: Stacks Project, Tag 0EYB, the sentence about the image of the extended
maximal ideal, with flatness of completion supplied by Tag 00MB.
(blueprint: lem-sbc-flat-power-series-chart-generic-image)

Proof: Since B is Noetherian its maximal ideal is finitely generated. Coefficientwise
reduction modulo this ideal identifies B[[X]]/m_B B[[X]] with the power-series ring
over the residue field: lift coefficients for surjectivity, and use finite generators
of m_B to write a series whose coefficients lie in m_B as a finite sum of those
generators times series. This quotient is a domain, including when n = 0, so the
extended ideal defines a point v. Its contraction to B is m_B. Localness of the map
from A to B contracts m_B to m_A; the commuting square therefore puts the projection
of t(v) to L in its closed fibre and gives a point eta there. Restrict t to the closed fibre over B.
This is a flat map to the closed fibre of the base-changed smooth scheme, by base
change. That target identifies with the base change of the closed fibre of q to the
residue field of B. Projection from that base change is flat because the residue
field extension is flat. Thus the resulting map from Spec(kappa(B)[[X]]) to the original closed
fibre is flat. The zero ideal is its source's generic point. Going down for flat maps
implies that its image is a minimal prime in every affine neighbourhood containing
that image. Choose an affine neighbourhood V of eta and lift eta to x in V. Minimal
primality identifies the closure of {x} with an irreducible component of V.
No section or flatness of the original map A to B is needed for this argument.
Flatness is required over the base-changed scheme, not merely over L. -/
theorem exists_flat_power_series_chart_generic_image
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {L : Scheme.{u}} (q : L ⟶ Spec (.of A)) [Smooth q]
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (φ : A →+* B) [IsLocalHom φ]
    (n : ℕ) (t : Spec (.of (MvPowerSeries (Fin n) B)) ⟶
      Limits.pullback q (Spec.map (CommRingCat.ofHom φ))) [Flat t]
    (ht : t ≫ Limits.pullback.snd q (Spec.map (CommRingCat.ofHom φ)) =
      Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n)))) :
    ∃ (v : Spec (.of (MvPowerSeries (Fin n) B)))
      (V : (q.fiber (IsLocalRing.closedPoint A)).Opens) (_ : IsAffineOpen V) (x : V),
      v.asIdeal = (IsLocalRing.maximalIdeal B).map (MvPowerSeries.C (σ := Fin n)) ∧
      (t ≫ Limits.pullback.fst q (Spec.map (CommRingCat.ofHom φ))) v =
        q.fiberι (IsLocalRing.closedPoint A) (V.ι x) ∧
      closure ({x} : Set V) ∈ irreducibleComponents V := by sorry

end AlgebraicGeometry.Scheme
