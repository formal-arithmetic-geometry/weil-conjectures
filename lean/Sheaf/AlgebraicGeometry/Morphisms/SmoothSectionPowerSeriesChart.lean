/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.RingHom.Flat

/-!
# Completion of a smooth section and its closed-fibre generic point

Source: Stacks Project, Tag 0EYB, completion and the image of the extended maximal ideal;
Tags 05D5 and 00MB.
(blueprint: lem-sbc-smooth-section-power-series-chart)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Completing a smooth chart along a section produces a flat power-series chart. Its
extended maximal ideal maps to a point generic on a nonempty open of the original fibre.
The number of variables is allowed to be zero.

Source: Stacks Project, Tag 0EYB, the completion paragraph; Tags 05D5 and 00MB.
(blueprint: lem-sbc-smooth-section-power-series-chart)

Proof: Base change q along Spec φ; the morphism s gives a section of that smooth scheme.
Choose an affine chart containing its value at the closed point of B. Its inverse image
under the section is an open neighbourhood of the closed point of the local spectrum,
so is all of Spec B. Thus the affine chart algebra has an augmentation to B. Its
conormal module is finite projective, hence free over the local ring B. Tag 05D5
identifies completion along the augmentation ideal with B[[X_1,...,X_n]]. The chart
algebra is Noetherian, so completion is flat by 00MB. Compose with the affine chart
inclusion and the flat base-change projection to get t. The augmentation gives the
stated origin equality and the B-algebra structure gives the commuting square.
The ideal m_B B[[X]] is prime, since the quotient is the power-series domain over κ(B).
Its point is generic in the completed closed fibre. Flatness of fibre completion and
field base change maps it to a generic point η of an irreducible component of the
original smooth fibre. That fibre is locally Noetherian, so this component has a
nonempty open W avoiding the other components. Every point of W specializes from η.
This argument includes n = 0 and assumes neither a dense open nor a depth bound. -/
theorem exists_smooth_section_power_series_chart
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {L : Scheme.{u}} (q : L ⟶ Spec (.of A)) [Smooth q]
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (φ : A →+* B) [IsLocalHom φ] (hflat : φ.Flat)
    (s : Spec (.of B) ⟶ L) (hs : s ≫ q = Spec.map (CommRingCat.ofHom φ)) :
    ∃ (n : ℕ) (t : Spec (.of (MvPowerSeries (Fin n) B)) ⟶ L), Flat t ∧
      t ≫ q = Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n))) ≫
        Spec.map (CommRingCat.ofHom φ) ∧
      t ((Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin n))))
        (IsLocalRing.closedPoint B)) = s (IsLocalRing.closedPoint B) ∧
      ∃ (v : Spec (.of (MvPowerSeries (Fin n) B)))
        (η : q.fiber (IsLocalRing.closedPoint A))
        (W : (q.fiber (IsLocalRing.closedPoint A)).Opens),
        v.asIdeal = (IsLocalRing.maximalIdeal B).map (MvPowerSeries.C (σ := Fin n)) ∧
        t v = q.fiberι (IsLocalRing.closedPoint A) η ∧
        (W : Set (q.fiber (IsLocalRing.closedPoint A))).Nonempty ∧ ∀ z ∈ W, η ⤳ z := by sorry

end AlgebraicGeometry.Scheme
