/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.MvPowerSeries.Basic

/-!
# Flat completion chart for a smooth section over a local base

Source: Stacks Project, Tags 0EYB, 05D5 and 00MB.
(blueprint: lem-sbc-smooth-section-completion-chart)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A smooth section over a Noetherian local ring has a flat power-series chart,
compatible with both its structure map and the entire section.

Source: Stacks Project, Tag 0EYB, the completion paragraph; Tags 05D5 and 00MB.
(blueprint: lem-sbc-smooth-section-completion-chart)

Proof: Choose an affine neighbourhood of the section's closed-point value. Its
inverse image under the section is an open containing the closed point of the
local spectrum, hence the whole spectrum. Factor the section through this affine
neighbourhood. Its algebra C is smooth over B and its augmentation C to B splits
the structure map. Put I equal to the augmentation kernel. By 05D5, I/I^2 is a
finite projective B-module, hence free over the local ring B. Choose a basis and
lifts in I. The resulting map from B[[X_1,...,X_n]] to the I-adic completion is an
isomorphism: modulo I^2 it is an isomorphism, formal smoothness lifts its inverse
successively modulo I^k, and passage to the inverse limit gives an inverse.
The chosen lifts lie in I, so evaluation at zero corresponds to the augmentation.
Since C is a finite type algebra over the Noetherian ring B it is Noetherian, and
its completion map is flat by 00MB. Compose its spectrum map with the affine open
immersion. The B-algebra structure proves the first equality, and compatibility
of the augmentation proves the second. For n = 0 the same argument has no basis
vectors and identifies the completion with B. -/
theorem exists_smooth_section_completion_chart
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of B)) [Smooth p]
    (s : Spec (.of B) ⟶ X) (hs : s ≫ p = 𝟙 _) :
    ∃ (n : ℕ) (t : Spec (.of (MvPowerSeries (Fin n) B)) ⟶ X), Flat t ∧
      t ≫ p = Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n))) ∧
      Spec.map (CommRingCat.ofHom (MvPowerSeries.constantCoeff (σ := Fin n))) ≫
        t = s := by sorry

end AlgebraicGeometry.Scheme
