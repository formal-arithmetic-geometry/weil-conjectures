/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J4
-/
module

public import Sheaf.AlgebraicGeometry.Morphisms.FiniteEtaleAdicSectionsTransfer
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.RingTheory.Depth
import Sheaf.AlgebraicGeometry.Morphisms.DepthTwoHartogsRestriction

/-! Categorical form of the finite thickening restriction comparison.

Source: Stacks Project, Tag 0EY9.
(blueprint: lem-sbc-power-series-punctured-thickening-restriction-iso)
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- The canonical map from a finite power-series thickening to its punctured
restriction is an isomorphism.

Proof: The finite monomial basis identifies the quotient thickening sections
with the quotient ring by depth-two Hartogs; this identification is canonical.
(source: Stacks Project, Tag 0EY9;
(blueprint: lem-sbc-power-series-punctured-thickening-restriction-iso)
-/
theorem isIso_powerSeries_punctured_thickening_restriction
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := A) A)
    (d : ℕ) (hd : 0 < d)
    (V : (Spec (.of (MvPowerSeries (Fin d) A))).Opens)
    (hV : ∀ x : Spec (.of A),
      (Spec.map (CommRingCat.ofHom
        (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)))) x ∈ V ↔
        x ≠ IsLocalRing.closedPoint A)
    (n : ℕ) :
    IsIso
      ((ΓSpecIso (.of (MvPowerSeries (Fin d) A ⧸ FiniteEtale.Adic.ideal
        (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) n))).inv ≫
        (pullback.snd V.ι (FiniteEtale.Adic.baseMap
          (MvPowerSeries.constantCoeff (σ := Fin d) (R := A)) n)).appTop) := by
  sorry

end AlgebraicGeometry.Scheme
