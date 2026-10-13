/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W4
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.RingTheory.Depth
/-!
# Descent of the finite depth-two power-series extension as a finite scheme

Source: Stacks Project, Tag 0EYA, identification C = C0 tensor B; Tags 0EY9 and 0EY6.
(blueprint: lem-sbc-power-series-depth-two-base-change)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A finite depth-two extension on a proper power-series open comes by base change
from a finite scheme over the coefficient ring. No etaleness of that scheme is asserted.

Source: Stacks Project, Tag 0EYA, construction of the isomorphism Psi; 0EY6(2),(a),(b).
(blueprint: lem-sbc-power-series-depth-two-base-change)

Proof: Let U be the punctured spectrum of B, and R its power-series ring.
The zero section intersects V in U: haway includes U, and a proper open of
Spec R cannot contain its closed point. Restrict p to this zero section and
extend that finite etale U-scheme by the canonical depth-two construction
0EY6. Write Y for the finite B-scheme obtained. Over the inverse image of U,
0EY9 identifies p with the pullback of Y: both restrict to the same cover of
U along the zero section. By flat base change 0EY6(a) and change of opens
0EY6(b), the canonical extension of this restriction is the base change of Y.
The supplied p is itself the canonical extension, by its finite and boundary
depth conditions and uniqueness 0EY6(2). The resulting isomorphism with the
base change gives a projection a and the asserted cartesian square. The empty
cover yields Y empty. Etaleness of Y and any point over the closed point of B
are not used in this identification. -/
theorem exists_finite_base_of_power_series_depth_two
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := B) B)
    (n : ℕ) (hn : 0 < n)
    (V : (Spec (.of (MvPowerSeries (Fin n) B))).Opens) (hproper : V ≠ ⊤)
    (haway : ∀ v, (Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n)))) v ≠
      IsLocalRing.closedPoint B → v ∈ V)
    {E : Scheme.{u}} (p : E ⟶ Spec (.of (MvPowerSeries (Fin n) B)))
    [IsFinite p] [Etale (p ∣_ V)]
    (hboundary : ∀ z : E, p z ∉ V →
      (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z)) :
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of B)) (a : E ⟶ Y),
      IsFinite g ∧ IsPullback a p g
        (Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n)))) := by sorry

end AlgebraicGeometry.Scheme
