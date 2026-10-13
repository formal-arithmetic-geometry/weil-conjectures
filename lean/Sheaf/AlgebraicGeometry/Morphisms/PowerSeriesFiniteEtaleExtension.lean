/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C4
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.RingTheory.Depth

/-!
# Extending finite etale covers of a power-series open

Source: Stacks Project, Tag 0EYA, with the boundary depth calculation of Tag 0337.
(blueprint: lem-sbc-power-series-finite-etale-extension)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A finite etale cover of the indicated power-series open extends to a finite
etale cover, with depth at least two above the complement.

Source: Stacks Project, Tag 0EYA; Tag 0EY6(1),(2),(a),(b); Tag 0337.
(blueprint: lem-sbc-power-series-finite-etale-extension)

Proof: Write T = Spec R, where R = B[[X_1,...,X_n]]. If v is outside V, its
contraction is the maximal ideal of B. Thus B -> R_v is flat and local, and
0337 gives depth at least two. By 0EY6 the cover f has a canonical finite
extension E, whose stalks over T minus V have depth at least two. It remains
to show that this extension is etale; this is the essential-surjectivity
assertion of 0EYA. Here is its argument. Let U be the punctured spectrum of B,
and let W0 be f pulled back to the zero section over U. Its canonical finite
extension has ring C0. Full faithfulness in 0EY9 on U times Spec B[[X]]
identifies f there with the pullback of W0. Flat-base-change compatibility
and invariance under enlarging the open in 0EY6 identify the ring of E with
C0 tensor_B R. At q = m_B R, which belongs to V, this algebra is etale after
localization at q. The map B -> R_q is faithfully flat: it is flat and local,
with contraction of q equal to m_B. Etaleness descends along this map, so
C0 is etale over B. Its base change, and hence E -> T, is finite etale.
The boundary depth is the depth assertion of the canonical extension in
0EY6(2), already obtained before proving etaleness. If V is all of T take
the given cover. The empty cover gives the empty extension; its depth
assertion is vacuous. No arbitrary choice is used to define an object. -/
theorem exists_finite_etale_extension_of_power_series_open
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := B) B)
    (n : ℕ) (hn : 0 < n)
    (V : (Spec (.of (MvPowerSeries (Fin n) B))).Opens)
    (haway : ∀ v, (Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n)))) v ≠
      IsLocalRing.closedPoint B → v ∈ V)
    (hgeneric : ∃ v, v ∈ V ∧ v.asIdeal =
      (IsLocalRing.maximalIdeal B).map (MvPowerSeries.C (σ := Fin n)))
    {X : Scheme.{u}} (f : X ⟶ V.toScheme) [IsFinite f] [Etale f] :
    ∃ (E : Scheme.{u}) (p : E ⟶ Spec (.of (MvPowerSeries (Fin n) B))),
      IsFinite p ∧ Etale p ∧
      (∀ z : E, p z ∉ V →
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := E.presheaf.stalk z) (E.presheaf.stalk z)) ∧
      ∃ e : (p ⁻¹ᵁ V).toScheme ≅ X, e.hom ≫ f = p ∣_ V := by sorry

end AlgebraicGeometry.Scheme
