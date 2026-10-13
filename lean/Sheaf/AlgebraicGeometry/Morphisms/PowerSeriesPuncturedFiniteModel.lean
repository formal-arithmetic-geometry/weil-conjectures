/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A4
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.MvPowerSeries.Basic
public import Sheaf.RingTheory.Depth

/-!
# A coefficient model on the punctured power-series base

Source: Stacks Project, Tag 0EYA, the construction preceding Psi; Tags 0EY9 and 0EY6.
(blueprint: lem-sbc-power-series-punctured-finite-model)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- Over the inverse image of the punctured coefficient spectrum, a finite etale
power-series cover has a finite coefficient model of depth two at the closed fibre.
No comparison on the whole power-series spectrum is asserted.

Source: Stacks Project, Tag 0EYA, paragraphs defining W0 and C0 and their comparison
on U times_X Y; Tags 0EY9 and 0EY6(1),(2).
(blueprint: lem-sbc-power-series-punctured-finite-model)

Proof: Put U = Spec B minus its closed point and t = Spec C. The zero section
s = Spec constantCoeff has inverse image of V equal to U: the inclusion follows
from haway and t composed with s = id, while the closed point maps to the closed
point of the local power-series spectrum, which a proper open cannot contain.
Pull the finite etale cover p restricted to V back along s restricted to U,
obtaining W0 -> U. Extend W0 by the finite depth-two extension theorem 0EY6,
applied to U in Spec B. Its boundary consists of the closed point, whose stalk
is B and has depth at least two. This gives g : Y -> Spec B finite, with the
asserted source-stalk depth bound and an isomorphism over U. Both p restricted
to t inverse U and the pullback of W0 are finite etale there, and have the same
restriction to the zero section U. Full faithfulness 0EY9 on t inverse U lifts
this isomorphism and its inverse; faithfulness gives the inverse identities.
For completeness, the fully faithful argument computes sections on the punctured
zero section of the truncated polynomial rings as B[X]/I^k, by depth-two Hartogs;
the inverse limit is the power-series ring. The constants map is flat by the
polynomial-adic completion equivalence and flatness of Noetherian completion.
At every point outside W the flat local depth formula gives depth at least two
from depth B. Hartogs applied to the structure sheaf therefore identifies sections
of W with the power-series ring. Thus W is quasi-affine and its global sections
agree with the inverse limit of sections of its formal thickenings. Finite
locally free modules embed in finite free modules with locally free cokernel;
repeat for the cokernel and compare the resulting kernels before and after
completion. This proves the sections comparison for finite locally free modules,
and then for their Hom modules. Finite etale covers lift uniquely through the
nilpotent thickenings of the zero section; the module comparison lifts their
formal algebra maps, and faithfulness on tensor products detects multiplication
and unit identities. This is Tags 0EKP and 0EL8 as used in 0EY9. Compose with the
pullback of the extension isomorphism over U. This gives e and its equation over W.
For the empty cover use the empty finite scheme;
no point over the closed coefficient point is needed. -/
theorem exists_power_series_punctured_finite_model
    (B : Type u) [CommRing B] [IsLocalRing B] [IsNoetherianRing B]
    (hdepth : (2 : ℕ∞) ≤ IsLocalRing.depth (R := B) B)
    (n : ℕ) (hn : 0 < n)
    (V : (Spec (.of (MvPowerSeries (Fin n) B))).Opens) (hproper : V ≠ ⊤)
    (haway : ∀ v, (Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n)))) v ≠
      IsLocalRing.closedPoint B → v ∈ V)
    {E : Scheme.{u}} (p : E ⟶ Spec (.of (MvPowerSeries (Fin n) B)))
    [IsFinite p] [Etale (p ∣_ V)]
    (U : (Spec (.of B)).Opens)
    (hU : ∀ x, x ∈ U ↔ x ≠ IsLocalRing.closedPoint B) :
    let t := Spec.map (CommRingCat.ofHom (MvPowerSeries.C (σ := Fin n) (R := B)))
    let W := t ⁻¹ᵁ U
    ∃ (Y : Scheme.{u}) (g : Y ⟶ Spec (.of B)), IsFinite g ∧
      (∀ z : Y, g z ∉ U →
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := Y.presheaf.stalk z) (Y.presheaf.stalk z)) ∧
      ∃ e : (p ⁻¹ᵁ W).toScheme ≅ ((Limits.pullback.snd g t) ⁻¹ᵁ W).toScheme,
        e.hom ≫ (Limits.pullback.snd g t) ∣_ W = p ∣_ W := by sorry

end AlgebraicGeometry.Scheme
