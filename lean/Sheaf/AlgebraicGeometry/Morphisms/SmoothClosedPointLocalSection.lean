/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.RingHom.Flat
import Sheaf.AlgebraicGeometry.Morphisms.SmoothClosedPointFiniteFlatLift
import WeilConjectures.AlgebraicGeometry.Morphisms.Slicing

/-!
# A flat local base change carrying a prescribed smooth-fibre point

Source: Stacks Project, Tag 0EYB, residue extension and étale slice; Tags 07NE and 057G.
(blueprint: lem-sbc-smooth-closed-point-local-section)
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme

/-- A closed point in a smooth closed fibre is reached by a flat local base change whose
closed fibre has only one point.

Source: Stacks Project, Tag 0EYB, the two base changes before completion; Tags 07NE and 057G.
(blueprint: lem-sbc-smooth-closed-point-local-section)

Proof: The smooth fibre is locally of finite type over the residue field. A closed point
therefore has finite residue extension. Tag 07NE realizes this extension by a finite flat
local algebra A' over A. In the base-changed fibre choose the rational lift of x. Apply
Tag 057G to obtain an étale slice through this lift, then localize its affine coordinate
ring at the slice point to obtain B. The composite A -> B is flat and local. Both the
finite local extension and the localized étale extension have zero-dimensional closed
fibre; hence the sole prime over the maximal ideal of A is the maximal ideal of B.
The map from the local slice to the original smooth scheme is s. The residue lift and
the localization send its closed point to the image of x. No open subset or depth
hypothesis is involved. -/
theorem exists_smooth_closed_point_local_section
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {L : Scheme.{u}} (q : L ⟶ Spec (.of A)) [Smooth q]
    (x : q.fiber (IsLocalRing.closedPoint A)) (hx : IsClosed ({x} : Set _)) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsLocalRing B) (_ : IsNoetherianRing B),
      ∃ (φ : A →+* B), IsLocalHom φ ∧ φ.Flat ∧
        (∀ z, (Spec.map (CommRingCat.ofHom φ)) z = IsLocalRing.closedPoint A →
          z = IsLocalRing.closedPoint B) ∧
        ∃ (s : Spec (.of B) ⟶ L), s ≫ q = Spec.map (CommRingCat.ofHom φ) ∧
          s (IsLocalRing.closedPoint B) = q.fiberι (IsLocalRing.closedPoint A) x := by
  obtain ⟨A', hA', hlocalA', hnoethA', α, hαlocal, hαflat, hαfinite,
    y, hyx, hyclosed, hyetale⟩ := exists_smooth_closed_point_finite_flat_lift A q x hx
  let := hA'
  let := hlocalA'
  let := hnoethA'
  let := hαlocal
  let := hαfinite
  let a := Spec.map (CommRingCat.ofHom α)
  have : Flat a := Flat.SpecMap_iff.mpr hαflat
  let p := Limits.pullback.snd q a
  obtain ⟨Z, i, z, _, hetale, hiz⟩ :=
    Smooth.exists_etale_comp_of_etale_residueFieldMap p hyetale
  let h := i ≫ p
  have : Etale h := hetale
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian h
  let B : Type u := Z.presheaf.stalk z
  let t : Spec (.of B) ⟶ Spec (.of A) := Z.fromSpecStalk z ≫ h ≫ a
  obtain ⟨β, hβ⟩ := Spec.map_surjective t
  have hclosed : t (IsLocalRing.closedPoint B) = IsLocalRing.closedPoint A := by
    change a (p (i (Z.fromSpecStalk z (IsLocalRing.closedPoint B)))) = _
    rw [fromSpecStalk_closedPoint, hiz, hyclosed]
    exact Spec_closedPoint
  have hβlocal : IsLocalHom β.hom := by
    apply ((IsLocalRing.local_hom_TFAE β.hom).out 4 0).mp
    exact congrArg PrimeSpectrum.asIdeal (hβ ▸ hclosed)
  have hβflat : β.hom.Flat := by
    apply Flat.SpecMap_iff.mp
    rw [hβ]
    infer_instance
  have : LocallyQuasiFinite (Z.fromSpecStalk z ≫ h) :=
    Hom.quasiFiniteAt_iff.mp (h.quasiFiniteAt z)
  have : LocallyQuasiFinite t := inferInstance
  let s : Spec (.of B) ⟶ L := Z.fromSpecStalk z ≫ i ≫ Limits.pullback.fst q a
  refine ⟨B, inferInstance, inferInstance, inferInstance, β.hom, hβlocal, hβflat,
    ?_, s, ?_, ?_⟩
  · intro w hw
    have hw' : t w = t (IsLocalRing.closedPoint B) :=
      (hβ ▸ hw).trans hclosed.symm
    have : DiscreteTopology (t ⁻¹' {t (IsLocalRing.closedPoint B)}) :=
      (t.isDiscrete_preimage_singleton _).to_subtype
    have heq : (⟨w, hw'⟩ : t ⁻¹' {t (IsLocalRing.closedPoint B)}) =
        ⟨IsLocalRing.closedPoint B, rfl⟩ :=
      (Topology.IsInducing.subtypeVal.specializes_iff.mp
        (IsLocalRing.specializes_closedPoint w)).eq
    exact congrArg Subtype.val heq
  · change s ≫ q = Spec.map β
    rw [hβ]
    dsimp [s, t, h, p]
    simp only [Category.assoc, Limits.pullback.condition]
  · change Limits.pullback.fst q a (i (Z.fromSpecStalk z (IsLocalRing.closedPoint B))) = _
    rw [fromSpecStalk_closedPoint, hiz]
    exact hyx

end AlgebraicGeometry.Scheme
