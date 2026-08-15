/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.Ring.Constructions

/-!
# Quotients by extended ideals are pushouts

For an ideal `K` of `R` and a ring map `φ : R ⟶ S`, the square formed by the quotient
maps `R ⟶ R ⧸ K`, `S ⟶ S ⧸ K·S` and the induced map `R ⧸ K ⟶ S ⧸ K·S` is a pushout in
`CommRingCat`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace CommRingCat

/-- Quotients by extended ideals are pushouts in `CommRingCat`. -/
lemma isPushout_quotient {R S : CommRingCat.{u}} (φ : R ⟶ S) (K : Ideal R) :
    IsPushout (CommRingCat.ofHom (Ideal.Quotient.mk K)) φ
      (CommRingCat.ofHom (Ideal.quotientMap (K.map φ.hom) φ.hom Ideal.le_comap_map))
      (CommRingCat.ofHom (Ideal.Quotient.mk (K.map φ.hom))) := by
  have w : CommRingCat.ofHom (Ideal.Quotient.mk K) ≫
      CommRingCat.ofHom (Ideal.quotientMap (K.map φ.hom) φ.hom Ideal.le_comap_map) =
      φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk (K.map φ.hom)) := by
    rw [← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk, CommRingCat.ofHom_comp,
      CommRingCat.ofHom_hom]
  have hkill : ∀ s : Limits.PushoutCocone (CommRingCat.ofHom (Ideal.Quotient.mk K)) φ,
      ∀ a ∈ K.map φ.hom, s.inr.hom a = 0 := by
    intro s a ha
    have hle : K.map φ.hom ≤ RingHom.ker s.inr.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro k hk
      have hc := congrArg (fun t ↦ CommRingCat.Hom.hom t k) s.condition
      simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hc
      rw [Ideal.mem_comap, RingHom.mem_ker, ← hc, Ideal.Quotient.eq_zero_iff_mem.mpr hk,
        map_zero]
    exact RingHom.mem_ker.mp (hle ha)
  refine IsPushout.of_isColimit' ⟨w⟩ (Limits.PushoutCocone.IsColimit.mk _
    (fun s ↦ CommRingCat.ofHom (Ideal.Quotient.lift (K.map φ.hom) s.inr.hom (hkill s)))
    (fun s ↦ ?_) (fun s ↦ ?_) (fun s m hl hr ↦ ?_))
  · ext x
    have hc := congrArg (fun t ↦ CommRingCat.Hom.hom t x) s.condition
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hc
    simp [Ideal.quotientMap_mk, Ideal.Quotient.lift_mk, ← hc]
  · ext x
    simp [Ideal.Quotient.lift_mk]
  · ext x
    have hc := congrArg (fun t ↦ CommRingCat.Hom.hom t x) hr
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at hc
    simp [Ideal.Quotient.lift_mk, ← hc]

end CommRingCat
