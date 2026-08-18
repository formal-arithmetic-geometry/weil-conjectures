/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import WeilConjectures.Mathlib.Algebra.Category.Ring.Basic
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Complements on pullback and pushforward of ideal sheaves

Three groups of complements to `Mathlib.AlgebraicGeometry.IdealSheaf.Functorial`.

The first computes the pullback of an ideal sheaf along the inclusion of its own closed
subscheme, which vanishes; as a consequence a morphism is scheme-theoretically dense in
its own scheme-theoretic image.

The second describes the pullback of an ideal sheaf along an open immersion on affine
opens, where it is the transport of the ideal of sections along the isomorphism of section
rings, and gives the resulting comparison criteria.

The third is flat base change: for a quasi-compact `g` and a cartesian square with flat
right-hand edge, pushforward along `g` commutes with pullback along the base change. This
is `AlgebraicGeometry.Scheme.Hom.ker_pullback_snd` in `map`/`comap` language.

## Main results

- `AlgebraicGeometry.Scheme.Hom.comap_ker_self`: `j.ker.comap j = ⊥` for every `j`;
- `AlgebraicGeometry.Scheme.IdealSheafData.fg_ideal_comap_iff`: finite generation of the
  ideal of sections transfers across an open immersion;
- `AlgebraicGeometry.Scheme.IdealSheafData.map_comap_of_isPullback`: flat base change, with
  `AlgebraicGeometry.Scheme.IdealSheafData.map_comap_opens` (restriction to an open) and
  `AlgebraicGeometry.Scheme.IdealSheafData.comap_map` (a quasi-compact flat monomorphism)
  as special cases.
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X Y : Scheme.{u}}

section Subscheme

/-- An ideal sheaf pulls back to zero along the inclusion of the closed subscheme it cuts
out: the inclusion is a monomorphism, so it is its own kernel pair. -/
lemma comap_subschemeι (I : X.IdealSheafData) : I.comap I.subschemeι = ⊥ :=
  Scheme.Hom.ker_eq_bot_of_isIso (pullback.fst I.subschemeι I.subschemeι)

/-- Every morphism is scheme-theoretically dense in its scheme-theoretic image: the ideal
sheaf cutting the image out pulls back to zero. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.comap_ker_self (j : X ⟶ Y) : j.ker.comap j = ⊥ := by
  have hfac : j.ker.comap j = (j.ker.comap j.imageι).comap j.toImage := by
    rw [← comap_comp, j.toImage_imageι]
  rw [hfac, comap_subschemeι, comap_bot]

end Subscheme

section OpenImmersion

variable {Z T : Scheme.{u}} (j : Z ⟶ T) [IsOpenImmersion j] (I : T.IdealSheafData)

/-- Pullback of ideal sheaves along an open immersion commutes with intersections. -/
lemma comap_inf_of_isOpenImmersion (K : T.IdealSheafData) :
    (I ⊓ K).comap j = I.comap j ⊓ K.comap j := by
  ext U : 2
  simp only [ideal_inf, Pi.inf_apply, ideal_comap_of_isOpenImmersion, Ideal.comap_inf]

/-- The ideal of sections of the pullback of an ideal sheaf along an open immersion is the
transport of the ideal of sections on the image along the isomorphism of section rings. -/
lemma ideal_comap_eq_map_appIso (U : Z.affineOpens) :
    (I.comap j).ideal U =
      (I.ideal ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩).map (j.appIso U.1).hom.hom := by
  rw [ideal_comap_of_isOpenImmersion, CommRingCat.comap_inv_eq_map]

/-- Finite generation of the ideal of sections is detected on either side of an open
immersion. -/
lemma fg_ideal_comap_iff (U : Z.affineOpens) :
    ((I.comap j).ideal U).FG ↔
      (I.ideal ⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩).FG := by
  rw [ideal_comap_eq_map_appIso]
  refine ⟨fun h ↦ ?_, fun h ↦ h.map _⟩
  have h' := h.map (j.appIso U.1).inv.hom
  rwa [Ideal.map_map, ← CommRingCat.hom_comp, Iso.hom_inv_id, CommRingCat.hom_id,
    Ideal.map_id] at h'

/-- The ideal of sections of the pullback of an ideal sheaf along an open immersion,
computed on an affine open of the source lying over an affine open `V` of the target: it
is the extension of the ideal of sections on `V` along the restriction map `appLE`. -/
lemma ideal_comap_eq_map_appLE (V : T.affineOpens) (U : Z.affineOpens)
    (h : U.1 ≤ j ⁻¹ᵁ V.1) :
    (I.comap j).ideal U = (I.ideal V).map (j.appLE V.1 U.1 h).hom := by
  have himg : (⟨j ''ᵁ U.1, U.2.image_of_isOpenImmersion j⟩ : T.affineOpens) ≤ V :=
    Subtype.coe_le_coe.mp <| (j.image_mono h).trans <| by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      exact inf_le_right
  rw [ideal_comap_eq_map_appIso, ← map_ideal I himg, Ideal.map_map]
  congr 1
  rw [← CommRingCat.hom_comp]
  congr 1
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

/-- To compare two pullbacks of ideal sheaves along an open immersion, it suffices to
compare the ideals of sections on a family of affine opens contained in the range whose
preimages cover the source. -/
lemma comap_le_comap_of_ideal_le {I K : T.IdealSheafData} {ι : Type*} (U : ι → T.affineOpens)
    (hran : ∀ i, (U i).1 ≤ j.opensRange) (hcov : j.opensRange ≤ ⨆ i, (U i).1)
    (H : ∀ i, I.ideal (U i) ≤ K.ideal (U i)) :
    I.comap j ≤ K.comap j := by
  refine le_of_iSup_eq_top
    (fun i ↦ ⟨j ⁻¹ᵁ (U i).1, (U i).2.preimage_of_isOpenImmersion j (hran i)⟩) ?_ fun i ↦ ?_
  · rw [eq_top_iff]
    intro x _
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcov ⟨x, rfl⟩)
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩
  · rw [ideal_comap_of_isOpenImmersion, ideal_comap_of_isOpenImmersion]
    refine Ideal.comap_mono ?_
    have himg : j ''ᵁ (j ⁻¹ᵁ (U i).1) = (U i).1 := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr (hran i)]
    have hcongr : (⟨j ''ᵁ (j ⁻¹ᵁ (U i).1),
        ((U i).2.preimage_of_isOpenImmersion j (hran i)).image_of_isOpenImmersion j⟩ :
        T.affineOpens) = U i := Subtype.ext himg
    have hle := H i
    rw [← hcongr] at hle
    exact hle

end OpenImmersion

section FlatBaseChange

/-- **Flat base change for pushforward of ideal sheaves**: for a cartesian square whose
right-hand edge `q` is flat and whose left-hand edge `g` is quasi-compact, pushing forward
along `g` and then restricting along `q` is restricting along `p` and then pushing forward
along `g'`. This is `AlgebraicGeometry.Scheme.Hom.ker_pullback_snd` in `map`/`comap`
language (Stacks Project Tag 081I). -/
theorem map_comap_of_isPullback {X' Y' : Scheme.{u}} (B : Y.IdealSheafData) {g : Y ⟶ X}
    [QuasiCompact g] {q : X' ⟶ X} [Flat q] {g' : Y' ⟶ X'} {p : Y' ⟶ Y}
    (h : IsPullback p g' g q) : (B.map g).comap q = (B.comap p).map g' := by
  have hker : ∀ {Z W : Scheme.{u}} (C : Z.IdealSheafData) (φ : Z ⟶ W),
      C.map φ = (C.subschemeι ≫ φ).ker := fun C φ ↦ by
    rw [Scheme.Hom.ker_comp, ker_subschemeι]
  -- paste the defining square of `B.comap p` onto the given cartesian square
  have H := ((IsPullback.of_hasPullback p B.subschemeι).paste_horiz h.flip).flip
  have hsub : (B.comap p).subschemeι = (B.comapIso p).hom ≫ pullback.fst p B.subschemeι :=
    (comapIso_hom_fst _ _).symm
  rw [hker B g, hker (B.comap p) g', ← Scheme.Hom.ker_pullback_snd (B.subschemeι ≫ g) q,
    hsub, Category.assoc, Scheme.Hom.ker_comp_of_isIso, ← H.isoPullback_hom_snd,
    Scheme.Hom.ker_comp_of_isIso]

/-- Restriction of a pushforward to an open subscheme, the case of
`AlgebraicGeometry.Scheme.IdealSheafData.map_comap_of_isPullback` for the open immersion
`O.ι`, which is flat. -/
theorem map_comap_opens (g : Y ⟶ X) [QuasiCompact g] (B : Y.IdealSheafData) (O : X.Opens) :
    (B.map g).comap O.ι = (B.comap (g ⁻¹ᵁ O).ι).map (g ∣_ O) :=
  map_comap_of_isPullback B (isPullback_morphismRestrict g O).flip

/-- The pushforward of an ideal sheaf along a quasi-compact flat monomorphism — for
instance the inclusion of a quasi-compact open — restricts back to the original ideal
sheaf. This is the case of
`AlgebraicGeometry.Scheme.IdealSheafData.map_comap_of_isPullback` for the kernel pair of a
monomorphism. -/
theorem comap_map (f : X ⟶ Y) [QuasiCompact f] [Flat f] [Mono f] (J : X.IdealSheafData) :
    (J.map f).comap f = J := by
  rw [map_comap_of_isPullback J (IsKernelPair.id_of_mono f), comap_id, map_id]

end FlatBaseChange

end AlgebraicGeometry.Scheme.IdealSheafData
