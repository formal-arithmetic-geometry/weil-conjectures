/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChange
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.BaseChangeClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DeformationSpace.NormalConeMap

/-!
# Naturality of the normal cone of a section

Let `g : V ⟶ B` be a morphism with a closed section `s`, with normal cone `N_s` and deformation
space `D_s V`. This file proves the geometric half of blueprint
`lemma-naturality-under-base-change-etale`:

* for a base change `b : B' ⟶ B`, the normal cone of the base-changed section `s'` of
  `g' : V ×_B B' ⟶ B'` is `N_{s'} = N_s ×_B B'` (clause (1));
* for an étale map of pairs, that is an étale `e : V' ⟶ V` and a closed section `s'` of
  `e ≫ g` with `s' ≫ e = s` and `e⁻¹(s(B)) = s'(B)` scheme-theoretically, the induced map of
  normal cones `N_{s'} ⟶ N_s` is an isomorphism (clause (4)) and the induced map of
  deformation spaces is étale (clause (5)).

Both statements follow from the fact that the normal cone is the fibre of the deformation space
over `t = 0`: the deformation space commutes with arbitrary base change in `B` for smooth `g`
(`AlgebraicGeometry.Scheme.Hom.exists_isPullback_deformationSpace_baseChange`), and with flat
base change in `V`
(`AlgebraicGeometry.Scheme.IdealSheafData.isPullback_deformationSpaceMap_of_flat`).
For the étale map of pairs, `N_{s'} = N_s ×_V V'`, and `N_s ⟶ V` factors through `s`, along
which `e` pulls back to the identity of `B` by the hypothesis on the centres.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.isPullback_normalConeMap_baseChangeSection`: `N_{s'} = N_s ×_B B'`.
- `AlgebraicGeometry.Scheme.Hom.isIso_normalConeMap_of_etale`: `N_{s'} ≅ N_s` for an étale map
  of pairs.
- `AlgebraicGeometry.Scheme.Hom.etale_deformationSpaceMap`: the map of deformation spaces induced
  by an étale map of pairs is étale.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

open AffineZariskiSite

variable {V B : Scheme.{u}} {g : V ⟶ B} {s : B ⟶ V}

/-- The projection `N_s ⟶ V` of the normal cone of a closed section factors through the
section: it is `N_s ⟶ B ⟶ V`. -/
lemma normalCone_toBase_eq [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) :
    (relativeGluingData s.ker.coequifibered_toNormalConePresheaf).toBase =
      normalConeProj g s ≫ s := by
  have h : (relativeGluingData s.ker.coequifibered_toQuotientAlgebra).toBase =
      inv s.toQuotientSpec ≫ s := by
    rw [IsIso.eq_inv_comp, toQuotientSpec_toBase]
  simp only [normalConeProj, ← s.ker.normalConeToQuotientSpec_toBase, h, Category.assoc,
    reassoc_of% hs]

/-- Blueprint `lemma-naturality-under-base-change-etale--1`: *the normal cone commutes with
base change.* For `g : V ⟶ B` smooth of relative dimension `d` with a closed section `s`, and any
`b : B' ⟶ B`, the normal cone of the base-changed section `s'` of `g' : V ×_B B' ⟶ B'` is the
base change of the normal cone of `s`, `N_{s'} = N_s ×_B B'`, by the morphism of normal cones
induced by `V ×_B B' ⟶ V`. -/
theorem isPullback_normalConeMap_baseChangeSection (d : ℕ) [SmoothOfRelativeDimension d g]
    [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B) {B' : Scheme.{u}} (b : B' ⟶ B) :
    IsPullback (IdealSheafData.normalConeMap (pullback.fst g b) s.ker
        (baseChangeSection g s hs b).ker (map_siteIdeal_ker_le_baseChangeSection g s hs b))
      (normalConeProj (pullback.snd g b) (baseChangeSection g s hs b)) (normalConeProj g s)
      b := by
  have hD : IsPullback _ (deformationSpaceProj (pullback.snd g b) (baseChangeSection g s hs b))
      (deformationSpaceProj g s) (AffineSpace.map _ b) :=
    IdealSheafData.isPullback_deformationSpaceMap_proj _ _ _
      (map_siteIdeal_ker_le_baseChangeSection g s hs b) (fun x ↦ by
        obtain ⟨U', U, hU, hx, _, H⟩ :=
          exists_isPushout_extendedReesAlgebraMap_baseChange g s hs b d x
        exact ⟨U', U, hU, hx, H⟩) g _ b (IsPullback.of_hasPullback g b)
  have hout := (isPullback_normalConeToDeformationSpace (pullback.snd g b)
    (baseChangeSection g s hs b)).paste_horiz hD
  rw [AffineSpace.zeroSection_comp_map,
    ← IdealSheafData.normalConeMap_normalConeToDeformationSpace] at hout
  refine IsPullback.of_right hout ?_ (isPullback_normalConeToDeformationSpace g s)
  simp only [normalConeProj, IdealSheafData.normalConeMap_toBase_assoc, pullback.condition,
    Category.assoc]

variable {V' : Scheme.{u}} (e : V' ⟶ V) (s' : B ⟶ V')

/-- If `e⁻¹(s(B)) = s'(B)` scheme-theoretically, the ideal of `s` pulls back into the ideal of
`s'`, so that `e` induces morphisms of deformation spaces and of normal cones. -/
lemma map_siteIdeal_ker_le_of_comap_eq (hker : s.ker.comap e = s'.ker)
    ⦃U' : V'.AffineZariskiSite⦄ ⦃U : V.AffineZariskiSite⦄ (hU : U'.1 ≤ e ⁻¹ᵁ U.1) :
    (s.ker.siteIdeal U).map (e.appLE U.1 U'.1 hU).hom ≤ s'.ker.siteIdeal U' :=
  hker ▸ IdealSheafData.map_siteIdeal_le_comap e s.ker hU

/-- The morphism of normal cones induced by `e : V' ⟶ V` lies over `B`. -/
@[reassoc]
lemma normalConeMap_normalConeProj (hker : s.ker.comap e = s'.ker) :
    IdealSheafData.normalConeMap e s.ker s'.ker (map_siteIdeal_ker_le_of_comap_eq e s' hker) ≫
      normalConeProj g s = normalConeProj (e ≫ g) s' := by
  simp only [normalConeProj, IdealSheafData.normalConeMap_toBase_assoc]

/-- The morphism of deformation spaces induced by `e : V' ⟶ V` lies over `𝔸¹_B`. -/
@[reassoc]
lemma deformationSpaceMap_deformationSpaceProj (hker : s.ker.comap e = s'.ker) :
    IdealSheafData.deformationSpaceMap e s.ker s'.ker
        (map_siteIdeal_ker_le_of_comap_eq e s' hker) ≫ deformationSpaceProj g s =
      deformationSpaceProj (e ≫ g) s' := by
  have := IdealSheafData.deformationSpaceMap_proj e s.ker s'.ker
    (map_siteIdeal_ker_le_of_comap_eq e s' hker) g (e ≫ g) (𝟙 B) (Category.comp_id _).symm
  rwa [AffineSpace.map_id, Category.comp_id] at this

/-- The morphism of normal cones induced by `e : V' ⟶ V` carries the zero section of `N_{s'}` to
the zero section of `N_s`. -/
@[reassoc]
lemma normalConeZeroSection_normalConeMap [IsClosedImmersion s] [IsClosedImmersion s']
    (hes : s' ≫ e = s) (hker : s.ker.comap e = s'.ker) :
    s'.normalConeZeroSection ≫ IdealSheafData.normalConeMap e s.ker s'.ker
      (map_siteIdeal_ker_le_of_comap_eq e s' hker) = s.normalConeZeroSection := by
  have h : s'.toQuotientSpec ≫ IdealSheafData.quotientSpecMap e s.ker s'.ker
      (map_siteIdeal_ker_le_of_comap_eq e s' hker) = s.toQuotientSpec := by
    rw [← cancel_mono (relativeGluingData s.ker.coequifibered_toQuotientAlgebra).toBase,
      Category.assoc, IdealSheafData.quotientSpecMap_toBase, toQuotientSpec_toBase_assoc,
      toQuotientSpec_toBase, hes]
  rw [Scheme.Hom.normalConeZeroSection, Scheme.Hom.normalConeZeroSection, Category.assoc]
  change s'.toQuotientSpec ≫ s'.ker.normalConeZeroSection ≫ _ =
    s.toQuotientSpec ≫ s.ker.normalConeZeroSection
  rw [IdealSheafData.normalConeZeroSection_normalConeMap, reassoc_of% h]

/-- Blueprint `lemma-naturality-under-base-change-etale--4`: *an étale map of pairs induces an
isomorphism of normal cones.* Let `e : V' ⟶ V` be étale and `s'` a closed section of `e ≫ g`
with `s' ≫ e = s` and `e⁻¹(s(B)) = s'(B)` scheme-theoretically. Then the induced morphism of
normal cones `N_{s'} ⟶ N_s` is an isomorphism; it lies over `B`
(`AlgebraicGeometry.Scheme.Hom.normalConeMap_normalConeProj`) and respects the zero sections
(`AlgebraicGeometry.Scheme.IdealSheafData.normalConeZeroSection_normalConeMap`). Its linearity
is not stated: the normal cone carries no module structure here. -/
theorem isIso_normalConeMap_of_etale [IsClosedImmersion s] (hs : s ≫ g = 𝟙 B)
    [Etale e] [IsClosedImmersion s'] (hes : s' ≫ e = s) (hker : s.ker.comap e = s'.ker) :
    IsIso (IdealSheafData.normalConeMap e s.ker s'.ker
      (map_siteIdeal_ker_le_of_comap_eq e s' hker)) := by
  have hφ := IdealSheafData.isPullback_deformationSpaceMap_of_flat e s.ker s'.ker
    (map_siteIdeal_ker_le_of_comap_eq e s' hker) hker.symm
  have hs' : s' ≫ e ≫ g = 𝟙 B := by rw [reassoc_of% hes, hs]
  have h₁ : IsPullback (IdealSheafData.normalConeMap e s.ker s'.ker
      (map_siteIdeal_ker_le_of_comap_eq e s' hker)) s'.ker.normalConeToDeformationSpace
      s.ker.normalConeToDeformationSpace (IdealSheafData.deformationSpaceMap e s.ker s'.ker
        (map_siteIdeal_ker_le_of_comap_eq e s' hker)) := by
    refine IsPullback.of_right ?_
      (IdealSheafData.normalConeMap_normalConeToDeformationSpace _ _ _ _)
      (isPullback_normalConeToDeformationSpace g s).flip
    rw [normalConeMap_normalConeProj e s' hker, deformationSpaceMap_deformationSpaceProj e s' hker]
    exact (isPullback_normalConeToDeformationSpace (e ≫ g) s').flip
  have h₂ := h₁.paste_vert hφ
  simp only [IdealSheafData.normalConeToDeformationSpace_deformationSpaceProj] at h₂
  rw [normalCone_toBase_eq hs, normalCone_toBase_eq hs'] at h₂
  have h₃ : IsPullback (𝟙 B) s' s e :=
    (isPullback_of_isClosedImmersion s' s (𝟙 B) e (by rw [hes, Category.id_comp]) hker).flip
  exact (IsPullback.of_bot h₂ (by rw [normalConeMap_normalConeProj e s' hker,
    Category.comp_id]) h₃).isIso_fst_of_isIso

/-- Blueprint `lemma-naturality-under-base-change-etale--5`, the geometric part: *an étale map
of pairs induces an étale map of deformation spaces.* If `e : V' ⟶ V` is étale and
`e⁻¹(s(B)) = s'(B)` scheme-theoretically, then `D_{s'} V' = V' ×_V D_s V`, so the morphism
`D_{s'} V' ⟶ D_s V` is étale, being a base change of `e`. -/
theorem etale_deformationSpaceMap [Etale e] (hker : s.ker.comap e = s'.ker) :
    Etale (IdealSheafData.deformationSpaceMap e s.ker s'.ker
      (map_siteIdeal_ker_le_of_comap_eq e s' hker)) :=
  MorphismProperty.of_isPullback (IdealSheafData.isPullback_deformationSpaceMap_of_flat e s.ker
    s'.ker (map_siteIdeal_ker_le_of_comap_eq e s' hker) hker.symm).flip ‹_›

end AlgebraicGeometry.Scheme.Hom
