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
# Naturality of the normal cone and the deformation space of a section

Let `g : V ⟶ B` be smooth with a closed section `s`, with normal cone `N_s` and deformation space
`𝒟_s V` (`AlgebraicGeometry.Scheme.Hom.deformationSpaceProj`). This file proves the geometric
part of blueprint `lemma-naturality-under-base-change-etale`.

* (1) For any `b : B' ⟶ B`, the normal cone of the base-changed section is the base change of the
  normal cone, `N_{s'} ≅ N_s ×_B B'`: it is the fibre over `t = 0` of the deformation space,
  which commutes with base change
  (`AlgebraicGeometry.Scheme.Hom.exists_isPullback_deformationSpace_baseChange`).
* (2) For an étale `e : V' ⟶ V` and a section `s'` with `s' ≫ e = s` and `e⁻¹(s(B)) = s'(B)`
  scheme-theoretically, the map of normal cones `N_{s'} ⟶ N_s`, induced by the maps of
  associated graded algebras (hence linear), is an isomorphism, and the map of deformation spaces
  `𝒟_{s'} V' ⟶ 𝒟_s V` is étale: the deformation space commutes with the flat base change `e`
  (`AlgebraicGeometry.Scheme.IdealSheafData.isPullback_deformationSpaceMap_of_flat`).

## Main statements

- `AlgebraicGeometry.Scheme.Hom.exists_isPullback_normalCone_baseChange`
- `AlgebraicGeometry.Scheme.Hom.isIso_normalConeMap_of_etale`
- `AlgebraicGeometry.Scheme.Hom.etale_deformationSpaceMap_of_etale`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

section BaseChange

variable {V B B' : Scheme.{u}} (g : V ⟶ B) (s : B ⟶ V) (hs : s ≫ g = 𝟙 B) (b : B' ⟶ B)

/-- Blueprint `lemma-naturality-under-base-change-etale` (1): *the normal cone commutes with base
change.* For `g : V ⟶ B` smooth of relative dimension `d` with a closed section `s`, and any
`b : B' ⟶ B`, the normal cone of the base-changed section `s'` of `g' : V ×_B B' ⟶ B'` is the
base change of the normal cone of `s`,

`N_{s'} = N_s ×_B B'`,

compatibly with the zero sections. -/
theorem exists_isPullback_normalCone_baseChange (d : ℕ) [SmoothOfRelativeDimension d g]
    [IsClosedImmersion s] :
    ∃ ψ : (baseChangeSection g s hs b).ker.normalCone ⟶ s.ker.normalCone,
      IsPullback ψ (normalConeProj (pullback.snd g b) (baseChangeSection g s hs b))
        (normalConeProj g s) b ∧
      (baseChangeSection g s hs b).normalConeZeroSection ≫ ψ = b ≫ s.normalConeZeroSection := by
  obtain ⟨φ, hφ, hφs⟩ := exists_isPullback_deformationSpace_baseChange g s hs b d
  have P := isPullback_normalConeToDeformationSpace g s
  have P' := (isPullback_normalConeToDeformationSpace (pullback.snd g b)
    (baseChangeSection g s hs b)).paste_horiz hφ
  rw [AffineSpace.zeroSection_comp_map] at P'
  refine ⟨P.lift _ _ P'.w, IsPullback.of_right ?_ (P.lift_snd _ _ P'.w) P, P.hom_ext ?_ ?_⟩
  · rw [P.lift_fst]
    exact P'
  · rw [Category.assoc, P.lift_fst,
      reassoc_of% normalConeZeroSection_comp_normalConeToDeformationSpace, hφs, Category.assoc,
      normalConeZeroSection_comp_normalConeToDeformationSpace, ← Category.assoc,
      AffineSpace.zeroSection_comp_map, Category.assoc]
  · rw [Category.assoc, P.lift_snd, reassoc_of% normalConeZeroSection_normalConeProj
      (baseChangeSection_snd g s hs b), Category.assoc, normalConeZeroSection_normalConeProj hs,
      Category.comp_id]

end BaseChange

section Etale

open AffineZariskiSite

variable {V V' B : Scheme.{u}} (e : V' ⟶ V) (s : B ⟶ V) (s' : B ⟶ V')

/-- For `s' ≫ e = s`, the ideal of `s` pulls back into the ideal of `s'`. -/
lemma map_siteIdeal_ker_le_of_comp_eq (hs : s' ≫ e = s) ⦃U' : V'.AffineZariskiSite⦄
    ⦃U : V.AffineZariskiSite⦄ (hU : U'.1 ≤ e ⁻¹ᵁ U.1) :
    (s.ker.siteIdeal U).map (e.appLE U.1 U'.1 hU).hom ≤ s'.ker.siteIdeal U' :=
  (IdealSheafData.map_siteIdeal_le_comap e s.ker hU).trans
    ((show s.ker.comap e ≤ s'.ker by rw [IdealSheafData.comap_le_ker_iff, hs]) ⟨U'.1, U'.2⟩)

/-- If `s'` is the base change of a closed immersion `s` along `e`, then the ideal of `s'` is the
pullback of the ideal of `s`. -/
lemma ker_eq_comap_of_isPullback [IsClosedImmersion s] (he : IsPullback s' (𝟙 B) e s) :
    s'.ker = s.ker.comap e := by
  rw [← IdealSheafData.ker_fst_of_isClosedImmersion, ← he.isoPullback_hom_fst,
    ker_comp_of_isIso]

/-- The normal cone `N_I X` is the fibre over the zero section of `D_I X ⟶ 𝔸¹_X ⟶ 𝔸¹_B`,
for any `g : X ⟶ B`. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.isPullback_normalConeToDeformationSpace_proj
    {X B : Scheme.{u}} (I : X.IdealSheafData) (g : X ⟶ B) :
    IsPullback I.normalConeToDeformationSpace
      ((relativeGluingData I.coequifibered_toNormalConePresheaf).toBase ≫ g)
      (I.deformationSpaceToPolynomialSpec ≫ X.polynomialSpecToAffineSpace ≫
        AffineSpace.map (ULift.{u} (Fin 1)) g)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) B) := by
  have h : IsPullback I.normalConeToDeformationSpace
      (relativeGluingData I.coequifibered_toNormalConePresheaf).toBase
      I.deformationSpaceToPolynomialSpec X.polynomialSpecZeroSection :=
    I.isPullback_normalConeToDeformationSpace.of_iso (Iso.refl _) (Iso.refl _)
      (asIso (relativeGluingData X.coequifibered_toPolynomialZeroPresheaf).toBase) (Iso.refl _)
      (by simp) (by
        simp only [asIso_hom, Iso.refl_hom, Category.id_comp,
          IdealSheafData.normalConeToPolynomialZeroSpec]
        exact relativeGluingMap_toBase _ _ _
          I.toPolynomialZeroPresheaf_comp_polynomialZeroToNormalCone)
      (by simp) (by simp [polynomialSpecZeroSection])
  exact h.paste_vert (isPullback_polynomialSpecZeroSection g)

/-- For `h : X' ⟶ X` flat and `J = h⁻¹ I`, the normal cone `N_J X'` is the base change
`N_I X ×_X X'`. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.isPullback_normalConeMap_of_flat
    {X X' : Scheme.{u}} (h : X' ⟶ X) (I : X.IdealSheafData) (J : X'.IdealSheafData)
    (hJ : ∀ ⦃U' : X'.AffineZariskiSite⦄ ⦃U : X.AffineZariskiSite⦄ (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      (I.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤ J.siteIdeal U')
    [Flat h] (hJI : J = I.comap h) :
    IsPullback (IdealSheafData.normalConeMap h I J hJ)
      (relativeGluingData J.coequifibered_toNormalConePresheaf).toBase
      (relativeGluingData I.coequifibered_toNormalConePresheaf).toBase h := by
  have PI := I.isPullback_normalConeToDeformationSpace_proj (𝟙 X)
  have PJ := J.isPullback_normalConeToDeformationSpace_proj (𝟙 X')
  simp only [AffineSpace.map_id, Category.comp_id] at PI PJ
  have G : IsPullback (IdealSheafData.deformationSpaceMap h I J hJ)
      (J.deformationSpaceToPolynomialSpec ≫ X'.polynomialSpecToAffineSpace)
      (I.deformationSpaceToPolynomialSpec ≫ X.polynomialSpecToAffineSpace)
      (AffineSpace.map (ULift.{u} (Fin 1)) h) := by
    refine IsPullback.of_bot ?_ ?_ (AffineSpace.isPullback_map h)
    · have hproj {Y : Scheme.{u}} (K : Y.IdealSheafData) :
          (K.deformationSpaceToPolynomialSpec ≫ Y.polynomialSpecToAffineSpace) ≫
            𝔸(ULift.{u} (Fin 1); Y) ↘ Y = K.deformationSpaceProj := by
        simpa using K.deformationSpaceProj_over' (𝟙 Y)
      rw [hproj, hproj]
      exact IdealSheafData.isPullback_deformationSpaceMap_of_flat h I J hJ hJI
    · rw [IdealSheafData.deformationSpaceMap_toPolynomialSpec_assoc,
        polynomialSpecMap_polynomialSpecToAffineSpace, Category.assoc]
  have P := PJ.paste_horiz G
  rw [AffineSpace.zeroSection_comp_map,
    ← IdealSheafData.normalConeMap_normalConeToDeformationSpace] at P
  exact IsPullback.of_right P (IdealSheafData.normalConeMap_toBase h I J hJ) PI

/-- Blueprint `lemma-naturality-under-base-change-etale` (4): let `e : V' ⟶ V` be étale and `s'`
a section with `s' ≫ e = s` and `e⁻¹(s(B)) = s'(B)` scheme-theoretically. Then the induced map
of normal cones `N_{s'} ⟶ N_s` (`AlgebraicGeometry.Scheme.IdealSheafData.normalConeMap`, induced
by the maps of associated graded algebras, hence linear) is an isomorphism. -/
theorem isIso_normalConeMap_of_etale [Etale e] [IsClosedImmersion s] (hs : s' ≫ e = s)
    (he : IsPullback s' (𝟙 B) e s) :
    IsIso (IdealSheafData.normalConeMap e s.ker s'.ker
      (map_siteIdeal_ker_le_of_comp_eq e s s' hs)) := by
  have hA := IdealSheafData.isPullback_normalConeMap_of_flat e s.ker s'.ker
    (map_siteIdeal_ker_le_of_comp_eq e s s' hs) (ker_eq_comap_of_isPullback e s s' he)
  rw [← s.ker.normalConeToQuotientSpec_toBase, ← s'.ker.normalConeToQuotientSpec_toBase] at hA
  have : IsClosedImmersion s' := MorphismProperty.of_isPullback he.flip inferInstance
  have hq : s'.toQuotientSpec ≫ IdealSheafData.quotientSpecMap e s.ker s'.ker
      (map_siteIdeal_ker_le_of_comp_eq e s s' hs) = s.toQuotientSpec := by
    rw [← cancel_mono (relativeGluingData s.ker.coequifibered_toQuotientAlgebra).toBase,
      Category.assoc, IdealSheafData.quotientSpecMap_toBase, toQuotientSpec_toBase_assoc,
      toQuotientSpec_toBase, hs]
  have hB : IsPullback (IdealSheafData.quotientSpecMap e s.ker s'.ker
      (map_siteIdeal_ker_le_of_comp_eq e s s' hs))
      (relativeGluingData s'.ker.coequifibered_toQuotientAlgebra).toBase
      (relativeGluingData s.ker.coequifibered_toQuotientAlgebra).toBase e :=
    he.flip.of_iso (asIso s'.toQuotientSpec) (asIso s.toQuotientSpec) (Iso.refl _) (Iso.refl _)
      (by simp [hq]) (by simp) (by simp) (by simp)
  have : IsIso (IdealSheafData.quotientSpecMap e s.ker s'.ker
      (map_siteIdeal_ker_le_of_comp_eq e s s' hs)) := by
    rw [← IsIso.inv_hom_id_assoc s'.toQuotientSpec (IdealSheafData.quotientSpecMap e s.ker s'.ker
      (map_siteIdeal_ker_le_of_comp_eq e s s' hs)), hq]
    infer_instance
  exact (hA.of_bot (IdealSheafData.normalConeMap_normalConeToQuotientSpec _ _ _ _)
    hB).isIso_fst_of_isIso

/-- Blueprint `lemma-naturality-under-base-change-etale` (5): let `e : V' ⟶ V` be étale and `s'`
a section with `s' ≫ e = s` and `e⁻¹(s(B)) = s'(B)` scheme-theoretically. Then the induced map
of deformation spaces `𝒟_{s'} V' ⟶ 𝒟_s V`
(`AlgebraicGeometry.Scheme.IdealSheafData.deformationSpaceMap`) is étale. -/
theorem etale_deformationSpaceMap_of_etale [Etale e] [IsClosedImmersion s] (hs : s' ≫ e = s)
    (he : IsPullback s' (𝟙 B) e s) :
    Etale (IdealSheafData.deformationSpaceMap e s.ker s'.ker
      (map_siteIdeal_ker_le_of_comp_eq e s s' hs)) :=
  MorphismProperty.of_isPullback (IdealSheafData.isPullback_deformationSpaceMap_of_flat e s.ker
    s'.ker _ (ker_eq_comap_of_isPullback e s s' he)).flip inferInstance

end Etale

end AlgebraicGeometry.Scheme.Hom
