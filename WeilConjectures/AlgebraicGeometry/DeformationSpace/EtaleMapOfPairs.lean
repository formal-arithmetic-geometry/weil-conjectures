/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.DeformationSpace.NormalConeMapPullback
public import WeilConjectures.AlgebraicGeometry.DeformationToNormalCone

/-!
# Étale maps of pairs

Let `g : V ⟶ B` be a morphism with a closed section `s`, let `e : V' ⟶ V` be étale and let
`s' : B ⟶ V'` be a section with `s' ≫ e = s` such that `e⁻¹(s(B)) = s'(B)` scheme-theoretically,
i.e. the square

```
  B --s'--> V'
  ‖         |e
  B --s---> V
```

is cartesian. Then the ideal of `s'` is the pullback of the ideal of `s`, so that `e` induces a
morphism of deformation spaces `D_{s'} V' ⟶ D_s V` and of normal cones `N_{s'} ⟶ N_s`. The
first is étale and the second is an isomorphism.

## Main statements

- `AlgebraicGeometry.Scheme.Hom.ker_eq_comap_of_isPullback`: the ideal of `s'` is `e⁻¹` of the
  ideal of `s`.
- `AlgebraicGeometry.Scheme.Hom.etale_deformationSpaceMap_of_isPullback`: the induced morphism of
  deformation spaces is étale.
- `AlgebraicGeometry.Scheme.Hom.isIso_normalConeMap_of_isPullback`: the induced morphism of normal
  cones is an isomorphism.

## Implementation details

* The morphism of deformation spaces is étale: it is the base change of `e` along
  `D_s V ⟶ V`.
* The morphism of normal cones is an isomorphism: by flat base change it is the base change of `e`
  along `N_s ⟶ V`, which factors through `s`, and the base change of `e` along `s` is the identity
  of `B`. It is linear, being induced by the map of associated graded algebras.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

open AffineZariskiSite

variable {V V' B : Scheme.{u}} (s : B ⟶ V) (e : V' ⟶ V) (s' : B ⟶ V')
  (he : IsPullback s' (𝟙 B) e s)

include he in
/-- If `e⁻¹(s(B)) = s'(B)` scheme-theoretically, the ideal of `s'` is the pullback along `e` of
the ideal of `s`. -/
lemma ker_eq_comap_of_isPullback [IsClosedImmersion s] : s'.ker = s.ker.comap e := by
  rw [← IdealSheafData.ker_fst_of_isClosedImmersion, ← he.isoPullback_hom_fst, ker_comp_of_isIso]

include he in
/-- The compatibility `e^* I_s ⊆ I_{s'}` of the ideals of the sections, which induces the
morphisms of deformation spaces and of normal cones along `e`. -/
lemma map_siteIdeal_ker_le_of_isPullback [IsClosedImmersion s]
    ⦃U' : V'.AffineZariskiSite⦄ ⦃U : V.AffineZariskiSite⦄ (hU : U'.1 ≤ e ⁻¹ᵁ U.1) :
    (s.ker.siteIdeal U).map (e.appLE U.1 U'.1 hU).hom ≤ s'.ker.siteIdeal U' := by
  rw [ker_eq_comap_of_isPullback s e s' he]
  exact IdealSheafData.map_siteIdeal_le_comap e s.ker hU

/-- The normal cone `N_I X` is the fibre of `D_I X ⟶ 𝔸¹_X` over the zero section of `𝔸¹_X`. -/
lemma _root_.AlgebraicGeometry.Scheme.IdealSheafData.isPullback_normalConeToDeformationSpace_zero
    {X : Scheme.{u}} (I : X.IdealSheafData) :
    IsPullback I.normalConeToDeformationSpace
      (relativeGluingData I.coequifibered_toNormalConePresheaf).toBase
      (I.deformationSpaceToPolynomialSpec ≫ X.polynomialSpecToAffineSpace)
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) X) := by
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
  simpa using h.paste_vert (IsPullback.of_vert_isIso (snd := 𝟙 X)
    ⟨(polynomialSpecZeroSection_comp_polynomialSpecToAffineSpace X).trans
      (Category.id_comp _).symm⟩)

/-- The zero section of `𝔸¹_{X'}` is the base change of the zero section of `𝔸¹_X` along
`𝔸¹_{X'} ⟶ 𝔸¹_X`. -/
lemma _root_.AlgebraicGeometry.AffineSpace.isPullback_zeroSection_map {X X' : Scheme.{u}}
    (h : X' ⟶ X) :
    IsPullback h (AffineSpace.zeroSection (ULift.{u} (Fin 1)) X')
      (AffineSpace.zeroSection (ULift.{u} (Fin 1)) X) (AffineSpace.map _ h) := by
  refine IsPullback.of_bot ?_ (AffineSpace.zeroSection_comp_map h).symm
    (AffineSpace.isPullback_map h)
  rw [AffineSpace.zeroSection_over, AffineSpace.zeroSection_over]
  exact IsPullback.of_vert_isIso ⟨by simp⟩

/-- For a flat `h : X' ⟶ X` and `J = h⁻¹ I`, the normal cone `N_J X'` is the base change
`N_I X ×_X X'`. -/
theorem _root_.AlgebraicGeometry.Scheme.IdealSheafData.isPullback_normalConeMap_of_flat
    {X X' : Scheme.{u}} (h : X' ⟶ X) (I : X.IdealSheafData) (J : X'.IdealSheafData)
    (hJ : ∀ ⦃U' : X'.AffineZariskiSite⦄ ⦃U : X.AffineZariskiSite⦄ (hU : U'.1 ≤ h ⁻¹ᵁ U.1),
      (I.siteIdeal U).map (h.appLE U.1 U'.1 hU).hom ≤ J.siteIdeal U')
    [Flat h] (hJI : J = I.comap h) :
    IsPullback (IdealSheafData.normalConeMap h I J hJ)
      (relativeGluingData J.coequifibered_toNormalConePresheaf).toBase
      (relativeGluingData I.coequifibered_toNormalConePresheaf).toBase h := by
  have hs : IsPullback (IdealSheafData.normalConeMap h I J hJ ≫
      (relativeGluingData I.coequifibered_toNormalConePresheaf).toBase)
      J.normalConeToDeformationSpace (AffineSpace.zeroSection (ULift.{u} (Fin 1)) X)
      (IdealSheafData.deformationSpaceMap h I J hJ ≫ I.deformationSpaceToPolynomialSpec ≫
        X.polynomialSpecToAffineSpace) := by
    rw [IdealSheafData.normalConeMap_toBase,
      IdealSheafData.deformationSpaceMap_toPolynomialSpec_assoc,
      polynomialSpecMap_polynomialSpecToAffineSpace, ← Category.assoc]
    exact (J.isPullback_normalConeToDeformationSpace_zero.flip).paste_horiz
      (AffineSpace.isPullback_zeroSection_map h)
  have := (IsPullback.of_right hs
    (IdealSheafData.normalConeMap_normalConeToDeformationSpace h I J hJ)
    I.isPullback_normalConeToDeformationSpace_zero.flip).paste_vert
    (IdealSheafData.isPullback_deformationSpaceMap_of_flat h I J hJ hJI)
  simpa using this

/-- For a closed immersion `t : B ⟶ W`, the projection `N_t ⟶ W` factors through `t`. -/
lemma normalCone_toBase_eq {W : Scheme.{u}} (t : B ⟶ W) [IsClosedImmersion t] :
    (relativeGluingData t.ker.coequifibered_toNormalConePresheaf).toBase =
      (t.ker.normalConeToQuotientSpec ≫ inv t.toQuotientSpec) ≫ t := by
  rw [Category.assoc, (IsIso.inv_comp_eq _).mpr (toQuotientSpec_toBase t).symm,
    IdealSheafData.normalConeToQuotientSpec_toBase]

variable [IsClosedImmersion s]

/-- The morphism `D_{s'} V' ⟶ D_s V` of deformation spaces induced by an étale map of pairs is
étale. -/
theorem etale_deformationSpaceMap_of_isPullback [Etale e] :
    Etale (IdealSheafData.deformationSpaceMap e s.ker s'.ker
      (map_siteIdeal_ker_le_of_isPullback s e s' he)) :=
  MorphismProperty.of_isPullback (IdealSheafData.isPullback_deformationSpaceMap_of_flat e s.ker
    s'.ker _ (ker_eq_comap_of_isPullback s e s' he)).flip inferInstance

/-- The morphism `N_{s'} ⟶ N_s` of normal cones induced by an étale map of pairs is an
isomorphism. -/
theorem isIso_normalConeMap_of_isPullback [Etale e] :
    IsIso (IdealSheafData.normalConeMap e s.ker s'.ker
      (map_siteIdeal_ker_le_of_isPullback s e s' he)) := by
  have : IsClosedImmersion s' := MorphismProperty.of_isPullback he.flip ‹_›
  have hP := IdealSheafData.isPullback_normalConeMap_of_flat e s.ker s'.ker
    (map_siteIdeal_ker_le_of_isPullback s e s' he) (ker_eq_comap_of_isPullback s e s' he)
  rw [normalCone_toBase_eq s, normalCone_toBase_eq s'] at hP
  refine (IsPullback.of_bot hP ?_ he.flip).isIso_fst_of_isIso
  rw [Category.comp_id, ← cancel_mono s, Category.assoc, hP.w, Category.assoc, he.w,
    Category.id_comp]

variable (g : V ⟶ B)

/-- The morphism of deformation spaces induced by an étale map of pairs lies over `𝔸¹_B`. -/
@[reassoc]
lemma deformationSpaceMap_deformationSpaceProj_of_isPullback :
    IdealSheafData.deformationSpaceMap e s.ker s'.ker
        (map_siteIdeal_ker_le_of_isPullback s e s' he) ≫ deformationSpaceProj g s =
      deformationSpaceProj (e ≫ g) s' := by
  rw [deformationSpaceProj, IdealSheafData.deformationSpaceMap_proj e s.ker s'.ker _ g (e ≫ g)
    (𝟙 B) (Category.comp_id _).symm, AffineSpace.map_id, Category.comp_id, deformationSpaceProj]

/-- The comparison `𝔸¹_{V(I_{s'})} ⟶ 𝔸¹_{V(I_s)}` induced by an étale map of pairs is compatible
with the affine lines over `B`. -/
@[reassoc]
lemma affineSpaceToQuotientPolynomialSpec_comp_comparison_of_isPullback :
    s'.affineSpaceToQuotientPolynomialSpec ≫
      (IdealSheafData.quotientPolynomialPullbackData e s.ker s'.ker
        (map_siteIdeal_ker_le_of_isPullback s e s' he)).comparison _ _ =
      s.affineSpaceToQuotientPolynomialSpec := by
  rw [← cancel_mono (relativeGluingMap V.coequifibered_toPolynomialPresheaf
    s.ker.coequifibered_toQuotientPolynomialAlgebra s.ker.polynomialToQuotientPolynomial),
    Category.assoc, PullbackData.comparison_comp_relativeGluingMap
      (H := V.coequifibered_toPolynomialPresheaf)
      (H' := V'.coequifibered_toPolynomialPresheaf) _ _ _ _ _ _
      (IdealSheafData.polynomialToQuotientPolynomial_comp_quotientPolynomialPullbackData_map
        _ _ _ _),
    affineSpaceToQuotientPolynomialSpec_toPolynomialSpec_assoc,
    affineSpaceToQuotientPolynomialSpec_toPolynomialSpec, ← Scheme.polynomialSpecMap,
    (IsIso.eq_comp_inv _).mpr (Scheme.polynomialSpecMap_polynomialSpecToAffineSpace _)]
  simp only [Category.assoc, IsIso.inv_hom_id_assoc, ← AffineSpace.map_comp_assoc, he.w,
    Category.id_comp]

/-- The morphism of deformation spaces induced by an étale map of pairs carries the section
`s̃'` to `s̃`. -/
@[reassoc]
lemma deformationSpaceSection_deformationSpaceMap_of_isPullback :
    s'.deformationSpaceSection ≫ IdealSheafData.deformationSpaceMap e s.ker s'.ker
        (map_siteIdeal_ker_le_of_isPullback s e s' he) = s.deformationSpaceSection := by
  rw [deformationSpaceSection, deformationSpaceSection, Category.assoc,
    IdealSheafData.deformationSpaceMap,
    ← PullbackData.comparison_comp_relativeGluingMap
      (HG := s.ker.coequifibered_toQuotientPolynomialAlgebra) _ _ _ _ _ _ _
      (IdealSheafData.reesToQuotientPolynomial_comp_quotientPolynomialPullbackData_map _ _ _ _),
    affineSpaceToQuotientPolynomialSpec_comp_comparison_of_isPullback_assoc s e s' he]

/-- The morphism of normal cones induced by an étale map of pairs lies over `B`. -/
@[reassoc]
lemma normalConeMap_normalConeProj_of_isPullback :
    IdealSheafData.normalConeMap e s.ker s'.ker
        (map_siteIdeal_ker_le_of_isPullback s e s' he) ≫ normalConeProj g s =
      normalConeProj (e ≫ g) s' := by
  rw [normalConeProj, IdealSheafData.normalConeMap_toBase_assoc, normalConeProj]

/-- The morphism of normal cones induced by an étale map of pairs carries the zero section to the
zero section. -/
@[reassoc]
lemma normalConeZeroSection_normalConeMap_of_isPullback :
    s'.normalConeZeroSection ≫ IdealSheafData.normalConeMap e s.ker s'.ker
        (map_siteIdeal_ker_le_of_isPullback s e s' he) = s.normalConeZeroSection := by
  have hq : s'.toQuotientSpec ≫ IdealSheafData.quotientSpecMap e s.ker s'.ker
      (map_siteIdeal_ker_le_of_isPullback s e s' he) = s.toQuotientSpec := by
    rw [← cancel_mono (relativeGluingData s.ker.coequifibered_toQuotientAlgebra).toBase,
      Category.assoc, IdealSheafData.quotientSpecMap_toBase, toQuotientSpec_toBase_assoc,
      toQuotientSpec_toBase, he.w, Category.id_comp]
  rw [normalConeZeroSection, Category.assoc, ← IdealSheafData.normalConeZeroSection,
    IdealSheafData.normalConeZeroSection_normalConeMap, reassoc_of% hq, normalConeZeroSection,
    IdealSheafData.normalConeZeroSection]

/-- The morphism of deformation spaces induced by an étale map of pairs restricts to `e` on the
fibres over `t = 1`. -/
@[reassoc]
lemma deformationSpaceOneFibre_deformationSpaceMap_of_isPullback :
    deformationSpaceOneFibre (e ≫ g) s' ≫ IdealSheafData.deformationSpaceMap e s.ker s'.ker
        (map_siteIdeal_ker_le_of_isPullback s e s' he) = e ≫ deformationSpaceOneFibre g s := by
  have hw : (deformationSpaceOneFibre (e ≫ g) s' ≫ IdealSheafData.deformationSpaceMap e s.ker
      s'.ker (map_siteIdeal_ker_le_of_isPullback s e s' he)) ≫ deformationSpaceProj g s =
      (e ≫ g ≫ oneSectionToPuncturedLine B) ≫ (puncturedLine B).ι := by
    rw [Category.assoc, deformationSpaceMap_deformationSpaceProj_of_isPullback s e s' he,
      (isPullback_deformationSpaceOneFibre (e ≫ g) s').w]
    simp
  have hG := isPullback_deformationSpaceGeneric g s
  rw [← hG.lift_fst _ _ hw, deformationSpaceOneFibre.eq_1 g s]
  refine Eq.trans ?_ (Category.assoc _ _ _)
  congr 1
  refine pullback.hom_ext ?_ (by simp)
  rw [← deformationSpaceGeneric_toBase, hG.lift_fst_assoc, Category.assoc,
    IdealSheafData.deformationSpaceMap_toBase, deformationSpaceOneFibre]
  simp

end AlgebraicGeometry.Scheme.Hom
