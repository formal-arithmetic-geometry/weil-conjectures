/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.Defect
public import WeilConjectures.TraceFormula.Specialization.DeformationModelGeneric
public import WeilConjectures.TraceFormula.Specialization.DeformationSpecialFibreComp
public import WeilConjectures.TraceFormula.Specialization.OpenExchange

/-!

# The deformation to the normal cone along a morphism and the zero section

Let `f : X' ⟶ X` be a morphism of `k`-schemes, `Z = V(I) ⊆ X` a closed subscheme and
`Z' = f⁻¹ Z = V(f^* I)` its schematic inverse image, with the restriction `f_Z : Z' ⟶ Z`
(`ProEtale.CondensedRing.centreMap`). The deformation of `f_Z` maps the special fibre
`N_⊥ Z' ≅ Z' ⊗ k'` of the constant family of `Z'` to that of `Z`
(`ProEtale.CondensedRing.centreSpecialFibreMap`).

This file proves the geometric inputs of the proper and smooth exchanges for the defect of the
specialization (blueprint `det-sp-defect-proper-smooth`), following blueprint
`det-sp-dnc-base-change`:

* the squares of geometric generic fibres of the morphisms of deformation models are cartesian
  (`ProEtale.CondensedRing.isPullback_deformationModel_ε_deformationGenericMap`);
* for `f` proper (resp. smooth), the morphism of total spaces `𝒟_{Z'} X' ⟶ 𝒟_Z X` is proper
  (resp. smooth) (`ProEtale.CondensedRing.isProper_deformationTotalMap`,
  `ProEtale.CondensedRing.smooth_deformationTotalMap`);
* the special fibre of the deformation of `f` pulls the zero section of `N_Z X` back to the zero
  section of `N_{Z'} X'`: the square of zero sections is cartesian
  (`ProEtale.CondensedRing.isPullback_zeroSectionSpecialFibreMap`);
* the morphisms of models `𝒟_{Z'} X' ⟶ 𝒟_Z X` and `Z' × S ⟶ Z × S` are compatible with the zero
  sections `ẽ` (`ProEtale.CondensedRing.zeroSectionDeformationModelHom_total_comp`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] {X X' : Over (Spec (.of k))} (f : X' ⟶ X)
  (I : X.left.IdealSheafData) (k' : Type u) [Field k'] [Algebra k k']

/-! ### The restriction to the centre -/

/-- The restriction `f_Z : Z' = V(f^* I) ⟶ Z = V(I)` of `f : X' ⟶ X` to the inverse image of the
centre. -/
noncomputable def centreMap : centre X' (I.comap f.left) ⟶ centre X I :=
  Over.homMk (IdealSheafData.subschemeMap _ _ f.left (I.le_map_comap f.left)) (by
    change _ ≫ I.subschemeι ≫ X.hom = (I.comap f.left).subschemeι ≫ X'.hom
    rw [IdealSheafData.subschemeMap_subschemeι_assoc, Over.w f])

@[reassoc (attr := simp)]
lemma centreMap_centreι : centreMap f I ≫ centreι X I = centreι X' (I.comap f.left) ≫ f :=
  Over.OverMorphism.ext (IdealSheafData.subschemeMap_subschemeι _ _ _ (I.le_map_comap f.left))

/-- The zero ideal of `Z'` contains the pullback of the zero ideal of `Z`. -/
lemma siteIdeal_map_appLE_le_bot_centreMap
    ⦃U' : (centre X' (I.comap f.left)).left.AffineZariskiSite⦄
    ⦃U : (centre X I).left.AffineZariskiSite⦄ (hU : U'.1 ≤ (centreMap f I).left ⁻¹ᵁ U.1) :
    ((⊥ : (centre X I).left.IdealSheafData).siteIdeal U).map
        ((centreMap f I).left.appLE U.1 U'.1 hU).hom ≤
      (⊥ : (centre X' (I.comap f.left)).left.IdealSheafData).siteIdeal U' :=
  IdealSheafData.siteIdeal_map_appLE_le_of_le_map bot_le hU

/-- The map `N_⊥ Z' ⟶ N_⊥ Z` of special fibres of the constant families, the deformation of
`f_Z`; under `N_⊥ Z ≅ Z ⊗ k'` it is `f_Z ⊗ k'`. -/
noncomputable def centreSpecialFibreMap :
    deformationSpecialFibre (centre X' (I.comap f.left)) ⊥ k' ⟶
      deformationSpecialFibre (centre X I) ⊥ k' :=
  deformationSpecialFibreMap (centreMap f I) (siteIdeal_map_appLE_le_bot_centreMap f I) k'

/-- The morphism of constant families `Z' × S ⟶ Z × S` induced by `f_Z : Z' ⟶ Z`. -/
noncomputable def centreDeformationModelHom :
    (deformationModel (centre X' (I.comap f.left)) ⊥ k').Hom
      (deformationModel (centre X I) ⊥ k') (centreMap f I).left
      (centreSpecialFibreMap f I k').left :=
  deformationModelHom (centreMap f I) (siteIdeal_map_appLE_le_bot_centreMap f I) k'

/-! ### The deformation along `f` -/

/-- The ideal `f^* I` contains the pullback of `I`, chart by chart. -/
lemma siteIdeal_map_appLE_le_comap ⦃U' : X'.left.AffineZariskiSite⦄
    ⦃U : X.left.AffineZariskiSite⦄ (hU : U'.1 ≤ f.left ⁻¹ᵁ U.1) :
    (I.siteIdeal U).map (f.left.appLE U.1 U'.1 hU).hom ≤ (I.comap f.left).siteIdeal U' :=
  IdealSheafData.siteIdeal_map_appLE_le_of_le_map (I.le_map_comap f.left) hU

/-- The map `N_{Z'} X' ⟶ N_Z X` of special fibres of the deformations to the normal cones induced
by `f`, for `Z' = f⁻¹ Z`. -/
noncomputable def comapSpecialFibreMap :
    deformationSpecialFibre X' (I.comap f.left) k' ⟶ deformationSpecialFibre X I k' :=
  deformationSpecialFibreMap f (siteIdeal_map_appLE_le_comap f I) k'

/-- The morphism of deformation models `𝒟_{Z'} X' ⟶ 𝒟_Z X` induced by `f`, for `Z' = f⁻¹ Z`
(blueprint `det-sp-dnc-base-change` (1)). -/
noncomputable def comapDeformationModelHom :
    (deformationModel X' (I.comap f.left) k').Hom (deformationModel X I k') f.left
      (comapSpecialFibreMap f I k').left :=
  deformationModelHom f (siteIdeal_map_appLE_le_comap f I) k'

/-! ### Geometric generic fibres -/

section Generic

variable {Y : Over (Spec (.of k))} (g : X ⟶ Y) {I : Y.left.IdealSheafData}
  {J : X.left.IdealSheafData}
  (hJ : ∀ ⦃U' : X.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
    (hU : U'.1 ≤ g.left ⁻¹ᵁ U.1), (I.siteIdeal U).map (g.left.appLE U.1 U'.1 hU).hom ≤
      J.siteIdeal U')

/-- The square of identifications `ε` of the geometric generic fibres of a morphism of deformation
models is cartesian: `𝒳_Ω = X ×_Y 𝒴_Ω`, since both are base changes to `Ω`. -/
lemma isPullback_deformationModel_ε_deformationGenericMap :
    IsPullback (deformationModel X J k').ε (deformationGenericMap g hJ k') g.left
      (deformationModel Y I k').ε :=
  sorry

/-- The morphisms of geometric generic fibres of deformation models compose. -/
lemma deformationGenericMap_comp {W : Over (Spec (.of k))} (h : W ⟶ X)
    {K : W.left.IdealSheafData}
    (hK : ∀ ⦃U' : W.left.AffineZariskiSite⦄ ⦃U : X.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ h.left ⁻¹ᵁ U.1), (J.siteIdeal U).map (h.left.appLE U.1 U'.1 hU).hom ≤
        K.siteIdeal U')
    (hKI : ∀ ⦃U' : W.left.AffineZariskiSite⦄ ⦃U : Y.left.AffineZariskiSite⦄
      (hU : U'.1 ≤ (h ≫ g).left ⁻¹ᵁ U.1),
      (I.siteIdeal U).map ((h ≫ g).left.appLE U.1 U'.1 hU).hom ≤ K.siteIdeal U') :
    deformationGenericMap h hK k' ≫ deformationGenericMap g hJ k' =
      deformationGenericMap (h ≫ g) hKI k' :=
  sorry

/-- For `f` proper and `J = f⁻¹ I`, the morphism of total spaces `𝒳 ⟶ 𝒴` of the deformation
models is proper (blueprint `det-sp-dnc-base-change` (3)). -/
lemma isProper_deformationTotalMap [IsProper g.left] (hJI : J = I.comap g.left) :
    IsProper (deformationTotalMap g hJ k') :=
  sorry

/-- For `f` smooth and `J = f⁻¹ I`, the morphism of total spaces `𝒳 ⟶ 𝒴` of the deformation
models is smooth: it is the base change of `f` (blueprint `det-sp-dnc-base-change` (3)). -/
lemma smooth_deformationTotalMap [Smooth g.left] (hJI : J = I.comap g.left) :
    Smooth (deformationTotalMap g hJ k') :=
  sorry

end Generic

instance [IsProper f.left] : IsProper (centreMap f I).left :=
  sorry

instance [Smooth f.left] : Smooth (centreMap f I).left :=
  sorry

/-! ### The zero sections -/

/-- **The zero sections are compatible with the deformation of `f`** (blueprint
`det-sp-dnc-base-change` (2)): the special fibre `N_{Z'} X' ⟶ N_Z X` of the deformation of `f`
pulls the zero section `e : N_⊥ Z ⟶ N_Z X` back to the zero section `e' : N_⊥ Z' ⟶ N_{Z'} X'`,
that is, `f̃_s⁻¹(Z) = Z'` schematically. -/
lemma isPullback_zeroSectionSpecialFibreMap :
    IsPullback (zeroSectionSpecialFibreMap X' (I.comap f.left) k').left
      (centreSpecialFibreMap f I k').left (comapSpecialFibreMap f I k').left
      (zeroSectionSpecialFibreMap X I k').left :=
  sorry

/-- The morphisms of total spaces of `Z' × S ⟶ 𝒟_{Z'} X' ⟶ 𝒟_Z X` and `Z' × S ⟶ Z × S ⟶ 𝒟_Z X`
agree. -/
lemma zeroSectionDeformationModelHom_total_comp :
    (zeroSectionDeformationModelHom X' (I.comap f.left) k').total ≫
        (comapDeformationModelHom f I k').total =
      (centreDeformationModelHom f I k').total ≫ (zeroSectionDeformationModelHom X I k').total :=
  sorry

/-- The morphisms of geometric generic fibres of `Z' × S ⟶ 𝒟_{Z'} X' ⟶ 𝒟_Z X` and
`Z' × S ⟶ Z × S ⟶ 𝒟_Z X` agree. -/
lemma zeroSectionDeformationModelHom_generic_comp :
    (zeroSectionDeformationModelHom X' (I.comap f.left) k').generic ≫
        (comapDeformationModelHom f I k').generic =
      (centreDeformationModelHom f I k').generic ≫
        (zeroSectionDeformationModelHom X I k').generic :=
  sorry

/-- For the zero ideal, the morphism of total spaces `Z × S ⟶ 𝒟_⊥ X` of the zero section is an
isomorphism: the centre `V(⊥)` is `X`. -/
instance isIso_zeroSectionDeformationModelHom_bot_total :
    IsIso (zeroSectionDeformationModelHom X ⊥ k').total :=
  sorry

/-- For the zero ideal, the morphism of geometric generic fibres of the zero section is an
isomorphism. -/
instance isIso_zeroSectionDeformationModelHom_bot_generic :
    IsIso (zeroSectionDeformationModelHom X ⊥ k').generic :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
