/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.Defect
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence

/-!

# The zero-section map for a centre with a retraction

Let `i : Z = V(I) ⟶ X` be the centre of the deformation to the normal cone, and let
`r : X ⟶ Z` be a retraction of `i` (`i ≫ r = 𝟙`). This is the situation of Verdier's contraction
argument (blueprint `det-sp-thick-origin-homotopy`) for `X = 𝔸ⁿ⁺¹`, `Z = 𝔸ⁿ × 0`, with `r` the
linear projection, the value at `a = 0` of the scaling `H_a(v, x) = (v, a x)`.

Since `r^* ⊥ ⊆ I`, the retraction lifts to a morphism of models `r̃ : 𝒟_Z X ⟶ Z × S` from the
deformation to the normal cone to the constant family (`ProEtale.CondensedRing.retractionModelHom`),
over `r` and a morphism of special fibres `s_r : N_Z X ⊗ k' ⟶ Z ⊗ k'`. The composite `ẽ ≫ r̃` is the
identity of the constant family, since the deformation space of the zero ideal is the relative
affine line (`ProEtale.CondensedRing.deformationTotalMap_centreι_comp_retraction`). The square
law of the pullback exchanges (`NearbyCyclesModel.Hom.pullbackExchange_square`) then shows that
the zero-section map at a complex `Lr^* M` pulled back along the retraction is split by
`Le^*(α_r(M))`, up to the canonical comparisons
(`ProEtale.CondensedRing.isIso_comp_zeroSectionMap_upperStar_retraction`). Consequently
`ε_{X,Z}(Lr^* M)` is an isomorphism if and only if `Le^*(α_r(M))` is
(`ProEtale.CondensedRing.isIso_zeroSectionMap_upperStar_retraction_iff`).

-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

namespace NearbyCyclesModel.Hom

variable {X X' Y Y' W W' : Scheme.{u}} {M : NearbyCyclesModel X X'} {N : NearbyCyclesModel Y Y'}
  {P : NearbyCyclesModel W W'} {f : X ⟶ Y} {f' : X' ⟶ Y'} {g : Y ⟶ W} {g' : Y' ⟶ W'}

/-- The composite of two morphisms of models. -/
@[simps]
def comp (φ : M.Hom N f f') (ψ : N.Hom P g g') : M.Hom P (f ≫ g) (f' ≫ g') where
  total := φ.total ≫ ψ.total
  generic := φ.generic ≫ ψ.generic
  comm_j := by rw [Category.assoc, ψ.comm_j, ← Category.assoc, φ.comm_j, Category.assoc]
  comm_i := by rw [Category.assoc, ψ.comm_i, ← Category.assoc, φ.comm_i, Category.assoc]
  comm_ε := by rw [Category.assoc, ψ.comm_ε, ← Category.assoc, φ.comm_ε, Category.assoc]

end NearbyCyclesModel.Hom

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k'] (r : X ⟶ centre X I)

/-- The pullback of the zero ideal of the centre along any morphism `r : X ⟶ Z` is contained in
`I`. -/
lemma siteIdeal_map_appLE_bot_le ⦃U' : X.left.AffineZariskiSite⦄
    ⦃U : (centre X I).left.AffineZariskiSite⦄ (hU : U'.1 ≤ r.left ⁻¹ᵁ U.1) :
    ((⊥ : (centre X I).left.IdealSheafData).siteIdeal U).map (r.left.appLE U.1 U'.1 hU).hom ≤
      I.siteIdeal U' := by
  rw [IdealSheafData.siteIdeal, IdealSheafData.ideal_bot, Pi.bot_apply, Ideal.map_bot]
  exact bot_le

/-- The morphism of models `r̃ : 𝒟_Z X ⟶ Z × S` from the deformation to the normal cone of
`Z = V(I)` to the constant family of `Z`, induced by a morphism `r : X ⟶ Z`. -/
noncomputable def retractionModelHom :
    (deformationModel X I k').Hom (deformationModel (centre X I) ⊥ k') r.left
      (deformationSpecialFibreMap r (siteIdeal_map_appLE_bot_le X I r) k').left :=
  deformationModelHom r (siteIdeal_map_appLE_bot_le X I r) k'

end AlgebraicGeometry.ProEtale.CondensedRing

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] (X : Over (Spec (.of k))) (I : X.left.IdealSheafData)
  (k' : Type u) [Field k'] [Algebra k k'] {r : X ⟶ centre X I}

/-- For a retraction `r` of `i : Z ⟶ X`, the composite `D_⊥ Z ⟶ D_I X ⟶ D_⊥ Z` of the morphisms
of deformation spaces is the identity: `D_⊥ Z` is the relative affine line `𝔸¹_Z`. -/
lemma deformationSpaceMap_centreι_comp_retraction (hr : centreι X I ≫ r = 𝟙 _) :
    IdealSheafData.deformationSpaceMap (centreι X I).left I ⊥ (siteIdeal_map_appLE_le_bot X I) ≫
      IdealSheafData.deformationSpaceMap r.left ⊥ I (siteIdeal_map_appLE_bot_le X I r) = 𝟙 _ := by
  rw [← cancel_mono ((⊥ : (centre X I).left.IdealSheafData).deformationSpaceToPolynomialSpec ≫
    (centre X I).left.polynomialSpecToAffineSpace), Category.assoc,
    IdealSheafData.deformationSpaceMap_toPolynomialSpec_assoc,
    IdealSheafData.deformationSpaceMap_toPolynomialSpec_assoc,
    polynomialSpecMap_polynomialSpecToAffineSpace,
    polynomialSpecMap_polynomialSpecToAffineSpace_assoc, ← AffineSpace.map_comp, ← Over.comp_left,
    hr, Over.id_left, AffineSpace.map_id, Category.comp_id, Category.id_comp]

lemma deformationTotalMap_centreι_comp_retraction (hr : centreι X I ≫ r = 𝟙 _) :
    deformationTotalMap (centreι X I) (siteIdeal_map_appLE_le_bot X I) k' ≫
      deformationTotalMap r (siteIdeal_map_appLE_bot_le X I r) k' = 𝟙 _ := by
  refine (isPullback_deformationTotal (centre X I) ⊥ k').hom_ext ?_ ?_
  · rw [Category.assoc, deformationTotalMap_toSpace, deformationTotalMap_toSpace_assoc,
      deformationSpaceMap_centreι_comp_retraction X I hr, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, deformationTotalMap_toTrait, deformationTotalMap_toTrait,
      Category.id_comp]

lemma deformationGenericMap_centreι_comp_retraction (hr : centreι X I ≫ r = 𝟙 _) :
    deformationGenericMap (centreι X I) (siteIdeal_map_appLE_le_bot X I) k' ≫
      deformationGenericMap r (siteIdeal_map_appLE_bot_le X I r) k' = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · simp [deformationGenericMap, deformationTotalMap_centreι_comp_retraction X I k' hr]
  · simp [deformationGenericMap]

lemma deformationSpecialFibreMap_centreι_comp_retraction (hr : centreι X I ≫ r = 𝟙 _) :
    (deformationSpecialFibreMap (centreι X I) (siteIdeal_map_appLE_le_bot X I) k').left ≫
      (deformationSpecialFibreMap r (siteIdeal_map_appLE_bot_le X I r) k').left = 𝟙 _ := by
  refine pullback.hom_ext ?_ ?_
  · simp [deformationSpecialFibreMap, deformationTotalMap_centreι_comp_retraction X I k' hr]
  · simp [deformationSpecialFibreMap]

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

/-- **The zero-section map at a complex pulled back along a retraction is split** (Verdier's
contraction argument, blueprint `det-sp-thick-origin-homotopy`, the factorisation at `a = 0`): for a
retraction `r` of `i : Z ⟶ X` and `M` on `Z`, the composite
`Le^* Ls_r^* Ψ_{Z × S}(M) ⟶ Le^* Ψ_{X,Z}(Lr^* M) ⟶ Ψ_{Z × S}(Li^* Lr^* M)` of `Le^*` of the
pullback exchange `α_r(M)` of `r̃` and of the zero-section map `ε_{X,Z}(Lr^* M)` is an isomorphism.
It is identified with the pullback exchange of the identity of the constant family by the square
law of the pullback exchanges, as `ẽ ≫ r̃` is the identity. -/
theorem isIso_comp_zeroSectionMap_upperStar_retraction (hr : centreι X I ≫ r = 𝟙 _)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (centre X I).left) Ab.{u + 1})
      (condensedRingObj Λ (centre X I).left))) :
    IsIso (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).map
        (((retractionModelHom X I k' r).pullbackExchange Λ).app M) ≫
      zeroSectionMap X I k' Λ (L((r.left)^*⟦Λ⟧).obj M)) := by
  have hb : (centreι X I).left ≫ r.left = 𝟙 _ ≫ 𝟙 _ := by
    rw [← Over.comp_left, hr, Over.id_left, Category.id_comp]
  have hs := (deformationSpecialFibreMap_centreι_comp_retraction X I k' hr).trans
    (Category.id_comp _).symm
  have h := NearbyCyclesModel.Hom.pullbackExchange_square Λ (zeroSectionDeformationModelHom X I k')
    (retractionModelHom X I k' r) (NearbyCyclesModel.Hom.id _) (NearbyCyclesModel.Hom.id _)
    ((deformationTotalMap_centreι_comp_retraction X I k' hr).trans (Category.id_comp _).symm)
    ((deformationGenericMap_centreι_comp_retraction X I k' hr).trans (Category.id_comp _).symm)
    hb hs M
  have : IsIso (NearbyCyclesModel.Hom.id (deformationModel (centre X I) ⊥ k')).total := by
    rw [NearbyCyclesModel.Hom.id_total]
    infer_instance
  have : IsIso (NearbyCyclesModel.Hom.id (deformationModel (centre X I) ⊥ k')).generic := by
    rw [NearbyCyclesModel.Hom.id_generic]
    infer_instance
  have := (NearbyCyclesModel.Hom.id
    (deformationModel (centre X I) ⊥ k')).isIso_pullbackExchange_of_isIso Λ
  have : IsIso _ := (congrArg IsIso h).mpr inferInstance
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ _ _ _ this

/-- For a retraction `r` of `i : Z ⟶ X` and `M` on `Z`, the zero-section map `ε_{X,Z}(Lr^* M)` is
a split epimorphism, split by `Le^*` of the pullback exchange `α_r(M)` of `r̃`. -/
theorem isSplitEpi_zeroSectionMap_upperStar_retraction (hr : centreι X I ≫ r = 𝟙 _)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (centre X I).left) Ab.{u + 1})
      (condensedRingObj Λ (centre X I).left))) :
    IsSplitEpi (zeroSectionMap X I k' Λ (L((r.left)^*⟦Λ⟧).obj M)) := by
  have := isIso_comp_zeroSectionMap_upperStar_retraction X I k' Λ hr M
  exact IsSplitEpi.mk' ⟨inv (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).map
      (((retractionModelHom X I k' r).pullbackExchange Λ).app M) ≫
      zeroSectionMap X I k' Λ (L((r.left)^*⟦Λ⟧).obj M)) ≫
    L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).map
      (((retractionModelHom X I k' r).pullbackExchange Λ).app M),
    by rw [Category.assoc, IsIso.inv_hom_id]⟩

/-- **Reduction of the zero-section map at a pulled-back complex to the pullback exchange of the
retraction** (Verdier's contraction argument, blueprint `det-sp-thick-origin-homotopy`): for a
retraction `r` of `i : Z ⟶ X` and `M` on `Z`, the zero-section map `ε_{X,Z}(Lr^* M)` is an
isomorphism if and only if `Le^*` of the pullback exchange `α_r(M) : Ls_r^* Ψ_{Z × S}(M) ⟶
Ψ_{X,Z}(Lr^* M)` of `r̃ : 𝒟_Z X ⟶ Z × S` is. In Verdier's argument, `Le^*(α_r(M))` is the value at
`a = 0` of the endomorphisms `φ_a` of `Le^* Ψ_{X,Z}(Lr^* M)` induced by the scaling, whose
invertibility follows from `φ_0 = φ_1 = id` by `𝔸¹`-homotopy invariance. -/
theorem isIso_zeroSectionMap_upperStar_retraction_iff (hr : centreι X I ≫ r = 𝟙 _)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (centre X I).left) Ab.{u + 1})
      (condensedRingObj Λ (centre X I).left))) :
    IsIso (zeroSectionMap X I k' Λ (L((r.left)^*⟦Λ⟧).obj M)) ↔
      IsIso (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).map
        (((retractionModelHom X I k' r).pullbackExchange Λ).app M)) := by
  have := isIso_comp_zeroSectionMap_upperStar_retraction X I k' Λ hr M
  refine ⟨fun _ ↦ IsIso.of_isIso_comp_right _
    (zeroSectionMap X I k' Λ (L((r.left)^*⟦Λ⟧).obj M)), fun _ ↦ IsIso.of_isIso_comp_left
      (L(((zeroSectionSpecialFibreMap X I k').left)^*⟦Λ⟧).map
        (((retractionModelHom X I k' r).pullbackExchange Λ).app M)) _⟩

/-- If the pullback exchange `α_r(M)` of `r̃ : 𝒟_Z X ⟶ Z × S` is an isomorphism (for instance by
smooth base change for nearby cycles, `r̃` being smooth with cartesian square of generic fibres when
`X = Z × 𝔸¹`), then the zero-section map `ε_{X,Z}(Lr^* M)` is an isomorphism. -/
theorem isIso_zeroSectionMap_upperStar_retraction (hr : centreι X I ≫ r = 𝟙 _)
    (M : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology (centre X I).left) Ab.{u + 1})
      (condensedRingObj Λ (centre X I).left)))
    [IsIso (((retractionModelHom X I k' r).pullbackExchange Λ).app M)] :
    IsIso (zeroSectionMap X I k' Λ (L((r.left)^*⟦Λ⟧).obj M)) :=
  (isIso_zeroSectionMap_upperStar_retraction_iff X I k' Λ hr M).mpr inferInstance

end AlgebraicGeometry.ProEtale.CondensedRing
