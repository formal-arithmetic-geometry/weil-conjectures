/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenProjectionMate
public import WeilConjectures.AlgebraicGeometry.Finite.Clopen.FiniteClopenMateData
import WeilConjectures.AlgebraicGeometry.Proper.Open.ProperOpenRefinementAlphaPlusInclusion
import WeilConjectures.AlgebraicGeometry.SmoothPurity.IdentityPushPlusInclusion

/-! # Bounded-below compatibility of the proper/open refinement mate

Source: the canonical D+ inclusion calculation in Step 2 of
lem-pur-pf-witnessed-mate-normalization, expanding the finite transport normalization;
Stacks Project, Tags 015F, 0B65 and 0F7B
(blueprint: lem-pur-refinement-mate-plus-compatibility).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

private theorem included_proper_counit
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {Y Z : Scheme.{u}} (f : Y ⟶ Z)
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ))) :
    (upperStar (ModuleCat.{u + 1} Λ) f).leftDerivedFunctor.map
        ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlusCompatibility.hom.app K) ≫
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app K.obj =
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) f).hom.app
        ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlus.obj K).obj ≫
      DerivedCategory.Plus.ι.map
        ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) f).counit.app K) := by
  change _ = _ ≫ DerivedCategory.Plus.ι.map
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).derivedAdjunctionPlus.counit.app K)
  rw [Adjunction.derivedAdjunctionPlus, Adjunction.map_restrictFullyFaithful_counit_app]
  simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_inv,
    Iso.refl_hom, NatTrans.id_app, Category.id_comp,
    Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app, Functor.whiskerLeft_app]
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory
    (ModuleCat.{u + 1} Λ) f).inv.naturality
      ((lowerStar (ModuleCat.{u + 1} Λ) f).rightDerivedFunctorPlusCompatibility.hom.app K)
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn
  erw [reassoc_of% hn]
  erw [Iso.hom_inv_id_app_assoc]
  rfl

set_option maxRecDepth 2048 in
private theorem refinement_mate_inclusion
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X T₁ T₂ : Scheme.{u}} (r : T₁ ⟶ T₂) [IsProper r]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [QuasiCompact j₁] [QuasiCompact j₂]
    (h : j₁ ≫ r = j₂)
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
    (openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂).mapDerivedCategory.map
        ((lowerStar (ModuleCat.{u + 1} Λ) (𝟙 X)).rightDerivedFunctorPlusCompatibility.hom.app
          K) ≫
      (properOpenMate Λ j₁ (𝟙 X) r j₂
        (h.trans (Category.id_comp j₂).symm)).app K.obj =
    DerivedCategory.Plus.ι.map
        ((cbcClopenMatePlus Λ j₁ j₂ (𝟙 X) r
          (h.trans (Category.id_comp j₂).symm)).app K) ≫
      (lowerStar (ModuleCat.{u + 1} Λ) r).rightDerivedFunctorPlusCompatibility.hom.app
        ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K) := by
  let J₁ := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁
  let J₂ := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂
  let P := upperStar (ModuleCat.{u + 1} Λ) r
  let R := lowerStar (ModuleCat.{u + 1} Λ) r
  let R₀ := lowerStar (ModuleCat.{u + 1} Λ) (𝟙 X)
  let a := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) r
  let a₀ := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)
  let ap := derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) r
  let ap₀ := derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) (𝟙 X)
  let hh := h.trans (Category.id_comp j₂).symm
  let α := properOpenAlpha Λ j₁ (𝟙 X) r j₂ hh
  let αp := cbcClopenAlphaPlus Λ j₁ j₂ (𝟙 X) r hh
  let γp := cbcClopenMatePlus Λ j₁ j₂ (𝟙 X) r hh
  apply (a.homEquiv
    (J₂.mapDerivedCategory.obj (R₀.rightDerivedFunctorPlus.obj K).obj)
    (J₁.mapDerivedCategory.obj K.obj)).symm.injective
  simp only [Adjunction.homEquiv_symm_apply, Functor.map_comp, Category.assoc]
  change P.leftDerivedFunctor.map (J₂.mapDerivedCategory.map
      (R₀.rightDerivedFunctorPlusCompatibility.hom.app K)) ≫
        P.leftDerivedFunctor.map ((properOpenMate Λ j₁ (𝟙 X) r j₂ hh).app K.obj) ≫
        a.counit.app (J₁.mapDerivedCategory.obj K.obj) =
    P.leftDerivedFunctor.map (DerivedCategory.Plus.ι.map (γp.app K)) ≫
      P.leftDerivedFunctor.map (R.rightDerivedFunctorPlusCompatibility.hom.app
        (J₁.mapDerivedCategoryPlus.obj K)) ≫
      a.counit.app (J₁.mapDerivedCategory.obj K.obj)
  rw [show P.leftDerivedFunctor.map
      ((properOpenMate Λ j₁ (𝟙 X) r j₂ hh).app K.obj) ≫ a.counit.app _ =
      α.app (R₀.rightDerivedFunctor.obj K.obj) ≫
        J₁.mapDerivedCategory.map (a₀.counit.app K.obj) from
    mateEquiv_counit a₀ a (TwoSquare.mk _ _ _ _ α) K.obj]
  have hn := α.naturality (R₀.rightDerivedFunctorPlusCompatibility.hom.app K)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc]
  erw [hn]
  rw [Category.assoc, ← J₁.mapDerivedCategory.map_comp]
  rw [included_proper_counit Λ (𝟙 X) K, Functor.map_comp]
  rw [← Category.assoc]
  erw [← properOpenRefinementAlpha_plus_inclusion Λ r j₁ j₂ h
      (R₀.rightDerivedFunctorPlus.obj K)]
  erw [included_proper_counit Λ r (J₁.mapDerivedCategoryPlus.obj K)]
  have hp := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) r).hom.naturality
    (DerivedCategory.Plus.ι.map (γp.app K))
  rw [← Category.assoc]
  erw [hp]
  simp only [Category.assoc]
  congr 1
  change DerivedCategory.Plus.ι.map
      (αp.app (R₀.rightDerivedFunctorPlus.obj K) ≫
        J₁.mapDerivedCategoryPlus.map (ap₀.counit.app K)) =
    DerivedCategory.Plus.ι.map
      (P.mapDerivedCategoryPlus.map (γp.app K) ≫
        ap.counit.app (J₁.mapDerivedCategoryPlus.obj K))
  exact congrArg DerivedCategory.Plus.ι.map
    (mateEquiv_counit ap₀ ap (TwoSquare.mk _ _ _ _ αp) K).symm

/-- The identity-normalized unbounded proper/open mate restricts to the specified
bounded-below clopen mate. This assertion is entirely on the pro-etale site and
applies to every bounded-below input, without an etale-origin witness.
Source: Step 2 of lem-pur-pf-witnessed-mate-normalization, canonical D+ inclusions;
Stacks Tags 015F, 0B65 and 0F7B
(blueprint: lem-pur-refinement-mate-plus-compatibility).

Proof: Let b and q be the projections of T1 ×_T2 X and s=(j1,1) its clopen section.
First identify the unbounded clopen alpha with localization of the sheaf alpha
used in cbcClopenAlphaPlus. For the cartesian open comparison, transpose its inverse
under the open adjunction: both constructions give the pulled-back open unit
followed by the pullback-square compositor. For the clopen factor, both are the
localized direct-image unit followed by the inverse of the open-to-direct-image
comparison; they are identity on s(X) and zero on its complement. The open and
pullback compositors agree by uniqueness of adjoints and the localization
factorization equations. Composition gives the equality of the two alpha words.
The canonical D+ inclusions carry the bounded-below derived adjunction unit and
counit to the unbounded unit and counit through rightDerivedFunctorPlusCompatibility
and the exact-functor inclusion comparisons. Expand both mates as unit, alpha,
and counit. Naturality moves these compatibility maps through the three factors;
the alpha equality identifies the middle factors, and the derived unit/counit
factorization equations identify the outer factors. This gives compatibility of
the two mates before identity normalization. Finally, the conjugate of the
canonical identity pullback is the canonical identity direct-image comparison:
transpose it under the identity-morphism adjunction; its transpose is the identity
pullback comparison, by the triangle identity and the identity localization
factorization. On D+ this is rightDerivedFunctorPlusNatIso(lowerStarId) followed
by rightDerivedFunctorPlusIdIso. Substitute its inverse into the preceding mate
compatibility and cancel the identity comparisons. The source and target factors
left over are exactly the three displayed inclusion comparisons. -/
theorem properOpenRefinementMate_plus_compatibility
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X T₁ T₂ : Scheme.{u}} (r : T₁ ⟶ T₂) [IsProper r]
    (j₁ : X ⟶ T₁) (j₂ : X ⟶ T₂)
    [IsOpenImmersion j₁] [IsOpenImmersion j₂] [QuasiCompact j₁] [QuasiCompact j₂]
    (h : j₁ ≫ r = j₂)
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
    let J₁ := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁
    let J₂ := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂
    let R := lowerStar (ModuleCat.{u + 1} Λ) r
    let d := Functor.rightDerivedFunctorPlusNatIso
      (lowerStarId (ModuleCat.{u + 1} Λ) X) ≪≫
        Functor.rightDerivedFunctorPlusIdIso _
    J₂.mapDerivedCategory.map
        (((conjugateIsoEquiv
          (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))
          Adjunction.id) (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).symm).inv.app
            K.obj) ≫
      (properOpenMate Λ j₁ (𝟙 X) r j₂
        (h.trans (Category.id_comp j₂).symm)).app K.obj =
    J₂.mapDerivedCategoryPlusCompatibility.inv.app K ≫
      DerivedCategory.Plus.ι.map
        (J₂.mapDerivedCategoryPlus.map (d.inv.app K) ≫
          (cbcClopenMatePlus Λ j₁ j₂ (𝟙 X) r
            (h.trans (Category.id_comp j₂).symm)).app K) ≫
      R.rightDerivedFunctorPlusCompatibility.hom.app (J₁.mapDerivedCategoryPlus.obj K) ≫
      R.rightDerivedFunctor.map (J₁.mapDerivedCategoryPlusCompatibility.hom.app K) := by
  dsimp only
  rw [← identityPush_plus_inclusion Λ X K, Functor.map_comp, Category.assoc,
    refinement_mate_inclusion Λ r j₁ j₂ h K]
  simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Functor.map_comp, Category.assoc]
  let J₂ := openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₂
  let R := lowerStar (ModuleCat.{u + 1} Λ) r
  let d := Functor.rightDerivedFunctorPlusNatIso
    (lowerStarId (ModuleCat.{u + 1} Λ) X) ≪≫ Functor.rightDerivedFunctorPlusIdIso _
  let m := DerivedCategory.Plus.ι.map ((cbcClopenMatePlus Λ j₁ j₂ (𝟙 X) r
    (h.trans (Category.id_comp j₂).symm)).app K)
  let c := R.rightDerivedFunctorPlusCompatibility.hom.app
    ((openImmersionLowerShriek (ModuleCat.{u + 1} Λ) j₁).mapDerivedCategoryPlus.obj K)
  change J₂.mapDerivedCategory.map (DerivedCategory.Plus.ι.map (d.inv.app K)) ≫ m ≫ c =
    𝟙 _ ≫ J₂.mapDerivedCategory.map (DerivedCategory.Plus.ι.map (d.inv.app K)) ≫
      m ≫ c ≫ R.rightDerivedFunctor.map (𝟙 _)
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.comp_id]

end AlgebraicGeometry.ProEtale
