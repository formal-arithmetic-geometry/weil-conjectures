/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B6
-/
module

public import Sheaf.AlgebraicGeometry.SupportedCoefficientDerivedOpenMate
import Sheaf.AlgebraicGeometry.SupportedCoefficientComplexOpenTensor
import all Sheaf.AlgebraicGeometry.SupportedExteriorProduct
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# Open pullback of the supported coefficient tensor comparison

Source: Stacks Project, Tags 09XP and 0F1E, the coefficient calculation in
lem-pur-supported-product-localization, steps 5 and 11.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
universe u v v₁ v₂ v₃ u₁ u₂ u₃
open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
namespace AlgebraicGeometry.Etale
attribute [local instance] supportedHasSheafify supportedHasWeakSheafify

/-- Identify the derived first coefficient functor with coefficients followed by the
canonical derived projection inverse image.
Source: Stacks Tag 0F1E (blueprint: lem-pur-supported-coefficient-open-tensor). -/
noncomputable def supportFirstCoefficientProjectionIso (A : Type (u + 1)) [CommRing A]
    {S X Y B : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X)
    [IsClosedImmersion b] :
    (supportedFirstCoefficients A f g b).mapDerivedCategory ≅
      (supportedCoefficients A b).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)).leftDerivedFunctor :=
  Functor.mapDerivedCategoryCompIso (supportedCoefficients A b)
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)) ≪≫
    Functor.isoWhiskerLeft (supportedCoefficients A b).mapDerivedCategory
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.fst f g)).symm

/-- The analogous comparison for the second projection.
Source: Stacks Tag 0F1E (blueprint: lem-pur-supported-coefficient-open-tensor). -/
noncomputable def supportSecondCoefficientProjectionIso (A : Type (u + 1)) [CommRing A]
    {S X Y D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y)
    [IsClosedImmersion d] :
    (supportedSecondCoefficients A f g d).mapDerivedCategory ≅
      (supportedCoefficients A d).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).leftDerivedFunctor :=
  Functor.mapDerivedCategoryCompIso (supportedCoefficients A d)
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)) ≪≫
    Functor.isoWhiskerLeft (supportedCoefficients A d).mapDerivedCategory
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.snd f g)).symm

/-- Pull the first supported coefficient to the open product, in the direction of the
mate of support restriction.
Source: Stacks Tag 0F1E (blueprint: lem-pur-supported-coefficient-open-tensor). -/
noncomputable def supportFirstOpenCoefficientMap (A : Type (u + 1)) [CommRing A]
    {S X Y B : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X)
    [IsClosedImmersion b] (U : X.Opens) (M : DerivedCategory (ModuleCat.{u + 1} A)) :
    (supportedFirstCoefficients A (U.ι ≫ f) g (supportOnOpen b U)).mapDerivedCategory.obj M ⟶
      (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)).mapDerivedCategory.obj
        ((supportedFirstCoefficients A f g b).mapDerivedCategory.obj M) :=
  (supportFirstCoefficientProjectionIso A (U.ι ≫ f) g (supportOnOpen b U)).hom.app M ≫
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst (U.ι ≫ f) g)).leftDerivedFunctor.map
      ((supportCoefficientOpenMate A U.ι b (supportOnOpen b U)
        (supportOnOpen_complement b U)).app M) ≫
    (supportPullbackSquareIso (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)
      (pullback.fst f g) (pullback.fst (U.ι ≫ f) g) U.ι
      (supportedFirstOpenMap_fst f g U)
      ((supportedCoefficients A b).mapDerivedCategory.obj M)).inv ≫
    (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)).mapDerivedCategory.map
      ((supportFirstCoefficientProjectionIso A f g b).inv.app M)

/-- Pull the uncut second supported coefficient to the open product.
Source: Stacks Tag 0F1E (blueprint: lem-pur-supported-coefficient-open-tensor). -/
noncomputable def supportFirstOpenSecondCoefficientMap (A : Type (u + 1)) [CommRing A]
    {S X Y D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y)
    [IsClosedImmersion d] (U : X.Opens) (N : DerivedCategory (ModuleCat.{u + 1} A)) :
    (supportedSecondCoefficients A (U.ι ≫ f) g d).mapDerivedCategory.obj N ⟶
      (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)).mapDerivedCategory.obj
        ((supportedSecondCoefficients A f g d).mapDerivedCategory.obj N) :=
  (supportSecondCoefficientProjectionIso A (U.ι ≫ f) g d).hom.app N ≫
    (supportPullbackProjectionIso (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)
      (pullback.snd f g) (pullback.snd (U.ι ≫ f) g)
      (supportedFirstOpenMap_snd f g U)
      ((supportedCoefficients A d).mapDerivedCategory.obj N)).inv ≫
    (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)).mapDerivedCategory.map
      ((supportSecondCoefficientProjectionIso A f g d).inv.app N)

end AlgebraicGeometry.Etale

universe w

section CachedSheafProofs
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] Functor.mapDerivedCategory Functor.leftDerivedFunctor
set_option backward.isDefEq.respectTransparency.types true

section
variable {C D E C' D' E' : Type*}
  [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']

/-- The normalization equation is kept abstract when specialized to sheaf functors. -/
@[irreducible]
private def tensorNormalization [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalCategory C'] [MonoidalCategory D']
    (L : C ⥤ C') (J : D ⥤ D') [L.LaxMonoidal] [J.LaxMonoidal]
    (G F₁ F₂ : C ⥤ D) (DG DF₁ DF₂ : C' ⥤ D')
    (eG : L ⋙ DG ⟶ G ⋙ J) (e₁ : L ⋙ DF₁ ⟶ F₁ ⋙ J)
    (e₂ : L ⋙ DF₂ ⟶ F₂ ⋙ J)
    (τ : ∀ P Q, G.obj (P ⊗ Q) ⟶ F₁.obj P ⊗ F₂.obj Q)
    (t : ∀ M N, DG.obj (M ⊗ N) ⟶ DF₁.obj M ⊗ DF₂.obj N) : Prop :=
  ∀ P Q, t (L.obj P) (L.obj Q) ≫
      (e₁.app P ⊗ₘ e₂.app Q) ≫ Functor.LaxMonoidal.μ J (F₁.obj P) (F₂.obj Q) =
    DG.map (Functor.LaxMonoidal.μ L P Q) ≫ eG.app (P ⊗ Q) ≫ J.map (τ P Q)

@[irreducible]
private def mapNormalization (L : C ⥤ C') (J : D ⥤ D') (K : E ⥤ E')
    (F : C ⥤ D) (H : D ⥤ E) (F₀ : C ⥤ E)
    (DF : C' ⥤ D') (DH : D' ⥤ E') (DF₀ : C' ⥤ E')
    (eF : L ⋙ DF ⟶ F ⋙ J) (eH : J ⋙ DH ⟶ H ⋙ K)
    (e₀ : L ⋙ DF₀ ⟶ F₀ ⋙ K) (a : F₀ ⟶ F ⋙ H) (da : DF₀ ⟶ DF ⋙ DH) : Prop :=
  ∀ P, da.app (L.obj P) ≫ DH.map (eF.app P) ≫ eH.app (F.obj P) =
    e₀.app P ≫ K.map (a.app P)

@[irreducible]
private def squareCondition [MonoidalCategory C] [MonoidalCategory D]
    [MonoidalCategory E]
    (G F₁ F₂ : C ⥤ D) (G₀ F₁₀ F₂₀ : C ⥤ E) (H : D ⥤ E)
    (τ : ∀ P Q, G.obj (P ⊗ Q) ⟶ F₁.obj P ⊗ F₂.obj Q)
    (τ₀ : ∀ P Q, G₀.obj (P ⊗ Q) ⟶ F₁₀.obj P ⊗ F₂₀.obj Q)
    (δ : ∀ P Q, H.obj (P ⊗ Q) ⟶ H.obj P ⊗ H.obj Q)
    (a₀ : G₀ ⟶ G ⋙ H) (a₁ : F₁₀ ⟶ F₁ ⋙ H) (a₂ : F₂₀ ⟶ F₂ ⋙ H) : Prop :=
  ∀ P Q, a₀.app (P ⊗ Q) ≫ H.map (τ P Q) ≫ δ (F₁.obj P) (F₂.obj Q) =
    τ₀ P Q ≫ (a₁.app P ⊗ₘ a₂.app Q)


end

section
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

-- Pass normalized transformations from homotopy models to cochain models.
private theorem derived_facQ_of_fach (α : F ⟶ G)
    (φ : F.mapDerivedCategory ⟶ G.mapDerivedCategory)
    (hφ : ∀ K : HomotopyCategory C (.up ℤ),
      φ.app (DerivedCategory.Qh.obj K) ≫ G.mapDerivedCategoryFactorsh.hom.app K =
        F.mapDerivedCategoryFactorsh.hom.app K ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory α (.up ℤ)).app K))
    (K : CochainComplex C ℤ) :
    φ.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategoryFactors.hom.app K =
      F.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (.up ℤ)).app K) := by
  have h := hφ ((HomotopyCategory.quotient _ _).obj K)
  rw [Functor.mapDerivedCategoryFactorsh_hom_app,
    Functor.mapDerivedCategoryFactorsh_hom_app] at h
  have hn := φ.naturality
    ((DerivedCategory.quotientCompQhIso C).hom.app K)
  rw [← Category.assoc] at h
  erw [← hn] at h
  simp only [Category.assoc] at h
  rw [cancel_epi] at h
  rw [← cancel_mono ((DerivedCategory.quotientCompQhIso D).inv.app
      ((G.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((G.mapHomotopyCategoryFactors (.up ℤ)).inv.app K))]
  rw [Category.assoc, h]
  change F.mapDerivedCategoryFactors.hom.app K ≫
      (DerivedCategory.quotientCompQhIso D).inv.app _ ≫
        DerivedCategory.Qh.map (𝟙 _) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex α (.up ℤ)).app K)) =
    (F.mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex α (.up ℤ)).app K)) ≫
      (DerivedCategory.quotientCompQhIso D).inv.app _ ≫ DerivedCategory.Qh.map (𝟙 _)
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Category.assoc]
  erw [Category.id_comp, Category.comp_id]
  congr 1
  exact ((DerivedCategory.quotientCompQhIso D).inv.naturality
    ((NatTrans.mapHomologicalComplex α (.up ℤ)).app K)).symm

end

namespace AlgebraicGeometry.Etale
private theorem projection_inv_eq
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [UpperStarPreservesFlat C] {P Q X : Scheme.{u}}
    (h : Q ⟶ P) (p : P ⟶ X) (q : Q ⟶ X) (hp : h ≫ p = q)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    (supportPullbackProjectionIso C h p q hp K).inv =
      (leftDerivedUpperStarIsoMapDerivedCategory C q).hom.app K ≫
      (Functor.mapDerivedCategoryNatIso
        (upperStarComp C h p q hp.symm)).hom.app K ≫
      (Functor.mapDerivedCategoryCompIso (upperStar C p)
        (upperStar C h)).hom.app K ≫
      (upperStar C h).mapDerivedCategory.map
        ((leftDerivedUpperStarIsoMapDerivedCategory C p).inv.app K) := by
  simp only [supportPullbackProjectionIso, leftDerivedUpperStarComp,
    leftDerivedUpperStarIsoMapDerivedCategory, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.symm_inv, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_hom, Iso.app_inv, Iso.app_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc]
  rw [Iso.inv_hom_id_app]
  erw [Category.comp_id]
end AlgebraicGeometry.Etale

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comp_facQ_of_fach
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (H : D ⥤ E) (F' : C ⥤ E)
    [F.Additive] [H.Additive] [F'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (α : F' ⟶ F ⋙ H)
    (φ : F'.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙ H.mapDerivedCategory)
    (hφ : ∀ K : HomotopyCategory C (.up ℤ),
      φ.app (DerivedCategory.Qh.obj K) ≫ H.mapDerivedCategory.map
          (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        H.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
      F'.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory α (.up ℤ)).app K))
    (K : CochainComplex C ℤ) :
    φ.app (DerivedCategory.Q.obj K) ≫ H.mapDerivedCategory.map
        (F.mapDerivedCategoryFactors.hom.app K) ≫
      H.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
    F'.mapDerivedCategoryFactors.hom.app K ≫
      DerivedCategory.Q.map (Functor.mapHomologicalComplexCompNatTrans F H F' α K) := by
  have : PreservesFiniteLimits (F ⋙ H) := inferInstance
  have : PreservesFiniteColimits (F ⋙ H) := inferInstance
  have h := derived_facQ_of_fach α (φ ≫ (Functor.mapDerivedCategoryCompIso F H).inv)
    (fun L ↦ by
      simp only [NatTrans.comp_app]
      rw [← Functor.mapDerivedCategoryCompIso_hom_app_factorsh F H L]
      simp only [Category.assoc]
      erw [Iso.inv_hom_id_app_assoc]
      exact hφ L) K
  simp only [NatTrans.comp_app] at h
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors F H K] at h
  simp only [Category.assoc] at h
  erw [Iso.inv_hom_id_app_assoc] at h
  have hc : Functor.mapHomologicalComplexCompNatTrans F H F' α K =
      (NatTrans.mapHomologicalComplex α (.up ℤ)).app K := by
    change _ ≫ 𝟙 _ = _
    exact Category.comp_id _
  rw [hc]
  exact h

namespace AlgebraicGeometry.Etale
private theorem square_inv_eq
    (C : Type v) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
    [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [UpperStarPreservesFlat C] {P Q X X' : Scheme.{u}}
    (h : Q ⟶ P) (p : P ⟶ X) (q : Q ⟶ X') (a : X' ⟶ X)
    (hp : h ≫ p = q ≫ a)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    (supportPullbackSquareIso C h p q a hp K).inv =
      (leftDerivedUpperStarIsoMapDerivedCategory C q).hom.app
        ((upperStar C a).mapDerivedCategory.obj K) ≫
      (Functor.mapDerivedCategorySquareIso
        (squareUpperStarIso C (CommSq.mk hp))).hom.app K ≫
      (upperStar C h).mapDerivedCategory.map
        ((leftDerivedUpperStarIsoMapDerivedCategory C p).inv.app K) := by
  simp only [supportPullbackSquareIso, leftDerivedUpperStarComp,
    leftDerivedUpperStarIsoMapDerivedCategory, Functor.leftDerivedFunctorNatIso,
    Functor.leftDerivedFunctorCompIso, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_hom, Iso.symm_inv, Iso.app_inv, Iso.app_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc]
  rw [Functor.mapIso_inv]
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory C q).hom.naturality
      ((leftDerivedUpperStarIsoMapDerivedCategory C a).inv.app K)
  erw [reassoc_of% hn]
  dsimp only [leftDerivedUpperStarIsoMapDerivedCategory]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  erw [Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  simp only [squareUpperStarIso, Functor.mapDerivedCategoryNatIso_trans,
    Functor.mapDerivedCategoryNatIso_symm, NatTrans.comp_app, Category.assoc]
end AlgebraicGeometry.Etale

section
variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Preadditive C] [Preadditive D] [Preadditive E]
  (F : C ⥤ D) (H : D ⥤ E) (F' : C ⥤ E)
  [F.Additive] [H.Additive] [F'.Additive] (a : F' ⟶ F ⋙ H)

private noncomputable def complexCompMap :
    F'.mapHomologicalComplex (.up ℤ) ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ H.mapHomologicalComplex (.up ℤ) :=
  NatTrans.mapHomologicalComplex a (.up ℤ) ≫
    (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ H)) (.up ℤ)).inv

private theorem complexCompMap_app (P : CochainComplex C ℤ) :
    (complexCompMap F H F' a).app P =
      Functor.mapHomologicalComplexCompNatTrans F H F' a P := rfl
end

section
variable {C D E : Type*} [Category C] [Category D] [Category E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  (F : C ⥤ D) (H : D ⥤ E) (F₀ : C ⥤ E)
  [F.Additive] [H.Additive] [F₀.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesFiniteLimits F₀] [PreservesFiniteColimits F₀]
@[irreducible]
private def mapNatNormalization (a : F₀ ⟶ F ⋙ H)
    (da : F₀.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙ H.mapDerivedCategory) : Prop :=
  mapNormalization DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    (F.mapHomologicalComplex (.up ℤ)) (H.mapHomologicalComplex (.up ℤ))
    (F₀.mapHomologicalComplex (.up ℤ)) F.mapDerivedCategory H.mapDerivedCategory
    F₀.mapDerivedCategory F.mapDerivedCategoryFactors.hom H.mapDerivedCategoryFactors.hom
    F₀.mapDerivedCategoryFactors.hom (complexCompMap F H F₀ a) da
end

private theorem comp_facQ_normalized_of_fach
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (F : C ⥤ D) (H : D ⥤ E) (F' : C ⥤ E)
    [F.Additive] [H.Additive] [F'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (α : F' ⟶ F ⋙ H)
    (φ : F'.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙ H.mapDerivedCategory)
    (hφ : ∀ K : HomotopyCategory C (.up ℤ),
      φ.app (DerivedCategory.Qh.obj K) ≫ H.mapDerivedCategory.map
          (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        H.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
      F'.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory α (.up ℤ)).app K))
 :
    mapNatNormalization F H F' α φ := by
  unfold mapNatNormalization mapNormalization
  intro K
  rw [complexCompMap_app]
  exact comp_facQ_of_fach F H F' α φ hφ K

section
variable {C D D' E E' : Type*}
  [Category C] [Category D] [Category D'] [Category E] [Category E']
  [Abelian C] [Abelian D] [Abelian D'] [Abelian E] [Abelian E']
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory D']
  [HasDerivedCategory E] [HasDerivedCategory E']
  (F : C ⥤ D) (F' : C ⥤ D') (a : D ⥤ D') (p : D ⥤ E)
  (q : D' ⥤ E') (h : E ⥤ E')
  [F.Additive] [F'.Additive] [a.Additive] [p.Additive] [q.Additive] [h.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
  [PreservesFiniteLimits a] [PreservesFiniteColimits a]
  [PreservesFiniteLimits p] [PreservesFiniteColimits p]
  [PreservesFiniteLimits q] [PreservesFiniteColimits q]
  [PreservesFiniteLimits h] [PreservesFiniteColimits h]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private noncomputable def squareCoefficient
    (sq : a ⋙ q ≅ p ⋙ h)
    (m : F'.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙ a.mapDerivedCategory) :
    (F' ⋙ q).mapDerivedCategory ⟶ (F ⋙ p).mapDerivedCategory ⋙ h.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F' q).hom ≫
    Functor.whiskerRight m q.mapDerivedCategory ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft F.mapDerivedCategory
      (Functor.mapDerivedCategorySquareIso sq).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Functor.mapDerivedCategoryCompIso F p).inv h.mapDerivedCategory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem square_facQ (sq : a ⋙ q ≅ p ⋙ h) (K : CochainComplex D ℤ) :
    (Functor.mapDerivedCategorySquareIso sq).hom.app (DerivedCategory.Q.obj K) ≫
        h.mapDerivedCategory.map (p.mapDerivedCategoryFactors.hom.app K) ≫
        h.mapDerivedCategoryFactors.hom.app ((p.mapHomologicalComplex (.up ℤ)).obj K) =
      q.mapDerivedCategory.map (a.mapDerivedCategoryFactors.hom.app K) ≫
        q.mapDerivedCategoryFactors.hom.app ((a.mapHomologicalComplex (.up ℤ)).obj K) ≫
        DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex sq.hom (.up ℤ)).app K) := by
  dsimp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors a q K]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]

omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory D'] [HasDerivedCategory E]
  [HasDerivedCategory E']
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [PreservesFiniteLimits F']
    [PreservesFiniteColimits F'] [PreservesFiniteLimits a] [PreservesFiniteColimits a]
    [PreservesFiniteLimits p] [PreservesFiniteColimits p] [PreservesFiniteLimits q]
    [PreservesFiniteColimits q] [PreservesFiniteLimits h] [PreservesFiniteColimits h] in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem squareCoefficient_complex
    (sq : a ⋙ q ≅ p ⋙ h) (α : F' ⟶ F ⋙ a) (K : CochainComplex C ℤ) :
    Functor.mapHomologicalComplexCompNatTrans (F ⋙ p) h (F' ⋙ q)
        (Functor.whiskerRight α q ≫ (Functor.associator F a q).hom ≫
          Functor.whiskerLeft F sq.hom ≫ (Functor.associator F p h).inv) K =
      (q.mapHomologicalComplex (.up ℤ)).map
          (Functor.mapHomologicalComplexCompNatTrans F a F' α K) ≫
        (NatTrans.mapHomologicalComplex sq.hom (.up ℤ)).app
          ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  ext n
  simp only [Functor.mapHomologicalComplexCompNatTrans_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, NatTrans.mapHomologicalComplex_app_f,
    NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem squareCoefficient_fac
    (sq : a ⋙ q ≅ p ⋙ h) (α : F' ⟶ F ⋙ a)
    (m : F'.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙ a.mapDerivedCategory)
    (hm : ∀ K : CochainComplex C ℤ,
      m.app (DerivedCategory.Q.obj K) ≫ a.mapDerivedCategory.map
          (F.mapDerivedCategoryFactors.hom.app K) ≫
        a.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      F'.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map (Functor.mapHomologicalComplexCompNatTrans F a F' α K))
    (K : CochainComplex C ℤ) :
    (squareCoefficient F F' a p q h sq m).app (DerivedCategory.Q.obj K) ≫
        h.mapDerivedCategory.map ((F ⋙ p).mapDerivedCategoryFactors.hom.app K) ≫
        h.mapDerivedCategoryFactors.hom.app
          (((F ⋙ p).mapHomologicalComplex (.up ℤ)).obj K) =
      (F' ⋙ q).mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
        ((q.mapHomologicalComplex (.up ℤ)).map
          (Functor.mapHomologicalComplexCompNatTrans F a F' α K) ≫
          (NatTrans.mapHomologicalComplex sq.hom (.up ℤ)).app
            ((F.mapHomologicalComplex (.up ℤ)).obj K)) := by
  dsimp only [squareCoefficient, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp, Category.assoc]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors F p K]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← h.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  have hn := (Functor.mapDerivedCategorySquareIso sq).hom.naturality
    (F.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn]
  erw [square_facQ a p q h sq]
  have hqm := congrArg q.mapDerivedCategory.map (hm K)
  simp only [CategoryTheory.Functor.map_comp] at hqm
  erw [reassoc_of% hqm]
  erw [q.mapDerivedCategoryFactors_hom_naturality_assoc]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]

private theorem squareCoefficient_facCached
    (sq : a ⋙ q ≅ p ⋙ h) (α : F' ⟶ F ⋙ a)
    (m : F'.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙ a.mapDerivedCategory)
    (hm : ∀ K : CochainComplex C ℤ,
      m.app (DerivedCategory.Q.obj K) ≫ a.mapDerivedCategory.map
          (F.mapDerivedCategoryFactors.hom.app K) ≫
        a.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      F'.mapDerivedCategoryFactors.hom.app K ≫
        DerivedCategory.Q.map (Functor.mapHomologicalComplexCompNatTrans F a F' α K))
    (K : CochainComplex C ℤ) :
    (squareCoefficient F F' a p q h sq m).app (DerivedCategory.Q.obj K) ≫
        h.mapDerivedCategory.map ((F ⋙ p).mapDerivedCategoryFactors.hom.app K) ≫
        h.mapDerivedCategoryFactors.hom.app
          (((F ⋙ p).mapHomologicalComplex (.up ℤ)).obj K) =
      (F' ⋙ q).mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
        ((complexCompMap (F ⋙ p) h (F' ⋙ q)
          (Functor.whiskerRight α q ≫ (Functor.associator F a q).hom ≫
            Functor.whiskerLeft F sq.hom ≫ (Functor.associator F p h).inv)).app K) := by
  rw [complexCompMap_app, squareCoefficient_complex]
  exact squareCoefficient_fac F F' a p q h sq α m hm K

private theorem squareCoefficient_normalized
    (sq : a ⋙ q ≅ p ⋙ h) (α : F' ⟶ F ⋙ a)
    (m : F'.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙ a.mapDerivedCategory)
    (hm : mapNatNormalization F a F' α m) :
    mapNatNormalization (F ⋙ p) h (F' ⋙ q)
      (Functor.whiskerRight α q ≫ (Functor.associator F a q).hom ≫
        Functor.whiskerLeft F sq.hom ≫ (Functor.associator F p h).inv)
      (squareCoefficient F F' a p q h sq m) := by
  unfold mapNatNormalization mapNormalization at hm ⊢
  simp only [complexCompMap_app] at hm
  exact squareCoefficient_facCached F F' a p q h sq α m hm

private theorem squareCoefficient_normalized_of_fach
    (sq : a ⋙ q ≅ p ⋙ h) (α : F' ⟶ F ⋙ a)
    (m : F'.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙ a.mapDerivedCategory)
    (hm : ∀ K : HomotopyCategory C (.up ℤ),
      m.app (DerivedCategory.Qh.obj K) ≫ a.mapDerivedCategory.map
          (F.mapDerivedCategoryFactorsh.hom.app K) ≫
        a.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K) =
      F'.mapDerivedCategoryFactorsh.hom.app K ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory α (.up ℤ)).app K)) :
    mapNatNormalization (F ⋙ p) h (F' ⋙ q)
      (Functor.whiskerRight α q ≫ (Functor.associator F a q).hom ≫
        Functor.whiskerLeft F sq.hom ≫ (Functor.associator F p h).inv)
      (squareCoefficient F F' a p q h sq m) :=
  squareCoefficient_normalized F F' a p q h sq α m
    (comp_facQ_normalized_of_fach F a F' α m hm)

end

section
variable {C D E E' : Type*}
  [Category C] [Category D] [Category E] [Category E']
  [Abelian C] [Abelian D] [Abelian E] [Abelian E']
  [HasDerivedCategory C] [HasDerivedCategory D]
  [HasDerivedCategory E] [HasDerivedCategory E']
  (F : C ⥤ D) (p : D ⥤ E) (q : D ⥤ E') (h : E ⥤ E')
  [F.Additive] [p.Additive] [q.Additive] [h.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits p] [PreservesFiniteColimits p]
  [PreservesFiniteLimits q] [PreservesFiniteColimits q]
  [PreservesFiniteLimits h] [PreservesFiniteColimits h]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private noncomputable def projectionCoefficient (sq : q ≅ p ⋙ h) :
    (F ⋙ q).mapDerivedCategory ⟶ (F ⋙ p).mapDerivedCategory ⋙ h.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso F q).hom ≫
    Functor.whiskerLeft F.mapDerivedCategory
      ((Functor.mapDerivedCategoryNatIso sq).hom ≫
        (Functor.mapDerivedCategoryCompIso p h).hom) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Functor.mapDerivedCategoryCompIso F p).inv h.mapDerivedCategory

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem projectionCoefficient_fac (sq : q ≅ p ⋙ h) (K : CochainComplex C ℤ) :
    (projectionCoefficient F p q h sq).app (DerivedCategory.Q.obj K) ≫
        h.mapDerivedCategory.map ((F ⋙ p).mapDerivedCategoryFactors.hom.app K) ≫
        h.mapDerivedCategoryFactors.hom.app
          (((F ⋙ p).mapHomologicalComplex (.up ℤ)).obj K) =
      (F ⋙ q).mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex sq.hom (.up ℤ)).app
          ((F.mapHomologicalComplex (.up ℤ)).obj K)) := by
  dsimp only [projectionCoefficient, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_inv_app]
  simp only [Category.id_comp, Category.assoc]
  rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors F p K]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← h.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := (Functor.mapDerivedCategoryNatIso sq).hom.naturality
    (F.mapDerivedCategoryFactors.hom.app K)
  have hc := (Functor.mapDerivedCategoryCompIso p h).hom.naturality
    (F.mapDerivedCategoryFactors.hom.app K)
  dsimp only [Functor.comp_map] at hc
  erw [← reassoc_of% hc, ← reassoc_of% hn]
  erw [Functor.mapDerivedCategoryCompIso_hom_app_factors p h
    ((F.mapHomologicalComplex (.up ℤ)).obj K)]
  erw [Functor.mapDerivedCategoryNatIso_fac sq
    ((F.mapHomologicalComplex (.up ℤ)).obj K)]
  rw [Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
omit [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E] [HasDerivedCategory E']
  [PreservesFiniteLimits F] [PreservesFiniteColimits F] [PreservesFiniteLimits p]
    [PreservesFiniteColimits p] [PreservesFiniteLimits q] [PreservesFiniteColimits q]
    [PreservesFiniteLimits h] [PreservesFiniteColimits h] in
private theorem projectionCoefficient_complex (sq : q ≅ p ⋙ h) (K : CochainComplex C ℤ) :
    Functor.mapHomologicalComplexCompNatTrans (F ⋙ p) h (F ⋙ q)
        (Functor.whiskerLeft F sq.hom ≫ (Functor.associator F p h).inv) K =
      (NatTrans.mapHomologicalComplex sq.hom (.up ℤ)).app
        ((F.mapHomologicalComplex (.up ℤ)).obj K) := by
  ext n
  simp only [Functor.mapHomologicalComplexCompNatTrans_f,
    NatTrans.mapHomologicalComplex_app_f,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Category.comp_id]
  rfl
private theorem projectionCoefficient_facCached (sq : q ≅ p ⋙ h) (K : CochainComplex C ℤ) :
    (projectionCoefficient F p q h sq).app (DerivedCategory.Q.obj K) ≫
        h.mapDerivedCategory.map ((F ⋙ p).mapDerivedCategoryFactors.hom.app K) ≫
        h.mapDerivedCategoryFactors.hom.app
          (((F ⋙ p).mapHomologicalComplex (.up ℤ)).obj K) =
      (F ⋙ q).mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map
        ((complexCompMap (F ⋙ p) h (F ⋙ q)
          (Functor.whiskerLeft F sq.hom ≫ (Functor.associator F p h).inv)).app K) := by
  rw [complexCompMap_app, projectionCoefficient_complex]
  exact projectionCoefficient_fac F p q h sq K

private theorem projectionCoefficient_normalized (sq : q ≅ p ⋙ h) :
    mapNatNormalization (F ⋙ p) h (F ⋙ q)
      (Functor.whiskerLeft F sq.hom ≫ (Functor.associator F p h).inv)
      (projectionCoefficient F p q h sq) := by
  unfold mapNatNormalization mapNormalization
  exact projectionCoefficient_facCached F p q h sq

end

section
variable {C D : Type*} [Category.{w} C] [Category.{w} D] [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{w} C] [IsGrothendieckAbelian.{w} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [SymmetricCategory C] [SymmetricCategory D] [MonoidalClosed C] [MonoidalClosed D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]

/-- Keep the complex and localization tensor structures behind a base-category interface. -/
@[irreducible]
private def tensorNatNormalization
    (τ : (Functor.postcompose₂.obj (G.mapHomologicalComplex (.up ℤ))).obj
      (curriedTensor (CochainComplex C ℤ)) ⟶
      (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ))).obj
        (F₂.mapHomologicalComplex (.up ℤ))).obj (curriedTensor _))
    (t : (Functor.postcompose₂.obj G.mapDerivedCategory).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁.mapDerivedCategory).obj
        F₂.mapDerivedCategory).obj (curriedTensor _)) : Prop :=
  tensorNormalization DerivedCategory.Q DerivedCategory.Q
    (G.mapHomologicalComplex (.up ℤ)) (F₁.mapHomologicalComplex (.up ℤ))
    (F₂.mapHomologicalComplex (.up ℤ))
    G.mapDerivedCategory F₁.mapDerivedCategory F₂.mapDerivedCategory
    G.mapDerivedCategoryFactors.hom F₁.mapDerivedCategoryFactors.hom
    F₂.mapDerivedCategoryFactors.hom
    (fun P Q ↦ (τ.app P).app Q) (fun M N ↦ (t.app M).app N)
end

section
variable {C D E : Type*} [Category.{w + 1} C] [Category.{w + 1} D]
  [Category.{w + 1} E] [Abelian C] [Abelian D] [Abelian E]
  [IsGrothendieckAbelian.{w + 1} C] [IsGrothendieckAbelian.{w + 1} D]
  [IsGrothendieckAbelian.{w + 1} E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [MonoidalPreadditive E]
  [SymmetricCategory C] [SymmetricCategory D] [SymmetricCategory E]
  [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosed E]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [Abelian.HasFunctorialFlatResolution E]
  [HasDerivedCategory.{w + 1} C] [HasDerivedCategory.{w + 1} D]
  [HasDerivedCategory.{w + 1} E]
  (F₁ F₂ : C ⥤ D) (H : D ⥤ E) [F₁.Additive] [F₂.Additive] [H.Additive]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem compositeTensor_ext [(F₂ ⋙ H).PreservesFlat] [(F₂ ⋙ H).IsLeftAdjoint]
    (G : DerivedCategory C ⥤ DerivedCategory C ⥤ DerivedCategory E)
    (γ₁ γ₂ : G ⟶
      (((Functor.whiskeringLeft₂ _).obj (F₁.mapDerivedCategory ⋙ H.mapDerivedCategory)).obj
        (F₂.mapDerivedCategory ⋙ H.mapDerivedCategory)).obj (curriedTensor _))
    (hγ : ∀ P Q : CochainComplex C ℤ,
      (γ₁.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q) ≫
        ((H.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app P) ≫
          H.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P)) ⊗ₘ
         (H.mapDerivedCategory.map (F₂.mapDerivedCategoryFactors.hom.app Q) ≫
          H.mapDerivedCategoryFactors.hom.app ((F₂.mapHomologicalComplex (.up ℤ)).obj Q))) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((H.mapHomologicalComplex (.up ℤ)).obj ((F₁.mapHomologicalComplex (.up ℤ)).obj P))
          ((H.mapHomologicalComplex (.up ℤ)).obj ((F₂.mapHomologicalComplex (.up ℤ)).obj Q)) =
      (γ₂.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q) ≫
        ((H.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app P) ≫
          H.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P)) ⊗ₘ
         (H.mapDerivedCategory.map (F₂.mapDerivedCategoryFactors.hom.app Q) ≫
          H.mapDerivedCategoryFactors.hom.app ((F₂.mapHomologicalComplex (.up ℤ)).obj Q))) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((H.mapHomologicalComplex (.up ℤ)).obj ((F₁.mapHomologicalComplex (.up ℤ)).obj P))
          ((H.mapHomologicalComplex (.up ℤ)).obj ((F₂.mapHomologicalComplex (.up ℤ)).obj Q))) :
    γ₁ = γ₂ := by
  apply Localization.natTrans₂_ext DerivedCategory.Q DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ)) (HomologicalComplex.quasiIso C (.up ℤ))
  intro P Q
  let Λ := (inferInstance : Abelian.HasFunctorialFlatResolution C).some.reduced
  let R := Λ.resolutionFunctor.obj Q
  let s := DerivedCategory.Q.map (Λ.resolutionNatTrans.app Q)
  have hs : (HomologicalComplex.quasiIso C (.up ℤ)) (Λ.resolutionNatTrans.app Q) := by
    rw [HomologicalComplex.mem_quasiIso_iff]
    exact Λ.quasiIso_resolutionNatTrans_app Q
  have : IsIso s := (Localization.inverts DerivedCategory.Q
    (HomologicalComplex.quasiIso C (.up ℤ))) _ hs
  have hR : (γ₁.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj R) =
      (γ₂.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj R) := by
    have hflat := (F₂ ⋙ H).kFlat_mapHomologicalComplex_obj_resolutionFunctor_obj
      Λ ObjectProperty.flat.essImage_ι_le Q
    have : IsIso (Functor.LaxMonoidal.μ DerivedCategory.Q
        ((H.mapHomologicalComplex (.up ℤ)).obj ((F₁.mapHomologicalComplex (.up ℤ)).obj P))
        ((H.mapHomologicalComplex (.up ℤ)).obj ((F₂.mapHomologicalComplex (.up ℤ)).obj R))) :=
      AlgebraicGeometry.Etale.tensorLocalization_isIso _ _ hflat
    have h := hγ P R
    exact (cancel_mono _).1 h
  apply (cancel_epi ((G.obj (DerivedCategory.Q.obj P)).map s)).1
  erw [(γ₁.app (DerivedCategory.Q.obj P)).naturality s,
    (γ₂.app (DerivedCategory.Q.obj P)).naturality s]
  exact congrArg (fun k ↦ k ≫ _) hR

end

private theorem model_square
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalCategory C'] [MonoidalCategory D'] [MonoidalCategory E']
    (L : C ⥤ C') (J : D ⥤ D') (K : E ⥤ E')
    [L.LaxMonoidal] [J.LaxMonoidal] [K.LaxMonoidal]
    (G F₁ F₂ : C ⥤ D) (G₀ F₁₀ F₂₀ : C ⥤ E) (H : D ⥤ E)
    (DG DF₁ DF₂ : C' ⥤ D') (DG₀ DF₁₀ DF₂₀ : C' ⥤ E') (DH : D' ⥤ E')
    (eG : L ⋙ DG ⟶ G ⋙ J) (eF₁ : L ⋙ DF₁ ⟶ F₁ ⋙ J)
    (eF₂ : L ⋙ DF₂ ⟶ F₂ ⋙ J) (eG₀ : L ⋙ DG₀ ⟶ G₀ ⋙ K)
    (eF₁₀ : L ⋙ DF₁₀ ⟶ F₁₀ ⋙ K) (eF₂₀ : L ⋙ DF₂₀ ⟶ F₂₀ ⋙ K)
    (eH : J ⋙ DH ⟶ H ⋙ K)
    (τ : ∀ P Q, G.obj (P ⊗ Q) ⟶ F₁.obj P ⊗ F₂.obj Q)
    (τ₀ : ∀ P Q, G₀.obj (P ⊗ Q) ⟶ F₁₀.obj P ⊗ F₂₀.obj Q)
    (t : ∀ M N, DG.obj (M ⊗ N) ⟶ DF₁.obj M ⊗ DF₂.obj N)
    (t₀ : ∀ M N, DG₀.obj (M ⊗ N) ⟶ DF₁₀.obj M ⊗ DF₂₀.obj N)
    (δ : (Functor.postcompose₂.obj DH).obj (curriedTensor D') ⟶
      (((Functor.whiskeringLeft₂ E').obj DH).obj DH).obj (curriedTensor E'))
    (δc : ∀ P Q, H.obj (P ⊗ Q) ⟶ H.obj P ⊗ H.obj Q)
    (a₀ : G₀ ⟶ G ⋙ H) (a₁ : F₁₀ ⟶ F₁ ⋙ H) (a₂ : F₂₀ ⟶ F₂ ⋙ H)
    (da₀ : DG₀ ⟶ DG ⋙ DH) (da₁ : DF₁₀ ⟶ DF₁ ⋙ DH)
    (da₂ : DF₂₀ ⟶ DF₂ ⋙ DH)
    (ht : ∀ P Q, t (L.obj P) (L.obj Q) ≫
        (eF₁.app P ⊗ₘ eF₂.app Q) ≫ Functor.LaxMonoidal.μ J (F₁.obj P) (F₂.obj Q) =
      DG.map (Functor.LaxMonoidal.μ L P Q) ≫ eG.app (P ⊗ Q) ≫ J.map (τ P Q))
    (ht₀ : ∀ P Q, t₀ (L.obj P) (L.obj Q) ≫
        (eF₁₀.app P ⊗ₘ eF₂₀.app Q) ≫ Functor.LaxMonoidal.μ K (F₁₀.obj P) (F₂₀.obj Q) =
      DG₀.map (Functor.LaxMonoidal.μ L P Q) ≫ eG₀.app (P ⊗ Q) ≫ K.map (τ₀ P Q))
    (hδ : ∀ P Q, (δ.app (J.obj P)).app (J.obj Q) ≫
        (eH.app P ⊗ₘ eH.app Q) ≫ Functor.LaxMonoidal.μ K (H.obj P) (H.obj Q) =
      DH.map (Functor.LaxMonoidal.μ J P Q) ≫ eH.app (P ⊗ Q) ≫ K.map (δc P Q))
    (ha₀ : ∀ P, da₀.app (L.obj P) ≫ DH.map (eG.app P) ≫ eH.app (G.obj P) =
      eG₀.app P ≫ K.map (a₀.app P))
    (ha₁ : ∀ P, da₁.app (L.obj P) ≫ DH.map (eF₁.app P) ≫ eH.app (F₁.obj P) =
      eF₁₀.app P ≫ K.map (a₁.app P))
    (ha₂ : ∀ P, da₂.app (L.obj P) ≫ DH.map (eF₂.app P) ≫ eH.app (F₂.obj P) =
      eF₂₀.app P ≫ K.map (a₂.app P))
    (hs : ∀ P Q, a₀.app (P ⊗ Q) ≫ H.map (τ P Q) ≫ δc (F₁.obj P) (F₂.obj Q) =
      τ₀ P Q ≫ (a₁.app P ⊗ₘ a₂.app Q)) (P Q : C) :
    (da₀.app (L.obj P ⊗ L.obj Q) ≫ DH.map (t (L.obj P) (L.obj Q)) ≫
        (δ.app (DF₁.obj (L.obj P))).app (DF₂.obj (L.obj Q))) ≫
      ((DH.map (eF₁.app P) ≫ eH.app (F₁.obj P)) ⊗ₘ
        (DH.map (eF₂.app Q) ≫ eH.app (F₂.obj Q))) ≫
      Functor.LaxMonoidal.μ K (H.obj (F₁.obj P)) (H.obj (F₂.obj Q)) =
    (t₀ (L.obj P) (L.obj Q) ≫ (da₁.app (L.obj P) ⊗ₘ da₂.app (L.obj Q))) ≫
      ((DH.map (eF₁.app P) ≫ eH.app (F₁.obj P)) ⊗ₘ
        (DH.map (eF₂.app Q) ≫ eH.app (F₂.obj Q))) ≫
      Functor.LaxMonoidal.μ K (H.obj (F₁.obj P)) (H.obj (F₂.obj Q)) := by
  have hδn := congr_app (δ.naturality (eF₁.app P)) (DF₂.obj (L.obj Q))
  have hδn' := (δ.app (J.obj (F₁.obj P))).naturality (eF₂.app Q)
  change DH.map (eF₁.app P ▷ DF₂.obj (L.obj Q)) ≫
      (δ.app (J.obj (F₁.obj P))).app (DF₂.obj (L.obj Q)) =
    (δ.app (DF₁.obj (L.obj P))).app (DF₂.obj (L.obj Q)) ≫
      (DH.map (eF₁.app P) ▷ DH.obj (DF₂.obj (L.obj Q))) at hδn
  change DH.map (J.obj (F₁.obj P) ◁ eF₂.app Q) ≫
      (δ.app (J.obj (F₁.obj P))).app (J.obj (F₂.obj Q)) =
    (δ.app (J.obj (F₁.obj P))).app (DF₂.obj (L.obj Q)) ≫
      (DH.obj (J.obj (F₁.obj P)) ◁ DH.map (eF₂.app Q)) at hδn'
  have hn : DH.map (eF₁.app P ⊗ₘ eF₂.app Q) ≫
        (δ.app (J.obj (F₁.obj P))).app (J.obj (F₂.obj Q)) =
      (δ.app (DF₁.obj (L.obj P))).app (DF₂.obj (L.obj Q)) ≫
        (DH.map (eF₁.app P) ⊗ₘ DH.map (eF₂.app Q)) := by
    rw [MonoidalCategory.tensorHom_def, CategoryTheory.Functor.map_comp, Category.assoc]
    erw [hδn',
      ← Category.assoc, hδn, Category.assoc, ← MonoidalCategory.tensorHom_def]
  simp only [Category.assoc, ← tensorHom_comp_tensorHom]
  rw [← reassoc_of% hn, hδ]
  have htn := congrArg DH.map (ht P Q)
  simp only [CategoryTheory.Functor.map_comp] at htn
  erw [reassoc_of% htn]
  erw [reassoc_of% (eH.naturality (τ P Q))]
  erw [← reassoc_of% (da₀.naturality (Functor.LaxMonoidal.μ L P Q))]
  rw [reassoc_of% ha₀]
  have hsk := congrArg K.map (hs P Q)
  simp only [CategoryTheory.Functor.map_comp] at hsk
  erw [hsk]
  rw [← reassoc_of% ht₀, ← Functor.LaxMonoidal.μ_natural]
  erw [tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc,
    tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc]
  rw [ha₁, ha₂]
  rfl

section
variable {C D E : Type*} [Category C] [Category D] [Category E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]

private def comparisonNatTrans (G F₁ F₂ : C ⥤ D)
    (t : ∀ M N, G.obj (M ⊗ N) ⟶ F₁.obj M ⊗ F₂.obj N)
    (ht : ∀ M M' N N' (a : M ⟶ M') (b : N ⟶ N'),
      G.map (a ⊗ₘ b) ≫ t M' N' = t M N ≫ (F₁.map a ⊗ₘ F₂.map b)) :
    (Functor.postcompose₂.obj G).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj (curriedTensor _) where
  app M :=
    { app N := t M N
      naturality N N' b := by
        change G.map (M ◁ b) ≫ t M N' = t M N ≫ (F₁.obj M ◁ F₂.map b)
        simpa only [id_tensorHom, CategoryTheory.Functor.map_id] using
          ht M M N N' (𝟙 M) b }
  naturality M M' a := by
    apply NatTrans.ext
    funext N
    change G.map (a ▷ N) ≫ t M' N = t M N ≫ (F₁.map a ▷ F₂.obj N)
    simpa only [tensorHom_id, CategoryTheory.Functor.map_id] using
      ht M M' N N a (𝟙 N)

private def squareLeft
    (G F₁ F₂ : C ⥤ D) (G₀ : C ⥤ E) (H : D ⥤ E)
    (a₀ : G₀ ⟶ G ⋙ H)
    (t : (Functor.postcompose₂.obj G).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj (curriedTensor _))
    (δ : (Functor.postcompose₂.obj H).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj H).obj H).obj (curriedTensor _)) :
    (Functor.postcompose₂.obj G₀).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj (F₁ ⋙ H)).obj (F₂ ⋙ H)).obj
        (curriedTensor _) :=
  (Functor.postcompose₂.map a₀).app (curriedTensor _) ≫
    (Functor.postcompose₂.obj H).map t ≫
    (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).map δ

private def squareRight
    (G₀ F₁₀ F₂₀ F₁ F₂ : C ⥤ E)
    (a₁ : F₁₀ ⟶ F₁) (a₂ : F₂₀ ⟶ F₂)
    (t₀ : (Functor.postcompose₂.obj G₀).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁₀).obj F₂₀).obj (curriedTensor _)) :
    (Functor.postcompose₂.obj G₀).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj (curriedTensor _) :=
  t₀ ≫ (((Functor.whiskeringLeft₂ _).map a₁).app F₂₀).app (curriedTensor _) ≫
    (((Functor.whiskeringLeft₂ _).obj F₁).map a₂).app (curriedTensor _)

private theorem squareLeft_app
    (G F₁ F₂ : C ⥤ D) (G₀ : C ⥤ E) (H : D ⥤ E)
    (a₀ : G₀ ⟶ G ⋙ H)
    (t : (Functor.postcompose₂.obj G).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj (curriedTensor _))
    (δ : (Functor.postcompose₂.obj H).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj H).obj H).obj (curriedTensor _)) (M N : C) :
    ((squareLeft G F₁ F₂ G₀ H a₀ t δ).app M).app N =
      a₀.app (M ⊗ N) ≫ H.map ((t.app M).app N) ≫ (δ.app (F₁.obj M)).app (F₂.obj N) := by
  simp only [squareLeft, NatTrans.comp_app]
  rfl

private theorem squareRight_app
    (G₀ F₁₀ F₂₀ F₁ F₂ : C ⥤ E)
    (a₁ : F₁₀ ⟶ F₁) (a₂ : F₂₀ ⟶ F₂)
    (t₀ : (Functor.postcompose₂.obj G₀).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁₀).obj F₂₀).obj (curriedTensor _)) (M N : C) :
    ((squareRight G₀ F₁₀ F₂₀ F₁ F₂ a₁ a₂ t₀).app M).app N =
      (t₀.app M).app N ≫ (a₁.app M ⊗ₘ a₂.app N) := by
  simp only [squareRight, NatTrans.comp_app, MonoidalCategory.tensorHom_def]
  rfl
end

private theorem square_equality_app
    {C D E : Type*} [Category C] [Category D] [Category E]
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    (G F₁ F₂ : C ⥤ D) (G₀ F₁₀ F₂₀ : C ⥤ E) (H : D ⥤ E)
    (a₀ : G₀ ⟶ G ⋙ H) (a₁ : F₁₀ ⟶ F₁ ⋙ H) (a₂ : F₂₀ ⟶ F₂ ⋙ H)
    (t : (Functor.postcompose₂.obj G).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj (curriedTensor _))
    (t₀ : (Functor.postcompose₂.obj G₀).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁₀).obj F₂₀).obj (curriedTensor _))
    (δ : (Functor.postcompose₂.obj H).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj H).obj H).obj (curriedTensor _))
    (he : squareLeft G F₁ F₂ G₀ H a₀ t δ =
      squareRight G₀ F₁₀ F₂₀ (F₁ ⋙ H) (F₂ ⋙ H) a₁ a₂ t₀) (M N : C) :
    a₀.app (M ⊗ N) ≫ H.map ((t.app M).app N) ≫
        (δ.app (F₁.obj M)).app (F₂.obj N) =
      (t₀.app M).app N ≫ (a₁.app M ⊗ₘ a₂.app N) := by
  have h := congr_app (congr_app he M) N
  rw [squareLeft_app, squareRight_app] at h
  exact h

section
variable {C : Type v₁} {D : Type v₂} [Category.{w + 1} C] [Category.{w + 1} D]
  [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{w + 1} C] [IsGrothendieckAbelian.{w + 1} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [SymmetricCategory C] [SymmetricCategory D] [MonoidalClosed C] [MonoidalClosed D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [HasDerivedCategory.{w + 1} C] [HasDerivedCategory.{w + 1} D]
  (G F₁ F₂ : C ⥤ D) [G.Additive] [F₁.Additive] [F₂.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  (τ : (Functor.postcompose₂.obj (G.mapHomologicalComplex (.up ℤ))).obj
    (curriedTensor (CochainComplex C ℤ)) ⟶
    (((Functor.whiskeringLeft₂ _).obj (F₁.mapHomologicalComplex (.up ℤ))).obj
      (F₂.mapHomologicalComplex (.up ℤ))).obj (curriedTensor _))
  (t : AlgebraicGeometry.Etale.supportedDerivedComparisonHom G F₁ F₂)
  (ht : AlgebraicGeometry.Etale.supportedDerivedComparisonCondition G F₁ F₂ τ t)
private noncomputable def comparisonFromCondition :=
  comparisonNatTrans G.mapDerivedCategory F₁.mapDerivedCategory F₂.mapDerivedCategory t ht.1
private theorem comparisonFromCondition_normalized :
    tensorNatNormalization G F₁ F₂ τ
      (comparisonFromCondition G F₁ F₂ τ t ht) := by
  unfold tensorNatNormalization tensorNormalization
  intro P Q
  have h := ht.2 P Q
  have hi : eqToHom (AlgebraicGeometry.Etale.supportedComplexTensor_eq
      ((F₁.mapHomologicalComplex (.up ℤ)).obj P)
      ((F₂.mapHomologicalComplex (.up ℤ)).obj Q)) = 𝟙 _ := rfl
  rw [hi, CategoryTheory.Functor.map_id, Category.comp_id] at h
  exact h.symm

end

section
variable {C D C' D' : Type*} [Category C] [Category D] [Category C'] [Category D']
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory C'] [MonoidalCategory D']

private def conjugateTensor (H H' : C' ⥤ D') (e : H ≅ H')
    (δ : (Functor.postcompose₂.obj H).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj H).obj H).obj (curriedTensor _)) :
    (Functor.postcompose₂.obj H').obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj H').obj H').obj (curriedTensor _) :=
  (Functor.postcompose₂.map e.inv).app (curriedTensor _) ≫ δ ≫
    (((Functor.whiskeringLeft₂ _).map e.hom).app H).app (curriedTensor _) ≫
    (((Functor.whiskeringLeft₂ _).obj H').map e.hom).app (curriedTensor _)

private theorem conjugateTensor_app (H H' : C' ⥤ D') (e : H ≅ H')
    (δ : (Functor.postcompose₂.obj H).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj H).obj H).obj (curriedTensor _)) (M N : C') :
    ((conjugateTensor H H' e δ).app M).app N =
      e.inv.app (M ⊗ N) ≫ (δ.app M).app N ≫ (e.hom.app M ⊗ₘ e.hom.app N) := by
  simp only [conjugateTensor, NatTrans.comp_app, MonoidalCategory.tensorHom_def]
  rfl

private theorem conjugateTensor_fac
    (J : C ⥤ C') (K : D ⥤ D') [J.LaxMonoidal] [K.LaxMonoidal]
    (F : C ⥤ D) (H H' : C' ⥤ D') (e : H ≅ H')
    (a : J ⋙ H ⟶ F ⋙ K) (a' : J ⋙ H' ⟶ F ⋙ K)
    (he : ∀ P, e.hom.app (J.obj P) ≫ a'.app P = a.app P)
    (δ : (Functor.postcompose₂.obj H).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj H).obj H).obj (curriedTensor _))
    (δc : ∀ P Q, F.obj (P ⊗ Q) ⟶ F.obj P ⊗ F.obj Q)
    (hδ : ∀ P Q, (δ.app (J.obj P)).app (J.obj Q) ≫
        (a.app P ⊗ₘ a.app Q) ≫ Functor.LaxMonoidal.μ K (F.obj P) (F.obj Q) =
      H.map (Functor.LaxMonoidal.μ J P Q) ≫ a.app (P ⊗ Q) ≫ K.map (δc P Q))
    (P Q : C) :
    ((conjugateTensor H H' e δ).app (J.obj P)).app (J.obj Q) ≫
        (a'.app P ⊗ₘ a'.app Q) ≫ Functor.LaxMonoidal.μ K (F.obj P) (F.obj Q) =
      H'.map (Functor.LaxMonoidal.μ J P Q) ≫ a'.app (P ⊗ Q) ≫ K.map (δc P Q) := by
  rw [conjugateTensor_app]
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc]
  rw [he P, he Q, hδ]
  rw [← reassoc_of% (e.inv.naturality (Functor.LaxMonoidal.μ J P Q))]
  rw [← he (P ⊗ Q)]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]

private theorem tensorNormalization_transport
    (J J' : C ⥤ C') (K K' : D ⥤ D')
    [J.LaxMonoidal] [J'.LaxMonoidal] [K.LaxMonoidal] [K'.LaxMonoidal]
    (eJ : J ≅ J') (eK : K ≅ K')
    (hJ : ∀ P Q, Functor.LaxMonoidal.μ J P Q ≫ eJ.hom.app (P ⊗ Q) =
      (eJ.hom.app P ⊗ₘ eJ.hom.app Q) ≫ Functor.LaxMonoidal.μ J' P Q)
    (hK : ∀ P Q, Functor.LaxMonoidal.μ K P Q ≫ eK.hom.app (P ⊗ Q) =
      (eK.hom.app P ⊗ₘ eK.hom.app Q) ≫ Functor.LaxMonoidal.μ K' P Q)
    (F : C ⥤ D) (H : C' ⥤ D')
    (a : ∀ P, H.obj (J.obj P) ⟶ K.obj (F.obj P))
    (a' : ∀ P, H.obj (J'.obj P) ⟶ K'.obj (F.obj P))
    (ha : ∀ P, H.map (eJ.hom.app P) ≫ a' P = a P ≫ eK.hom.app (F.obj P))
    (δ : (Functor.postcompose₂.obj H).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj H).obj H).obj (curriedTensor _))
    (δc : ∀ P Q, F.obj (P ⊗ Q) ⟶ F.obj P ⊗ F.obj Q)
    (hδ : ∀ P Q, (δ.app (J.obj P)).app (J.obj Q) ≫
        (a P ⊗ₘ a Q) ≫ Functor.LaxMonoidal.μ K (F.obj P) (F.obj Q) =
      H.map (Functor.LaxMonoidal.μ J P Q) ≫ a (P ⊗ Q) ≫ K.map (δc P Q))
    (P Q : C) :
    (δ.app (J'.obj P)).app (J'.obj Q) ≫
        (a' P ⊗ₘ a' Q) ≫ Functor.LaxMonoidal.μ K' (F.obj P) (F.obj Q) =
      H.map (Functor.LaxMonoidal.μ J' P Q) ≫ a' (P ⊗ Q) ≫ K'.map (δc P Q) := by
  apply (cancel_epi (H.map (eJ.hom.app P ⊗ₘ eJ.hom.app Q))).1
  have hn₁ := congr_app (δ.naturality (eJ.hom.app P)) (J.obj Q)
  have hn₂ := (δ.app (J'.obj P)).naturality (eJ.hom.app Q)
  change H.map (eJ.hom.app P ▷ J.obj Q) ≫ _ = _ at hn₁
  change H.map (J'.obj P ◁ eJ.hom.app Q) ≫ _ = _ at hn₂
  have hn : H.map (eJ.hom.app P ⊗ₘ eJ.hom.app Q) ≫
        (δ.app (J'.obj P)).app (J'.obj Q) =
      (δ.app (J.obj P)).app (J.obj Q) ≫
        (H.map (eJ.hom.app P) ⊗ₘ H.map (eJ.hom.app Q)) := by
    rw [MonoidalCategory.tensorHom_def, CategoryTheory.Functor.map_comp, Category.assoc]
    erw [hn₂, ← Category.assoc, hn₁, Category.assoc, ← MonoidalCategory.tensorHom_def]
  rw [reassoc_of% hn, tensorHom_comp_tensorHom_assoc, ha P, ha Q]
  rw [← tensorHom_comp_tensorHom, Category.assoc, ← hK]
  rw [reassoc_of% hδ]
  erw [eK.hom.naturality (δc P Q)]
  rw [← reassoc_of% (ha (P ⊗ Q)), ← H.map_comp_assoc, hJ]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

end

section
variable {C : Type v₁} {D : Type v₂} [Category.{w} C] [Category.{w} D]
  [Abelian C] [Abelian D]
  [IsGrothendieckAbelian.{w} C] [IsGrothendieckAbelian.{w} D]
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalPreadditive C] [MonoidalPreadditive D]
  [SymmetricCategory C] [SymmetricCategory D] [MonoidalClosed C] [MonoidalClosed D]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  (F : C ⥤ D) [F.Additive] [F.Monoidal]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesColimitsOfSize.{0, 0} F]
private theorem tensor_facQ_of_fach
    (δ : (Functor.postcompose₂.obj F.mapDerivedCategory).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj F.mapDerivedCategory).obj
        F.mapDerivedCategory).obj (curriedTensor _))
    (hδ : ∀ P Q : HomotopyCategory C (.up ℤ),
      (δ.app (DerivedCategory.Qh.obj P)).app (DerivedCategory.Qh.obj Q) ≫
          (F.mapDerivedCategoryFactorsh.hom.app P ⊗ₘ F.mapDerivedCategoryFactorsh.hom.app Q) ≫
          Functor.LaxMonoidal.μ DerivedCategory.Qh
            ((F.mapHomotopyCategory (.up ℤ)).obj P) ((F.mapHomotopyCategory (.up ℤ)).obj Q) =
        F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Qh P Q) ≫
          F.mapDerivedCategoryFactorsh.hom.app (P ⊗ Q) ≫
          DerivedCategory.Qh.map (Functor.OplaxMonoidal.δ
            (F.mapHomotopyCategory (.up ℤ)) P Q))
    (P Q : CochainComplex C ℤ) :
    (δ.app (DerivedCategory.Q.obj P)).app (DerivedCategory.Q.obj Q) ≫
        (F.mapDerivedCategoryFactors.hom.app P ⊗ₘ F.mapDerivedCategoryFactors.hom.app Q) ≫
        Functor.LaxMonoidal.μ DerivedCategory.Q
          ((F.mapHomologicalComplex (.up ℤ)).obj P)
          ((F.mapHomologicalComplex (.up ℤ)).obj Q) =
      F.mapDerivedCategory.map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
        F.mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
        DerivedCategory.Q.map (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app
          P).app Q) := by
  let J := HomotopyCategory.quotient (C) (.up ℤ) ⋙
    DerivedCategory.Qh
  let K := HomotopyCategory.quotient (D) (.up ℤ) ⋙
    DerivedCategory.Qh
  let eJ := DerivedCategory.quotientCompQhIso (C)
  let eK := DerivedCategory.quotientCompQhIso (D)
  refine tensorNormalization_transport J DerivedCategory.Q K DerivedCategory.Q eJ eK
    ?_ ?_ (F.mapHomologicalComplex (.up ℤ))
    F.mapDerivedCategory
    (fun R ↦ F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj R))
    (fun R ↦ F.mapDerivedCategoryFactors.hom.app R) ?_
    (δ) (fun R V ↦ ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app R).app V)
      ?_ P Q
  · intro R V
    dsimp only [J, K, eJ, eK]
    change _ = (_ ⊗ₘ _) ≫ ((_ ⊗ₘ _) ≫ _ ≫ _)
    simp only [← Category.assoc, tensorHom_comp_tensorHom, Iso.hom_inv_id_app,
      id_tensorHom_id, Category.id_comp]
  · intro R V
    dsimp only [J, K, eJ, eK]
    change _ = (_ ⊗ₘ _) ≫ ((_ ⊗ₘ _) ≫ _ ≫ _)
    simp only [← Category.assoc, tensorHom_comp_tensorHom, Iso.hom_inv_id_app,
      id_tensorHom_id, Category.id_comp]
  · intro R
    dsimp only [eJ, eK]
    rw [Functor.mapDerivedCategoryFactorsh_hom_app]
    change _ = (_ ≫ _ ≫ _ ≫ DerivedCategory.Qh.map (𝟙 _)) ≫ _
    simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc,
      Iso.inv_hom_id_app, Category.comp_id]
    erw [Category.comp_id]
  · intro R V
    have hd := hδ
      ((HomotopyCategory.quotient _ _).obj R) ((HomotopyCategory.quotient _ _).obj V)
    have hc : Functor.OplaxMonoidal.δ (F.mapHomotopyCategory (.up ℤ))
        ((HomotopyCategory.quotient _ _).obj R)
        ((HomotopyCategory.quotient _ _).obj V) =
      (HomotopyCategory.quotient _ _).map (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans
        (.up ℤ) F).app R).app V) := rfl
    rw [hc] at hd
    change _ ≫ _ ≫ (_ ≫ DerivedCategory.Qh.map (𝟙 _)) =
      F.mapDerivedCategory.map (_ ≫ DerivedCategory.Qh.map (𝟙 _)) ≫ _ ≫ _
    simp only [CategoryTheory.Functor.map_id, Category.comp_id]
    exact hd

private theorem tensor_facQ_normalized
    (δ : (Functor.postcompose₂.obj F.mapDerivedCategory).obj (curriedTensor _) ⟶
      (((Functor.whiskeringLeft₂ _).obj F.mapDerivedCategory).obj
        F.mapDerivedCategory).obj (curriedTensor _))
    (hδ : tensorNormalization DerivedCategory.Qh DerivedCategory.Qh
      (F.mapHomotopyCategory (.up ℤ)) (F.mapHomotopyCategory (.up ℤ))
      (F.mapHomotopyCategory (.up ℤ)) F.mapDerivedCategory F.mapDerivedCategory
      F.mapDerivedCategory F.mapDerivedCategoryFactorsh.hom F.mapDerivedCategoryFactorsh.hom
      F.mapDerivedCategoryFactorsh.hom
      (fun P Q ↦ Functor.OplaxMonoidal.δ (F.mapHomotopyCategory (.up ℤ)) P Q)
      (fun M N ↦ (δ.app M).app N)) :
    tensorNormalization DerivedCategory.Q DerivedCategory.Q
      (F.mapHomologicalComplex (.up ℤ)) (F.mapHomologicalComplex (.up ℤ))
      (F.mapHomologicalComplex (.up ℤ)) F.mapDerivedCategory F.mapDerivedCategory
      F.mapDerivedCategory F.mapDerivedCategoryFactors.hom F.mapDerivedCategoryFactors.hom
      F.mapDerivedCategoryFactors.hom
      (fun P Q ↦ ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q)
      (fun M N ↦ (δ.app M).app N) := by
  unfold tensorNormalization at hδ ⊢
  exact tensor_facQ_of_fach F δ hδ

end

section
variable {C : Type v₁} {D : Type v₂} {E : Type v₃}
  [Category.{w + 1} C] [Category.{w + 1} D] [Category.{w + 1} E]
  [Abelian C] [Abelian D] [Abelian E]
  [IsGrothendieckAbelian.{w + 1} C] [IsGrothendieckAbelian.{w + 1} D]
  [IsGrothendieckAbelian.{w + 1} E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [MonoidalPreadditive E]
  [SymmetricCategory C] [SymmetricCategory D] [SymmetricCategory E]
  [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosed E]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [Abelian.HasFunctorialFlatResolution E]
  [HasDerivedCategory.{w + 1} C] [HasDerivedCategory.{w + 1} D]
  [HasDerivedCategory.{w + 1} E]
  (G F₁ F₂ : C ⥤ D) (G₀ F₁₀ F₂₀ : C ⥤ E) (H : D ⥤ E)
  [G.Additive] [F₁.Additive] [F₂.Additive]
  [G₀.Additive] [F₁₀.Additive] [F₂₀.Additive] [H.Additive] [H.Monoidal]
  [PreservesColimitsOfSize.{0, 0} G] [PreservesColimitsOfSize.{0, 0} G₀]
  [PreservesColimitsOfSize.{0, 0} H]
  (τ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj (curriedTensor D))
  (τ₀ : (Functor.postcompose₂.obj G₀).obj (curriedTensor C) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁₀).obj F₂₀).obj (curriedTensor E))
  (a₀ : G₀ ⟶ G ⋙ H) (a₁ : F₁₀ ⟶ F₁ ⋙ H) (a₂ : F₂₀ ⟶ F₂ ⋙ H)
omit [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [Abelian.HasFunctorialFlatResolution E] [HasDerivedCategory C]
  [HasDerivedCategory D] [HasDerivedCategory E] in
private theorem complexSquare_cached
    (hs : ∀ P Q, AlgebraicGeometry.Etale.supportedTensorComplexSquareCondition
      G F₁ F₂ G₀ F₁₀ F₂₀ H τ τ₀ a₀ a₁ a₂ P Q) :
    squareCondition (G.mapHomologicalComplex (.up ℤ))
      (F₁.mapHomologicalComplex (.up ℤ)) (F₂.mapHomologicalComplex (.up ℤ))
      (G₀.mapHomologicalComplex (.up ℤ)) (F₁₀.mapHomologicalComplex (.up ℤ))
      (F₂₀.mapHomologicalComplex (.up ℤ)) (H.mapHomologicalComplex (.up ℤ))
      (fun P Q ↦ ((AlgebraicGeometry.Etale.supportedComplexComparisonNatTrans
        G F₁ F₂ τ).app P).app Q)
      (fun P Q ↦ ((AlgebraicGeometry.Etale.supportedComplexComparisonNatTrans
        G₀ F₁₀ F₂₀ τ₀).app P).app Q)
      (fun P Q ↦ ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans
        (.up ℤ) H).app P).app Q)
      (complexCompMap G H G₀ a₀) (complexCompMap F₁ H F₁₀ a₁)
      (complexCompMap F₂ H F₂₀ a₂) := by
  unfold squareCondition
  intro P Q
  have h := hs P Q
  unfold AlgebraicGeometry.Etale.supportedTensorComplexSquareCondition at h
  exact h
end

section
variable {C : Type v} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory.{u + 1} C] {X : AlgebraicGeometry.Scheme.{u}}
  (G F₁ F₂ : C ⥤ Sheaf X.smallEtaleTopology C)
  [G.Additive] [F₁.Additive] [F₂.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  (t : (Functor.postcompose₂.obj G.mapDerivedCategory).obj (curriedTensor _) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁.mapDerivedCategory).obj
      F₂.mapDerivedCategory).obj (AlgebraicGeometry.Etale.derivedTensor C X))

@[irreducible]
private noncomputable def schemeTensorComponent (M N : DerivedCategory C) :
    G.mapDerivedCategory.obj (M ⊗ N) ⟶
      ((AlgebraicGeometry.Etale.derivedTensor C X).obj (F₁.mapDerivedCategory.obj M)).obj
        (F₂.mapDerivedCategory.obj N) :=
  (t.app M).app N

end

section
variable {C D E : Type*}
  [Category.{w + 1} C] [Category.{w + 1} D] [Category.{w + 1} E]
  [Abelian C] [Abelian D] [Abelian E]
  [IsGrothendieckAbelian.{w + 1} C] [IsGrothendieckAbelian.{w + 1} D]
  [IsGrothendieckAbelian.{w + 1} E]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
  [MonoidalPreadditive C] [MonoidalPreadditive D] [MonoidalPreadditive E]
  [SymmetricCategory C] [SymmetricCategory D] [SymmetricCategory E]
  [MonoidalClosed C] [MonoidalClosed D] [MonoidalClosed E]
  [Abelian.HasFunctorialFlatResolution C] [Abelian.HasFunctorialFlatResolution D]
  [Abelian.HasFunctorialFlatResolution E]
  [HasDerivedCategory.{w + 1} C] [HasDerivedCategory.{w + 1} D]
  [HasDerivedCategory.{w + 1} E]
  (G F₁ F₂ : C ⥤ D) (G₀ F₁₀ F₂₀ : C ⥤ E) (H : D ⥤ E)
  [G.Additive] [F₁.Additive] [F₂.Additive]
  [G₀.Additive] [F₁₀.Additive] [F₂₀.Additive] [H.Additive] [H.Monoidal]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G₀] [PreservesFiniteColimits G₀]
  [PreservesFiniteLimits F₁₀] [PreservesFiniteColimits F₁₀]
  [PreservesFiniteLimits F₂₀] [PreservesFiniteColimits F₂₀]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  [PreservesColimitsOfSize.{0, 0} G] [PreservesColimitsOfSize.{0, 0} G₀]
  [PreservesColimitsOfSize.{0, 0} H]
  [(F₂ ⋙ H).PreservesFlat] [(F₂ ⋙ H).IsLeftAdjoint]
  (τ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj (curriedTensor D))
  (τ₀ : (Functor.postcompose₂.obj G₀).obj (curriedTensor C) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁₀).obj F₂₀).obj (curriedTensor E))
  (a₀ : G₀ ⟶ G ⋙ H) (a₁ : F₁₀ ⟶ F₁ ⋙ H) (a₂ : F₂₀ ⟶ F₂ ⋙ H)
  (da₀ : G₀.mapDerivedCategory ⟶ G.mapDerivedCategory ⋙ H.mapDerivedCategory)
  (da₁ : F₁₀.mapDerivedCategory ⟶ F₁.mapDerivedCategory ⋙ H.mapDerivedCategory)
  (da₂ : F₂₀.mapDerivedCategory ⟶ F₂.mapDerivedCategory ⋙ H.mapDerivedCategory)
  (t : (Functor.postcompose₂.obj G.mapDerivedCategory).obj (curriedTensor _) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁.mapDerivedCategory).obj
      F₂.mapDerivedCategory).obj (curriedTensor _))
  (t₀ : (Functor.postcompose₂.obj G₀.mapDerivedCategory).obj (curriedTensor _) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁₀.mapDerivedCategory).obj
      F₂₀.mapDerivedCategory).obj (curriedTensor _))
  (δ : (Functor.postcompose₂.obj H.mapDerivedCategory).obj (curriedTensor _) ⟶
    (((Functor.whiskeringLeft₂ _).obj H.mapDerivedCategory).obj
      H.mapDerivedCategory).obj (curriedTensor _))
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
private theorem derived_square
    (ht : tensorNatNormalization G F₁ F₂
      (AlgebraicGeometry.Etale.supportedComplexComparisonNatTrans G F₁ F₂ τ) t)
    (ht₀ : tensorNatNormalization G₀ F₁₀ F₂₀
      (AlgebraicGeometry.Etale.supportedComplexComparisonNatTrans G₀ F₁₀ F₂₀ τ₀) t₀)
    (hδ : tensorNatNormalization H H H
      (Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) H) δ)
    (ha₀ : mapNatNormalization G H G₀ a₀ da₀)
    (ha₁ : mapNatNormalization F₁ H F₁₀ a₁ da₁)
    (ha₂ : mapNatNormalization F₂ H F₂₀ a₂ da₂)
    (hs : ∀ P Q, AlgebraicGeometry.Etale.supportedTensorComplexSquareCondition
      G F₁ F₂ G₀ F₁₀ F₂₀ H τ τ₀ a₀ a₁ a₂ P Q)
    : squareLeft G.mapDerivedCategory F₁.mapDerivedCategory F₂.mapDerivedCategory
        G₀.mapDerivedCategory H.mapDerivedCategory da₀ t δ =
      squareRight G₀.mapDerivedCategory F₁₀.mapDerivedCategory F₂₀.mapDerivedCategory
        (F₁.mapDerivedCategory ⋙ H.mapDerivedCategory)
        (F₂.mapDerivedCategory ⋙ H.mapDerivedCategory) da₁ da₂ t₀ := by
  unfold tensorNatNormalization tensorNormalization at ht ht₀ hδ
  unfold mapNatNormalization mapNormalization at ha₀ ha₁ ha₂
  have hc := complexSquare_cached G F₁ F₂ G₀ F₁₀ F₂₀ H τ τ₀ a₀ a₁ a₂ hs
  unfold squareCondition at hc
  apply compositeTensor_ext F₁ F₂ H
  intro P Q
  rw [squareLeft_app, squareRight_app]
  exact model_square DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    (G.mapHomologicalComplex (.up ℤ))
    (F₁.mapHomologicalComplex (.up ℤ)) (F₂.mapHomologicalComplex (.up ℤ))
    (G₀.mapHomologicalComplex (.up ℤ))
    (F₁₀.mapHomologicalComplex (.up ℤ)) (F₂₀.mapHomologicalComplex (.up ℤ))
    (H.mapHomologicalComplex (.up ℤ))
    G.mapDerivedCategory F₁.mapDerivedCategory F₂.mapDerivedCategory
    G₀.mapDerivedCategory F₁₀.mapDerivedCategory F₂₀.mapDerivedCategory H.mapDerivedCategory
    G.mapDerivedCategoryFactors.hom F₁.mapDerivedCategoryFactors.hom
    F₂.mapDerivedCategoryFactors.hom G₀.mapDerivedCategoryFactors.hom
    F₁₀.mapDerivedCategoryFactors.hom F₂₀.mapDerivedCategoryFactors.hom
    H.mapDerivedCategoryFactors.hom
    (fun P Q ↦ ((AlgebraicGeometry.Etale.supportedComplexComparisonNatTrans
      G F₁ F₂ τ).app P).app Q)
    (fun P Q ↦ ((AlgebraicGeometry.Etale.supportedComplexComparisonNatTrans
      G₀ F₁₀ F₂₀ τ₀).app P).app Q)
    (fun M N ↦ (t.app M).app N) (fun M N ↦ (t₀.app M).app N) δ
    (fun P Q ↦ ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) H).app P).app Q)
    (complexCompMap G H G₀ a₀) (complexCompMap F₁ H F₁₀ a₁)
    (complexCompMap F₂ H F₂₀ a₂) da₀ da₁ da₂
    ht ht₀ hδ ha₀ ha₁ ha₂ hc P Q
end

namespace AlgebraicGeometry.Etale
attribute [local instance] supportedHasSheafify supportedHasWeakSheafify
end AlgebraicGeometry.Etale

section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace AlgebraicGeometry.Etale
variable (C : Type v) [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
    [UpperStarPreservesFlat C]
private noncomputable abbrev exactPullbackTensor
    {S T : Scheme.{u}} (h : S ⟶ T) [(upperStar C h).PreservesFlat] :
    (Functor.postcompose₂.obj (upperStar C h).mapDerivedCategory).obj
      (curriedTensor _) ⟶
    (((Functor.whiskeringLeft₂ _).obj
      (upperStar C h).mapDerivedCategory).obj
      (upperStar C h).mapDerivedCategory).obj (curriedTensor _) :=
  conjugateTensor (upperStar C h).leftDerivedFunctor (upperStar C h).mapDerivedCategory
    (leftDerivedUpperStarIsoMapDerivedCategory C h)
    (leftDerivedUpperStarTensorComparison C h)

private theorem exactPullbackTensor_app
    {S T : Scheme.{u}} (h : S ⟶ T) [(upperStar C h).PreservesFlat]
    (M N : DerivedCategory (Sheaf T.smallEtaleTopology C)) :
    ((exactPullbackTensor C h).app M).app N =
      (supportExactPullbackTensorIso C h M N).hom := by
  rw [exactPullbackTensor, conjugateTensor_app]
  simp only [supportExactPullbackTensorIso, supportDerivedTensorIso,
    Iso.trans_hom, Iso.symm_hom, Iso.app_hom,
    leftDerivedUpperStarTensorIso_hom]
  rfl

omit [UpperStarPreservesFlat C] in
private theorem exactPullbackTensor_fac_h
    {S T : Scheme.{u}} (h : S ⟶ T) [(upperStar C h).PreservesFlat] :
    tensorNormalization DerivedCategory.Qh DerivedCategory.Qh
      ((upperStar C h).mapHomotopyCategory (.up ℤ))
      ((upperStar C h).mapHomotopyCategory (.up ℤ))
      ((upperStar C h).mapHomotopyCategory (.up ℤ))
      (upperStar C h).mapDerivedCategory (upperStar C h).mapDerivedCategory
      (upperStar C h).mapDerivedCategory
      (upperStar C h).mapDerivedCategoryFactorsh.hom
      (upperStar C h).mapDerivedCategoryFactorsh.hom
      (upperStar C h).mapDerivedCategoryFactorsh.hom
      (fun P Q ↦ Functor.OplaxMonoidal.δ ((upperStar C h).mapHomotopyCategory (.up ℤ)) P Q)
      (fun M N ↦ ((exactPullbackTensor C h).app M).app N) := by
  unfold tensorNormalization
  intro P Q
  exact conjugateTensor_fac DerivedCategory.Qh DerivedCategory.Qh
    ((upperStar C h).mapHomotopyCategory (.up ℤ))
    (upperStar C h).leftDerivedFunctor (upperStar C h).mapDerivedCategory
    (leftDerivedUpperStarIsoMapDerivedCategory C h)
    (upperStar C h).leftDerivedFunctorCounit (upperStar C h).mapDerivedCategoryFactorsh.hom
    (fun R ↦ by
      have hf := NatTrans.congr_app
        (Functor.leftDerivedFunctorIsoMapDerivedCategory_hom_fac (upperStar C h)) R
      exact hf)
    (leftDerivedUpperStarTensorComparison C h)
    (fun R V ↦ Functor.OplaxMonoidal.δ ((upperStar C h).mapHomotopyCategory (.up ℤ)) R V)
    (leftDerivedUpperStarTensorComparison_app_app_comp C h) P Q

omit [UpperStarPreservesFlat C] in
private theorem exactPullbackTensor_fac
    {S T : Scheme.{u}} (h : S ⟶ T) [(upperStar C h).PreservesFlat] :
    tensorNatNormalization (upperStar C h) (upperStar C h) (upperStar C h)
      (Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) (upperStar C h))
      (exactPullbackTensor C h) := by
  unfold tensorNatNormalization
  exact tensor_facQ_normalized (upperStar C h) (exactPullbackTensor C h)
    (exactPullbackTensor_fac_h C h)
end AlgebraicGeometry.Etale

end
section
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] AlgebraicGeometry.Etale.upperStar
variable {C : Type v} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [Abelian.HasFunctorialFlatResolution C]
  [HasDerivedCategory.{u + 1} C]
  [AlgebraicGeometry.Etale.UpperStarPreservesFlat C]
  {X Y : AlgebraicGeometry.Scheme.{u}} (h : Y ⟶ X)
variable
  (G F₁ F₂ : C ⥤ (Sheaf X.smallEtaleTopology C)) (G₀ F₁₀ F₂₀ : C ⥤ (Sheaf Y.smallEtaleTopology C))
  [G.Additive] [F₁.Additive] [F₂.Additive]
  [G₀.Additive] [F₁₀.Additive] [F₂₀.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
  [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
  [PreservesFiniteLimits G₀] [PreservesFiniteColimits G₀]
  [PreservesFiniteLimits F₁₀] [PreservesFiniteColimits F₁₀]
  [PreservesFiniteLimits F₂₀] [PreservesFiniteColimits F₂₀]
  [PreservesColimitsOfSize.{0, 0} G] [PreservesColimitsOfSize.{0, 0} G₀]
  [(F₂ ⋙ (AlgebraicGeometry.Etale.upperStar C h)).PreservesFlat] [(F₂ ⋙
    (AlgebraicGeometry.Etale.upperStar C h)).IsLeftAdjoint]
  (τ : (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj
      (AlgebraicGeometry.Etale.supportedSheafTensorGeneric C X))
  (τ₀ : (Functor.postcompose₂.obj G₀).obj (curriedTensor C) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁₀).obj F₂₀).obj
      (AlgebraicGeometry.Etale.supportedSheafTensorGeneric C Y))
  (a₀ : G₀ ⟶ G ⋙ (AlgebraicGeometry.Etale.upperStar C h)) (a₁ : F₁₀ ⟶ F₁ ⋙
    (AlgebraicGeometry.Etale.upperStar C h)) (a₂ : F₂₀ ⟶ F₂ ⋙ (AlgebraicGeometry.Etale.upperStar C
    h))
  (da₀ : G₀.mapDerivedCategory ⟶ G.mapDerivedCategory ⋙ (AlgebraicGeometry.Etale.upperStar C
    h).mapDerivedCategory)
  (da₁ : F₁₀.mapDerivedCategory ⟶ F₁.mapDerivedCategory ⋙ (AlgebraicGeometry.Etale.upperStar C
    h).mapDerivedCategory)
  (da₂ : F₂₀.mapDerivedCategory ⟶ F₂.mapDerivedCategory ⋙ (AlgebraicGeometry.Etale.upperStar C
    h).mapDerivedCategory)
  (t : (Functor.postcompose₂.obj G.mapDerivedCategory).obj (curriedTensor _) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁.mapDerivedCategory).obj
      F₂.mapDerivedCategory).obj (AlgebraicGeometry.Etale.derivedTensor C X))
  (t₀ : (Functor.postcompose₂.obj G₀.mapDerivedCategory).obj (curriedTensor _) ⟶
    (((Functor.whiskeringLeft₂ _).obj F₁₀.mapDerivedCategory).obj
      F₂₀.mapDerivedCategory).obj (AlgebraicGeometry.Etale.derivedTensor C Y))
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
private theorem pullback_square_scheme
    (ht : tensorNatNormalization G F₁ F₂
      (AlgebraicGeometry.Etale.supportedComplexComparisonNatTrans G F₁ F₂ τ) t)
    (ht₀ : tensorNatNormalization G₀ F₁₀ F₂₀
      (AlgebraicGeometry.Etale.supportedComplexComparisonNatTrans G₀ F₁₀ F₂₀ τ₀) t₀)
    (ha₀ : mapNatNormalization G (AlgebraicGeometry.Etale.upperStar C h) G₀ a₀ da₀)
    (ha₁ : mapNatNormalization F₁ (AlgebraicGeometry.Etale.upperStar C h) F₁₀ a₁ da₁)
    (ha₂ : mapNatNormalization F₂ (AlgebraicGeometry.Etale.upperStar C h) F₂₀ a₂ da₂)
    (hs : ∀ P Q, AlgebraicGeometry.Etale.supportedTensorComplexSquareCondition
      G F₁ F₂ G₀ F₁₀ F₂₀ (AlgebraicGeometry.Etale.upperStar C h) τ τ₀ a₀ a₁ a₂ P Q)
    (M N : DerivedCategory C) :
    da₀.app (M ⊗ N) ≫ (AlgebraicGeometry.Etale.upperStar C h).mapDerivedCategory.map
      (schemeTensorComponent G F₁ F₂ t M N) ≫
        (AlgebraicGeometry.Etale.supportExactPullbackTensorIso C h
          (F₁.mapDerivedCategory.obj M) (F₂.mapDerivedCategory.obj N)).hom =
      (schemeTensorComponent G₀ F₁₀ F₂₀ t₀ M N) ≫
        (((AlgebraicGeometry.Etale.derivedTensor C Y).map (da₁.app M)).app
            (F₂₀.mapDerivedCategory.obj N) ≫
          ((AlgebraicGeometry.Etale.derivedTensor C Y).obj
            ((AlgebraicGeometry.Etale.upperStar C h).mapDerivedCategory.obj
              (F₁.mapDerivedCategory.obj M))).map (da₂.app N)) := by
  have hsq := derived_square G F₁ F₂ G₀ F₁₀ F₂₀
    (AlgebraicGeometry.Etale.upperStar C h) τ τ₀ a₀ a₁ a₂ da₀ da₁ da₂
    t t₀ (AlgebraicGeometry.Etale.exactPullbackTensor C h)
    ht ht₀ (AlgebraicGeometry.Etale.exactPullbackTensor_fac C h) ha₀ ha₁ ha₂ hs
  have he := square_equality_app G.mapDerivedCategory F₁.mapDerivedCategory
    F₂.mapDerivedCategory G₀.mapDerivedCategory F₁₀.mapDerivedCategory
    F₂₀.mapDerivedCategory (AlgebraicGeometry.Etale.upperStar C h).mapDerivedCategory
    da₀ da₁ da₂ t t₀ (AlgebraicGeometry.Etale.exactPullbackTensor C h) hsq M N
  rw [AlgebraicGeometry.Etale.exactPullbackTensor_app C h
    (F₁.mapDerivedCategory.obj M) (F₂.mapDerivedCategory.obj N)] at he
  simpa only [schemeTensorComponent, Functor.whiskeringLeft₂_obj_obj_obj_obj_obj,
    Functor.comp_obj,
    AlgebraicGeometry.Etale.derivedTensor, curriedTensor_map_app,
    curriedTensor_obj_map, MonoidalCategory.tensorHom_def, Category.assoc] using he
end

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace AlgebraicGeometry.Etale
attribute [local instance] supportedHasSheafify supportedHasWeakSheafify
private noncomputable abbrev coefficientTensorNatTrans
    (A : Type (u + 1)) [CommRing A] {S X Y B D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] :
    (Functor.postcompose₂.obj
      (supportedCoefficients A (supportedProductImmersion f g b d)).mapDerivedCategory).obj
        (curriedTensor (DerivedCategory (ModuleCat.{u + 1} A))) ⟶
      (((Functor.whiskeringLeft₂ _).obj
        (supportedFirstCoefficients A f g b).mapDerivedCategory).obj
          (supportedSecondCoefficients A f g d).mapDerivedCategory).obj
            (derivedTensor (ModuleCat.{u + 1} A) (pullback f g)) :=
  comparisonFromCondition
    (supportedCoefficients A (supportedProductImmersion f g b d))
    (supportedFirstCoefficients A f g b) (supportedSecondCoefficients A f g d)
    (supportedComplexComparisonNatTrans
      (supportedCoefficients A (supportedProductImmersion f g b d))
      (supportedFirstCoefficients A f g b) (supportedSecondCoefficients A f g d)
      (supportedCoefficientTensorNatTrans A f g b d))
    (exists_unique_supportedCoefficientTensorDerived A f g b d).choose
    (exists_unique_supportedCoefficientTensorDerived A f g b d).choose_spec.1

private theorem coefficientTensorNatTrans_fac
    (A : Type (u + 1)) [CommRing A] {S X Y B D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] :
    tensorNatNormalization
      (supportedCoefficients A (supportedProductImmersion f g b d))
      (supportedFirstCoefficients A f g b) (supportedSecondCoefficients A f g d)
      (supportedComplexComparisonNatTrans
        (supportedCoefficients A (supportedProductImmersion f g b d))
        (supportedFirstCoefficients A f g b) (supportedSecondCoefficients A f g d)
        (supportedCoefficientTensorNatTrans A f g b d))
      (coefficientTensorNatTrans A f g b d) :=
  comparisonFromCondition_normalized
    (supportedCoefficients A (supportedProductImmersion f g b d))
    (supportedFirstCoefficients A f g b) (supportedSecondCoefficients A f g d)
    (supportedComplexComparisonNatTrans
      (supportedCoefficients A (supportedProductImmersion f g b d))
      (supportedFirstCoefficients A f g b) (supportedSecondCoefficients A f g d)
      (supportedCoefficientTensorNatTrans A f g b d))
    (exists_unique_supportedCoefficientTensorDerived A f g b d).choose
    (exists_unique_supportedCoefficientTensorDerived A f g b d).choose_spec.1
end AlgebraicGeometry.Etale

private theorem mapped_nat_iso_cancel {C : Type u₁} {D : Type u₂} {E : Type u₃}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] (F : D ⥤ E)
    {G H : C ⥤ D} (e : G ≅ H) (X : C) {Z : E} (f : F.obj (H.obj X) ⟶ Z) :
    F.map (e.inv.app X) ≫ F.map (e.hom.app X) ≫ f = f := by
  rw [← F.map_comp_assoc, e.inv_hom_id_app, F.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
namespace AlgebraicGeometry.Etale
private noncomputable abbrev firstCoefficientMap
    (A : Type (u + 1)) [CommRing A] {S X Y B : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) [IsClosedImmersion b] (U : X.Opens) :=
  squareCoefficient (supportedCoefficients A b) (supportedCoefficients A (supportOnOpen b U))
    (upperStar (ModuleCat.{u + 1} A) U.ι)
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g))
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst (U.ι ≫ f) g))
    (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U))
    (squareUpperStarIso (ModuleCat.{u + 1} A) (CommSq.mk (supportedFirstOpenMap_fst f g U)))
    (supportCoefficientOpenMate A U.ι b (supportOnOpen b U) (supportOnOpen_complement b U))

private theorem firstCoefficientMap_eq
    (A : Type (u + 1)) [CommRing A] {S X Y B : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) [IsClosedImmersion b] (U : X.Opens)
    (M : DerivedCategory (ModuleCat.{u + 1} A)) :
    supportFirstOpenCoefficientMap A f g b U M = (firstCoefficientMap A f g b U).app M := by
  dsimp only [supportFirstOpenCoefficientMap]
  rw [square_inv_eq]
  simp only [supportFirstCoefficientProjectionIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
    (pullback.fst (U.ι ≫ f) g)).inv.naturality
      ((supportCoefficientOpenMate A U.ι b (supportOnOpen b U)
        (supportOnOpen_complement b U)).app M)
  rw [← reassoc_of% hn]
  rw [(leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
    (pullback.fst (U.ι ≫ f) g)).inv_hom_id_app_assoc]
  rw [mapped_nat_iso_cancel (upperStar (ModuleCat.{u + 1} A)
    (supportedFirstOpenMap f g U)).mapDerivedCategory
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.fst f g)) ((supportedCoefficients A b).mapDerivedCategory.obj M)]
  simp only [firstCoefficientMap, squareCoefficient, Functor.mapDerivedCategorySquareIso,
    Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc]

private noncomputable abbrev secondCoefficientMap
    (A : Type (u + 1)) [CommRing A] {S X Y D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y) [IsClosedImmersion d] (U : X.Opens) :=
  projectionCoefficient (supportedCoefficients A d)
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g))
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd (U.ι ≫ f) g))
    (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U))
    (upperStarComp (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)
      (pullback.snd f g) (pullback.snd (U.ι ≫ f) g)
      (supportedFirstOpenMap_snd f g U).symm)

private theorem secondCoefficientMap_eq
    (A : Type (u + 1)) [CommRing A] {S X Y D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y) [IsClosedImmersion d] (U : X.Opens)
    (N : DerivedCategory (ModuleCat.{u + 1} A)) :
    supportFirstOpenSecondCoefficientMap A f g d U N =
      (secondCoefficientMap A f g d U).app N := by
  dsimp only [supportFirstOpenSecondCoefficientMap]
  rw [projection_inv_eq]
  simp only [supportSecondCoefficientProjectionIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.isoWhiskerLeft_inv, Functor.whiskerLeft_app,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rw [(leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
    (pullback.snd (U.ι ≫ f) g)).inv_hom_id_app_assoc]
  rw [mapped_nat_iso_cancel (upperStar (ModuleCat.{u + 1} A)
    (supportedFirstOpenMap f g U)).mapDerivedCategory
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.snd f g)) ((supportedCoefficients A d).mapDerivedCategory.obj N)]
  simp only [secondCoefficientMap, projectionCoefficient, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc]
private theorem firstCoefficient_fac
    (A : Type (u + 1)) [CommRing A] {S X Y B : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) [IsClosedImmersion b] (U : X.Opens) :
    mapNatNormalization (supportedFirstCoefficients A f g b)
      (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U))
      (supportedFirstCoefficients A (U.ι ≫ f) g (supportOnOpen b U))
      (supportFirstOrdinaryOpenCoefficientNatTrans A f g b U)
      (firstCoefficientMap A f g b U) := by
  exact squareCoefficient_normalized_of_fach (supportedCoefficients A b)
    (supportedCoefficients A (supportOnOpen b U))
    (upperStar (ModuleCat.{u + 1} A) U.ι)
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g))
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst (U.ι ≫ f) g))
    (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U))
    (squareUpperStarIso (ModuleCat.{u + 1} A) (CommSq.mk (supportedFirstOpenMap_fst f g U)))
    (supportCoefficientMate (supportedCoefficientAdjunction A b)
      (supportedCoefficientAdjunction A (supportOnOpen b U))
      (upperStar (ModuleCat.{u + 1} A) U.ι)
      (supportTransport A U.ι b (supportOnOpen b U) (supportOnOpen_complement b U)))
    (supportCoefficientOpenMate A U.ι b (supportOnOpen b U) (supportOnOpen_complement b U))
    (supportedCoefficientDerivedOpenMate_fac A U.ι b (supportOnOpen b U)
      (supportOnOpen_complement b U))

private theorem secondCoefficient_fac
    (A : Type (u + 1)) [CommRing A] {S X Y D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y) [IsClosedImmersion d] (U : X.Opens) :
    mapNatNormalization (supportedSecondCoefficients A f g d)
      (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U))
      (supportedSecondCoefficients A (U.ι ≫ f) g d)
      (supportFirstOrdinaryOpenSecondCoefficientNatTrans A f g d U)
      (secondCoefficientMap A f g d U) := by
  have h := projectionCoefficient_normalized (supportedCoefficients A d)
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g))
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd (U.ι ≫ f) g))
    (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U))
    (upperStarComp (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)
      (pullback.snd f g) (pullback.snd (U.ι ≫ f) g)
      (supportedFirstOpenMap_snd f g U).symm)
  exact h

private theorem productCoefficient_fac
    (A : Type (u + 1)) [CommRing A] {S X Y B D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] (U : X.Opens) :
    mapNatNormalization (supportedCoefficients A (supportedProductImmersion f g b d))
      (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U))
      (supportedCoefficients A
        (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d))
      (supportFirstOrdinaryOpenProductCoefficientNatTrans A f g b d U)
      (supportCoefficientOpenMate A (supportedFirstOpenMap f g U)
        (supportedProductImmersion f g b d)
        (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d)
        (supportedFirstOpenSupport_complement f g b d U)) := by
  exact comp_facQ_normalized_of_fach (supportedCoefficients A (supportedProductImmersion f g b d))
      (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)) (supportedCoefficients A
    (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d))
      (supportFirstOrdinaryOpenProductCoefficientNatTrans A f g b d U) (supportCoefficientOpenMate A
      (supportedFirstOpenMap f g U)
    (supportedProductImmersion f g b d)
    (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d)
    (supportedFirstOpenSupport_complement f g b d U))
      (supportedCoefficientDerivedOpenMate_fac A (supportedFirstOpenMap f g U)
        (supportedProductImmersion f g b d)
        (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d)
        (supportedFirstOpenSupport_complement f g b d U))

private theorem secondCoefficient_flat
    (A : Type (u + 1)) [CommRing A] {S X Y D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y) [IsClosedImmersion d] :
    (supportedSecondCoefficients A f g d).PreservesFlat := by
  have : (supportedCoefficients A d).PreservesFlat := coefficients_preserveFlat A d
  exact ⟨fun h ↦ Functor.PreservesFlat.flat_obj
    (F := upperStar (ModuleCat.{u + 1} A) (pullback.snd f g))
    (Functor.PreservesFlat.flat_obj (F := supportedCoefficients A d) h)⟩

private theorem secondCoefficient_leftAdjoint
    (A : Type (u + 1)) [CommRing A] {S X Y D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y) [IsClosedImmersion d] :
    (supportedSecondCoefficients A f g d).IsLeftAdjoint :=
  inferInstanceAs ((supportedCoefficients A d) ⋙
    upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)).IsLeftAdjoint

private theorem secondCoefficient_openFlat
    (A : Type (u + 1)) [CommRing A] {S X Y D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y) [IsClosedImmersion d] (U : X.Opens) :
    ((supportedSecondCoefficients A f g d) ⋙
      upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)).PreservesFlat := by
  have := secondCoefficient_flat A f g d
  exact ⟨fun h ↦ Functor.PreservesFlat.flat_obj
    (F := upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U))
    (Functor.PreservesFlat.flat_obj (F := supportedSecondCoefficients A f g d) h)⟩

private theorem secondCoefficient_openLeftAdjoint
    (A : Type (u + 1)) [CommRing A] {S X Y D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (d : D ⟶ Y) [IsClosedImmersion d] (U : X.Opens) :
    ((supportedSecondCoefficients A f g d) ⋙
      upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)).IsLeftAdjoint := by
  have := secondCoefficient_leftAdjoint A f g d
  infer_instance

private theorem coefficientTensorComponent_app
    (A : Type (u + 1)) [CommRing A] {S X Y B D : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d]
    (M N : DerivedCategory (ModuleCat.{u + 1} A)) :
    schemeTensorComponent (supportedCoefficients A (supportedProductImmersion f g b d))
      (supportedFirstCoefficients A f g b) (supportedSecondCoefficients A f g d)
      (coefficientTensorNatTrans A f g b d) M N =
        supportedCoefficientTensorDerived A f g b d M N := by
  unfold schemeTensorComponent
  rfl

end AlgebraicGeometry.Etale

end CachedSheafProofs
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

namespace AlgebraicGeometry.Etale
attribute [local instance] supportedHasSheafify supportedHasWeakSheafify

/-- The coefficient tensor comparison commutes with open pullback in the first variable.
This statement involves arbitrary coefficient complexes and no supported-section inputs
or evaluation maps.

Source: Stacks Project Tags 09XP and 0F1E, coefficient calculation in steps 5 and 11
of lem-pur-supported-product-localization.
(blueprint: lem-pur-supported-coefficient-open-tensor).
Proof: the left mates of the ordinary support restrictions are inverse images of the
closed supported constant coefficient functors, normalized by their quotient maps.
Cancel the quotient from the constant sheaf to check the ordinary tensor square: both
maps restrict and multiply the same two local constants. On each tensor bidegree this
is the same square for the signed total comparison. Localizing K-flat coefficient
complexes gives the displayed equality, by the normalization of the derived coefficient
tensor comparison. Naturality and the existence of K-flat models extend it to arbitrary
coefficient complexes. The normalized derived-adjunction units identify the left mates
of derived restrictions with the derived ordinary left mates. This includes empty opens
and empty supports, where the corresponding coefficient sheaves vanish. -/
theorem supportedCoefficientTensor_openFirst (A : Type (u + 1)) [CommRing A]
    {S X Y B D : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (b : B ⟶ X) (d : D ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion d] (U : X.Opens)
    (M N : DerivedCategory (ModuleCat.{u + 1} A)) :
    (supportCoefficientOpenMate A (supportedFirstOpenMap f g U)
      (supportedProductImmersion f g b d)
      (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d)
      (supportedFirstOpenSupport_complement f g b d U)).app (M ⊗ N) ≫
      (upperStar (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)).mapDerivedCategory.map
        (supportedCoefficientTensorDerived A f g b d M N) ≫
      (supportExactPullbackTensorIso (ModuleCat.{u + 1} A) (supportedFirstOpenMap f g U)
        ((supportedFirstCoefficients A f g b).mapDerivedCategory.obj M)
        ((supportedSecondCoefficients A f g d).mapDerivedCategory.obj N)).hom =
    supportedCoefficientTensorDerived A (U.ι ≫ f) g (supportOnOpen b U) d M N ≫
      supportedDerivedTensorMap A (pullback (U.ι ≫ f) g)
        (supportFirstOpenCoefficientMap A f g b U M)
        (supportFirstOpenSecondCoefficientMap A f g d U N) := by
  have := secondCoefficient_openLeftAdjoint A f g d U
  have := secondCoefficient_openFlat A f g d U
  have he := pullback_square_scheme (C := (ModuleCat.{u + 1} A)) (supportedFirstOpenMap f g U)
    (supportedCoefficients A (supportedProductImmersion f g b d)) (supportedFirstCoefficients A f g
    b) (supportedSecondCoefficients A f g d) (supportedCoefficients A
    (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d)) (supportedFirstCoefficients A
      (U.ι ≫ f) g (supportOnOpen b U)) (supportedSecondCoefficients A (U.ι ≫ f) g d)
    (supportedCoefficientTensorNatTrans A f g b d)
    (supportedCoefficientTensorNatTrans A (U.ι ≫ f) g (supportOnOpen b U) d)
    (supportFirstOrdinaryOpenProductCoefficientNatTrans A f g b d U)
      (supportFirstOrdinaryOpenCoefficientNatTrans A f g b U)
      (supportFirstOrdinaryOpenSecondCoefficientNatTrans A f g d U) (supportCoefficientOpenMate A
      (supportedFirstOpenMap f g U)
    (supportedProductImmersion f g b d)
    (supportedProductImmersion (U.ι ≫ f) g (supportOnOpen b U) d)
    (supportedFirstOpenSupport_complement f g b d U)) (firstCoefficientMap A f g b U)
      (secondCoefficientMap A f g d U) (coefficientTensorNatTrans A f g b d)
      (coefficientTensorNatTrans A (U.ι ≫ f) g (supportOnOpen b U) d)
    (coefficientTensorNatTrans_fac A f g b d)
    (coefficientTensorNatTrans_fac A (U.ι ≫ f) g (supportOnOpen b U) d)
    (productCoefficient_fac A f g b d U)
    (firstCoefficient_fac A f g b U) (secondCoefficient_fac A f g d U)
    (supportedCoefficientTensor_complexOpenFirst A f g b d U)
    M N
  simpa only [coefficientTensorComponent_app, ← firstCoefficientMap_eq,
    ← secondCoefficientMap_eq, supportedDerivedTensorMap] using he

end AlgebraicGeometry.Etale
