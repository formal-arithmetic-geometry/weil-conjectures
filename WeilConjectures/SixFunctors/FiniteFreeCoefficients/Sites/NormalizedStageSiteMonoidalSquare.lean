/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.FiniteFreeCoefficientExtensionData
public import WeilConjectures.AlgebraicGeometry.SixFunctors.EvaluationHomSiteComparison
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSiteComparisonSupplement
import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.NormalizedStageSiteKFlatComparisonNormalization
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
public import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorCoherence
public import WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorKFlat
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackIsoExistence
public import WeilConjectures.AlgebraicGeometry.Scalar.ScalarSheafTensorPullback
public import WeilConjectures.AlgebraicGeometry.Upper.UpperStarTensorCochainRepresentative
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MapDerivedCategoryMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionMonoidal

/-! # The normalized scalar/site monoidal square

Source: latest blueprint, sec-smooth-purity/sk-lem-sp-tower,
lem-coef-finite-free-extension.proof.md, paragraphs 1--3.
(blueprint: lem-sf-normalized-stage-site-monoidal-square).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory AlgebraicGeometry MonoidalCategory

namespace WeilConjectures.FiniteFreeCoefficients.Sites

private noncomputable def siteTensor
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) :
    Functor.uncurry.obj (tensor false A X) ⋙ nu A X ≅
      (nu A X).prod (nu A X) ⋙ Functor.uncurry.obj (tensor true A X) := by
  let : (nu A X).Monoidal :=
    ProEtale.siteComparisonDerivedMonoidal (ModuleCat.{u + 1} A) X
  exact (Functor.Monoidal.μNatIso (nu A X)).symm

private theorem siteTensor_hom
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K N : D false A X) :
    (siteTensor A X).hom.app (K, N) =
      (ProEtale.siteComparisonTensorIso (ModuleCat.{u + 1} A) X K).hom.app N := by
  unfold siteTensor ProEtale.siteComparisonTensorIso
  rfl

private theorem cancel_iso_right
    {C : Type*} [Category C] {W X Y : C} (f g : W ⟶ X) (i : X ⟶ Y)
    (hi : IsIso i) (h : f ≫ i = g ≫ i) : f = g := by
  let := hi
  exact (cancel_mono i).1 h

private theorem natTrans_ext_flat
    {C : Type*} [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
    [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory.{u + 1} C] {E : Type*} [Category E]
    {F G : DerivedCategory C × DerivedCategory C ⥤ E} (α β : F ⟶ G)
    (h : ∀ P Q : CochainComplex C ℤ,
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P →
      (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q →
      (∀ i : ℤ, ObjectProperty.flat (P.X i)) →
      (∀ i : ℤ, ObjectProperty.flat (Q.X i)) →
      α.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) =
        β.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) : α = β := by
  ext ⟨U, V⟩
  obtain ⟨P, p, hp, hPflat, hP⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage U)
  obtain ⟨Q, q, hq, hQflat, hQ⟩ :=
    CochainComplex.exists_quasiIso_flat_kFlat (DerivedCategory.Q.objPreimage V)
  have := hp
  have := hq
  let eP := asIso (DerivedCategory.Q.map p) ≪≫ DerivedCategory.Q.objObjPreimageIso U
  let eQ := asIso (DerivedCategory.Q.map q) ≪≫ DerivedCategory.Q.objObjPreimageIso V
  apply (cancel_epi (F.mapIso (eP.prod eQ)).hom).1
  change F.map (Prod.mkHom eP.hom eQ.hom) ≫ α.app (U, V) =
    F.map (Prod.mkHom eP.hom eQ.hom) ≫ β.app (U, V)
  rw [α.naturality, β.naturality, h P Q hP hQ hPflat hQflat]

private theorem slide_iso
    {C : Type*} [Category C] {W X Y Z : C} (i : W ≅ X) (j : Y ≅ Z)
    (f : X ⟶ Y) (g : W ⟶ Z) (h : i.hom ≫ f = g ≫ j.inv) :
    f ≫ j.hom = i.inv ≫ g := by
  apply (cancel_epi i.hom).1
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, h, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

private theorem cochain_square_normalization
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F₁ : A ⥤ B} {F₂ : B ⥤ D} {G₁ : A ⥤ C} {G₂ : C ⥤ D}
    [F₁.Additive] [F₂.Additive] [G₁.Additive] [G₂.Additive]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁]
    [PreservesFiniteLimits G₂] [PreservesFiniteColimits G₂]
    (e : F₁ ⋙ F₂ ≅ G₁ ⋙ G₂) (P : CochainComplex A ℤ) :
    F₂.mapDerivedCategory.map (F₁.mapDerivedCategoryFactors.hom.app P) ≫
      F₂.mapDerivedCategoryFactors.hom.app ((F₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
      _root_.DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) =
    (Functor.mapDerivedCategorySquareIso e).hom.app (_root_.DerivedCategory.Q.obj P) ≫
      G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app P) ≫
      G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj P) := by
  with_unfolding_all
    apply (cancel_epi ((Functor.mapDerivedCategoryCompIso F₁ F₂).hom.app
      (_root_.DerivedCategory.Q.obj P))).1
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Category.assoc]
    erw [Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc,
      Functor.mapDerivedCategoryCompIso_hom_app_factors]
    erw [Iso.hom_inv_id_app_assoc, Functor.mapDerivedCategoryNatIso_fac]
    rfl

private theorem cochain_unit_formula
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {E : C ⥤ D} {U : D ⥤ C} [E.Additive] [U.Additive] (a : E ⊣ U)
    (P : CochainComplex C ℤ) :
    (a.mapHomologicalComplex (.up ℤ)).unit.app P =
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
        (NatTrans.mapHomologicalComplex a.unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (E ⋙ U)) (.up ℤ)).inv.app P := by
  ext i
  change a.unit.app (P.X i) = 𝟙 _ ≫ a.unit.app (P.X i) ≫ 𝟙 _
  simp only [Category.id_comp, Category.comp_id]

private theorem cochain_left_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {E₁ : A ⥤ B} {U₁ : B ⥤ A} {E₂ : C ⥤ D} {U₂ : D ⥤ C}
    [E₁.Additive] [U₁.Additive] [E₂.Additive] [U₂.Additive]
    (a₁ : E₁ ⊣ U₁) (a₂ : E₂ ⊣ U₂)
    {F : A ⥤ C} {G : B ⥤ D} [F.Additive] [G.Additive]
    (τ : U₁ ⋙ F ⟶ G ⋙ U₂) (P : CochainComplex A ℤ) :
    ((mateEquiv (G := F.mapHomologicalComplex (.up ℤ))
      (H := G.mapHomologicalComplex (.up ℤ)) (a₁.mapHomologicalComplex (.up ℤ))
      (a₂.mapHomologicalComplex (.up ℤ))).symm
      (TwoSquare.mk _ _ _ _ (NatTrans.mapHomologicalComplex τ (.up ℤ)))).natTrans.app P =
    (NatTrans.mapHomologicalComplex
      (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ)).natTrans) (.up ℤ)).app P := by
  with_unfolding_all
    erw [left_mate_app]

private theorem cochain_scalar_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {E₁ : A ⥤ B} {U₁ : B ⥤ A} {E₂ : C ⥤ D} {U₂ : D ⥤ C}
    [E₁.Additive] [U₁.Additive] [E₂.Additive] [U₂.Additive]
    [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
    [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
    (a₁ : E₁ ⊣ U₁) (a₂ : E₂ ⊣ U₂)
    {L₁ : _root_.DerivedCategory A ⥤ _root_.DerivedCategory B}
    {L₂ : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D}
    (d₁ : L₁ ⊣ U₁.mapDerivedCategory) (d₂ : L₂ ⊣ U₂.mapDerivedCategory)
    (N : A ⥤ C) (N' : B ⥤ D) [N.Additive] [N'.Additive]
    [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    [PreservesFiniteLimits N'] [PreservesFiniteColimits N']
    (e : N' ⋙ U₂ ≅ U₁ ⋙ N) (P : CochainComplex A ℤ) :
    ((mateEquiv d₁ d₂).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso e).inv)).natTrans.app
        (_root_.DerivedCategory.Q.obj P) ≫
      N'.mapDerivedCategory.map ((representative E₁ U₁ a₁ d₁).app P) ≫
      N'.mapDerivedCategoryFactors.hom.app ((E₁.mapHomologicalComplex (.up ℤ)).obj P) =
    L₂.map (N.mapDerivedCategoryFactors.hom.app P) ≫
      (representative E₂ U₂ a₂ d₂).app ((N.mapHomologicalComplex (.up ℤ)).obj P) ≫
      _root_.DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ e.inv)).natTrans) (.up ℤ)).app P) := by
  with_unfolding_all
    have h := left_mate_normalization
      (a₁.mapHomologicalComplex (.up ℤ)) (a₂.mapHomologicalComplex (.up ℤ)) d₁ d₂
      _root_.DerivedCategory.Q _root_.DerivedCategory.Q
      _root_.DerivedCategory.Q _root_.DerivedCategory.Q
      (representative E₁ U₁ a₁ d₁) (representative E₂ U₂ a₂ d₂)
      U₁.mapDerivedCategoryFactors U₂.mapDerivedCategoryFactors
      N.mapDerivedCategoryFactors N'.mapDerivedCategoryFactors
      (NatTrans.mapHomologicalComplex e.inv (.up ℤ))
      (Functor.mapDerivedCategorySquareIso e).inv
      (representative_unit E₁ U₁ a₁ d₁) (representative_unit E₂ U₂ a₂ d₂)
      (by
        intro R
        have he := cochain_square_normalization e.symm R
        simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom,
          Iso.symm_hom, Functor.mapDerivedCategoryNatIso_symm,
          NatTrans.comp_app, Category.assoc] at he
        convert! he using 1
        simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_inv, Iso.symm_inv,
          NatTrans.comp_app, Category.assoc]) P
    have hc := cochain_left_mate (F := N) (G := N') a₁ a₂ e.inv P
    rw [hc] at h
    exact h

private theorem cochain_scalar_mate_iso
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {E₁ : A ⥤ B} {U₁ : B ⥤ A} {E₂ : C ⥤ D} {U₂ : D ⥤ C}
    [E₁.Additive] [U₁.Additive] [E₂.Additive] [U₂.Additive]
    [PreservesFiniteLimits U₁] [PreservesFiniteColimits U₁]
    [PreservesFiniteLimits U₂] [PreservesFiniteColimits U₂]
    (a₁ : E₁ ⊣ U₁) (a₂ : E₂ ⊣ U₂)
    {L₁ : _root_.DerivedCategory A ⥤ _root_.DerivedCategory B}
    {L₂ : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D}
    (d₁ : L₁ ⊣ U₁.mapDerivedCategory) (d₂ : L₂ ⊣ U₂.mapDerivedCategory)
    (N : A ⥤ C) (N' : B ⥤ D) [N.Additive] [N'.Additive]
    [PreservesFiniteLimits N] [PreservesFiniteColimits N]
    [PreservesFiniteLimits N'] [PreservesFiniteColimits N']
    (e : N' ⋙ U₂ ≅ U₁ ⋙ N) (s : E₁ ⋙ N' ≅ N ⋙ E₂)
    (δ : N.mapDerivedCategory ⋙ L₂ ≅ L₁ ⋙ N'.mapDerivedCategory)
    (hδ : δ.hom = ((mateEquiv d₁ d₂).symm
      (TwoSquare.mk _ _ _ _ (Functor.mapDerivedCategorySquareIso e).inv)).natTrans)
    (hs : ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ e.inv)).natTrans = s.inv)
    (P : CochainComplex A ℤ) :
    N'.mapDerivedCategory.map ((representative E₁ U₁ a₁ d₁).app P) ≫
      N'.mapDerivedCategoryFactors.hom.app ((E₁.mapHomologicalComplex (.up ℤ)).obj P) ≫
      _root_.DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex s.hom (.up ℤ)).app P) =
    δ.inv.app (_root_.DerivedCategory.Q.obj P) ≫
      L₂.map (N.mapDerivedCategoryFactors.hom.app P) ≫
      (representative E₂ U₂ a₂ d₂).app ((N.mapHomologicalComplex (.up ℤ)).obj P) := by
  with_unfolding_all
    have h := cochain_scalar_mate a₁ a₂ d₁ d₂ N N' e P
    erw [← hδ, hs] at h
    have hh := slide_iso (δ.app (_root_.DerivedCategory.Q.obj P))
      (_root_.DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex s (.up ℤ)).app P))
      (N'.mapDerivedCategory.map ((representative E₁ U₁ a₁ d₁).app P) ≫
        N'.mapDerivedCategoryFactors.hom.app ((E₁.mapHomologicalComplex (.up ℤ)).obj P))
      (L₂.map (N.mapDerivedCategoryFactors.hom.app P) ≫
        (representative E₂ U₂ a₂ d₂).app ((N.mapHomologicalComplex (.up ℤ)).obj P))
      (h.trans (Category.assoc _ _ _).symm)
    exact (Category.assoc _ _ _).symm.trans hh

private instance genericSiteTensorComparison_isIso
    (C : Type (u + 2)) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar C X).PreservesFlat] :
    IsIso (genericSiteTensorComparison C X) := by
  dsimp only [genericSiteTensorComparison]
  infer_instance

private theorem inverse_tensor_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u})
    (μ : Sites.TensorComparison true φ X) (hμ : Sites.NormalizedTensor true φ X μ)
    (K M : Cat A X) :
    (Sites.scalarSite φ X).inv.app (K ⊗ M) ≫
      (Sites.scalar true φ X).map
        ((ProEtale.siteComparisonTensorIso (ModuleCat.{u + 1} A) X K).hom.app M) ≫
      μ.hom.app ((Sites.nu A X).obj K, (Sites.nu A X).obj M) =
    (Sites.nu B X).map ((Etale.ExceptionalCoefficients.tensorIso φ X).hom.app (K, M)) ≫
      (ProEtale.siteComparisonTensorIso (ModuleCat.{u + 1} B) X
        ((Sites.scalar false φ X).obj K)).hom.app ((Sites.scalar false φ X).obj M) ≫
      ((Sites.scalarSite φ X).inv.app K ⊗ₘ (Sites.scalarSite φ X).inv.app M) := by
  with_unfolding_all
    let F := Sites.scalar false φ X
    let G := Sites.scalar true φ X
    let P := Sites.nu A X
    let Q := Sites.nu B X
    let TY := Functor.uncurry.obj (curriedTensor (Cat A X))
    let TX := Functor.uncurry.obj (curriedTensor (Sites.D true B X))
    let tF : TY ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj (curriedTensor (Cat B X)) := by
      with_unfolding_all
        exact Etale.ExceptionalCoefficients.tensorIso φ X
    let tG : Functor.uncurry.obj (curriedTensor (Sites.D true A X)) ⋙ G ≅
        G.prod G ⋙ TX := by
      with_unfolding_all exact μ
    let tP := (rawSiteTensor A X).hom
    let tQ := (rawSiteTensor B X).hom
    let a := (Sites.scalarSite φ X).symm
    let α : TY ⋙ F ⋙ Q ⟶ P.prod P ⋙ G.prod G ⋙ TX :=
      Functor.whiskerLeft TY a.hom ≫ Functor.whiskerRight tP G ≫
        Functor.whiskerLeft (P.prod P) tG.hom
    let β : TY ⋙ F ⋙ Q ⟶ P.prod P ⋙ G.prod G ⋙ TX :=
      Functor.whiskerRight tF.hom Q ≫ Functor.whiskerLeft (F.prod F) tQ ≫
        Functor.whiskerRight (NatTrans.prod a.hom a.hom) TX
    have h : α = β := by
      apply Etale.natTrans_ext_flat α β
      intro U V hU hV _ _
      dsimp only [α, β, TY, TX, P, Q, F, G, tF, tP, tQ, a, Iso.symm_hom,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
        Functor.uncurry_obj_obj, Functor.prod_obj, Functor.comp_obj, NatTrans.prod]
      dsimp only [tG]
      rw [rawSiteTensor_generic_app, rawSiteTensor_generic_app]
      have hk := normalized_site_tensor_kflat φ X μ hμ U V hU hV
      simp only [Sites.tensor, _root_.id, Etale.derivedTensor, ProEtale.derivedTensor,
        curriedTensor_obj_obj, Etale.uncurryCurriedTensor_map,
        Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj] at hk ⊢
      with_unfolding_all
        convert! hk using 1
    have h' := congrArg (fun t ↦ t.app (K, M)) h
    dsimp only [α, β, TY, TX, P, Q, F, G, tF, tP, tQ, a, Iso.symm_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Functor.uncurry_obj_obj, Functor.prod_obj, Functor.comp_obj, NatTrans.prod,
      Etale.uncurryTensorComparison] at h'
    rw [rawSiteTensor_hom_app, rawSiteTensor_hom_app] at h'
    dsimp only [tG] at h'
    simp only [Sites.tensor, _root_.id, Etale.derivedTensor, ProEtale.derivedTensor,
      curriedTensor_obj_obj, Etale.uncurryCurriedTensor_map,
      Functor.comp_obj, Functor.prod_obj, Functor.uncurry_obj_obj] at h' ⊢
    with_unfolding_all
      convert! h' using 1

/-- The canonical scalar/site comparison commutes with the normalized tensorators.
The tensor product of the two comparison components is written using the two actions
of the published derived tensor bifunctor.

Source: latest blueprint, lem-coef-finite-free-extension.proof.md, paragraphs 1--3.
(blueprint: lem-sf-normalized-stage-site-monoidal-square).

Proof: (1) Unpack the fixed comparison data. Both composites have source
S_pro(nu_A(U tensor V)) and target nu_B(S_et U) tensor nu_B(S_et V).
(2) On ordinary sheaves the scalar/site mate and the site tensor comparison commute
with balanced scalar tensor products: both routes send b tensor (m tensor n) to
(b tensor m) tensor (1 tensor n).
(3) Choose flat-term K-flat representatives P and Q. The ordinary square assembles
into the signed total tensor square, with the same Koszul differential on both routes.
The K-flat comparison-normalization statement identifies sigma, both mu components
and both site tensor comparisons with these cochain maps, with the same endpoint
identifications.
(4) Thus the two natural transformations agree after restriction to localized pairs
of flat-term K-flat complexes. Injectivity of this restriction, from derived tensor
descent, gives their equality everywhere. Taking the component at (U,V) gives the
assertion. No boundedness, constructibility, Tor-amplitude or flatness of the ring
map is needed. -/
theorem normalized_stage_site_monoidal_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u})
    (μet : TensorComparison false φ X) (μpro : TensorComparison true φ X)
    (hμet : NormalizedTensor false φ X μet) (hμpro : NormalizedTensor true φ X μpro)
    (U V : D false A X) :
    (scalar true φ X).map
        ((ProEtale.siteComparisonTensorIso (ModuleCat.{u + 1} A) X U).hom.app V) ≫
      μpro.hom.app ((nu A X).obj U, (nu A X).obj V) ≫
      ((tensor true B X).map ((scalarSite φ X).hom.app U)).app
        ((scalar true φ X).obj ((nu A X).obj V)) ≫
      ((tensor true B X).obj ((nu B X).obj ((scalar false φ X).obj U))).map
        ((scalarSite φ X).hom.app V) =
    (scalarSite φ X).hom.app (((tensor false A X).obj U).obj V) ≫
      (nu B X).map (μet.hom.app (U, V)) ≫
      (ProEtale.siteComparisonTensorIso (ModuleCat.{u + 1} B) X
        ((scalar false φ X).obj U)).hom.app ((scalar false φ X).obj V) := by
  let TA := Functor.uncurry.obj (tensor false A X)
  let TB := Functor.uncurry.obj (tensor true B X)
  let νA := nu A X
  let νB := nu B X
  let SE := scalar false φ X
  let SP := scalar true φ X
  let σ := scalarSite φ X
  let α : TA ⋙ νA ⋙ SP ⟶ (SE.prod SE) ⋙ (νB.prod νB) ⋙ TB :=
    Functor.whiskerRight (siteTensor A X).hom SP ≫
      Functor.whiskerLeft (νA.prod νA) μpro.hom ≫
      Functor.whiskerRight (NatTrans.prod σ.hom σ.hom) TB
  let β : TA ⋙ νA ⋙ SP ⟶ (SE.prod SE) ⋙ (νB.prod νB) ⋙ TB :=
    Functor.whiskerLeft TA σ.hom ≫
      Functor.whiskerRight μet.hom νB ≫
      Functor.whiskerLeft (SE.prod SE) (siteTensor B X).hom
  have hab : α = β := by
    apply natTrans_ext_flat α β
    intro P Q hP hQ hPflat hQflat
    obtain ⟨_, hn⟩ := normalized_stage_site_kflat_comparison_normalization
      φ X μet μpro hμet hμpro
    obtain ⟨_, ht, _, _, _, _, _, hl, hr⟩ := hn P Q hPflat hQflat hP hQ
    have hc := normalized_stage_site_cochain_tensor_square φ X P Q hPflat hQflat hP hQ
    rw [hc] at hl
    have he := cancel_iso_right _ _ _ ht (hl.trans hr.symm)
    dsimp only [α, β, TA, TB, νA, νB, SE, SP, σ,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
      Functor.comp_obj, Functor.prod_obj, NatTrans.prod]
    rw [siteTensor_hom, siteTensor_hom]
    simpa only [tensor, Etale.derivedTensor, ProEtale.derivedTensor, _root_.id,
      Functor.uncurry_obj_obj, Functor.comp_obj, Functor.prod_obj, curriedTensor_obj_obj,
      Functor.uncurry_obj_map, curriedTensor_map_app, curriedTensor_obj_map,
      MonoidalCategory.tensorHom_def, Category.assoc] using he
  have h := congrArg (fun t ↦ t.app (U, V)) hab
  dsimp only [α, β, TA, TB, νA, νB, SE, SP, σ,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app,
    Functor.comp_obj, Functor.prod_obj, NatTrans.prod] at h
  rw [siteTensor_hom, siteTensor_hom] at h
  exact h

end WeilConjectures.FiniteFreeCoefficients.Sites
