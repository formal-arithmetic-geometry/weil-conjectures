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
