/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.Sites.NormalizedStageComparisonObligations
public import WeilConjectures.CategoryTheory.SixFunctors.ParametrizedTensorHomSquare
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageSiteBridgeFoundations
public import WeilConjectures.SixFunctors.FiniteFreeCoefficients.NormalizedStageSiteTensorSquare

/-! # Site equations for normalized stage comparisons

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1--3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.FiniteCoefficientAdjoints
open scoped CategoryTheory.Functor
namespace WeilConjectures.FiniteFreeCoefficients

private theorem inverse_component_naturality
    {C : Type g₁} {D : Type g₂}
    [CategoryTheory.Category.{h₁} C] [CategoryTheory.Category.{h₂} D] {F G : C ⥤ D} (α : F ⟶ G)
    {K L : C} (g : K ⟶ L) [IsIso (α.app K)] [IsIso (α.app L)] :
    G.map g ≫ inv (α.app L) = inv (α.app K) ≫ F.map g := by
  apply (cancel_mono (α.app L)).1
  simp only [CategoryTheory.Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [α.naturality g, IsIso.inv_hom_id_assoc]

private theorem right_mate_naturality
    {C : Type g₁} {D : Type g₂} {C' : Type g₃} {D' : Type g₄}
    [CategoryTheory.Category.{h₁} C] [CategoryTheory.Category.{h₂} D]
    [CategoryTheory.Category.{h₃} C'] [CategoryTheory.Category.{h₄} D']
    {FA : C ⥤ D} {GA : D ⥤ C} {FB : C' ⥤ D'} {GB : D' ⥤ C'}
    (adA : FA ⊣ GA) (adB : FB ⊣ GB) (SC : C ⥤ C') (SD : D ⥤ D')
    (α : FA ⋙ SD ⟶ SC ⋙ FB) {K L : D} (g : K ⟶ L)
    [IsIso (α.app (GA.obj K))] [IsIso (α.app (GA.obj L))] :
    SC.map (GA.map g) ≫ adB.homEquiv _ _
        (inv (α.app (GA.obj L)) ≫ SD.map (adA.counit.app L)) =
      adB.homEquiv _ _ (inv (α.app (GA.obj K)) ≫ SD.map (adA.counit.app K)) ≫
        GB.map (SD.map g) := by
  apply (adB.homEquiv _ _).symm.injective
  rw [adB.homEquiv_naturality_left_symm, adB.homEquiv_naturality_right_symm]
  simp only [Equiv.symm_apply_apply]
  have hn := inverse_component_naturality α (GA.map g)
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hn, Category.assoc]
  simp only [CategoryTheory.Category.assoc, ← SD.map_comp]
  exact congrArg (fun q ↦ inv (α.app (GA.obj K)) ≫ SD.map q)
    (adA.counit.naturality g)

private theorem etale_closed_natural
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    {K L : Cat A X} (g : K ⟶ L)
    [IsIso (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj K))]
    [IsIso (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj L))] :
    (Etale.scalarExtension φ Z).map ((closedUpper A i).map g) ≫ closedMap φ i L =
      closedMap φ i K ≫ (closedUpper B i).map ((Etale.scalarExtension φ X).map g) := by
  classical
  let α : R(Etale.lowerStar (ModuleCat.{u + 1} A) i) ⋙ Etale.scalarExtension φ X ⟶
      Etale.scalarExtension φ Z ⋙ R(Etale.lowerStar (ModuleCat.{u + 1} B) i) := {
    app := Etale.finiteCoefficientDirectImageMap φ i
    naturality := fun _ _ g ↦ Etale.finiteCoefficientDirectImageMap_naturality φ i g }
  simpa only [closedUpper, closedMap, α, Functor.id_obj, dif_pos (inferInstance : IsIso
      (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj K))),
    dif_pos (inferInstance : IsIso
      (Etale.finiteCoefficientDirectImageMap φ i ((closedUpper A i).obj L)))] using
    right_mate_naturality
      (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} A) i)))
      (Adjunction.ofIsLeftAdjoint (R(Etale.lowerStar (ModuleCat.{u + 1} B) i)))
      (Etale.scalarExtension φ Z) (Etale.scalarExtension φ X) α g

private theorem mate_unit_square
    {C : Type g₁} {D : Type g₂} {C' : Type g₃} {D' : Type g₄}
    [Category C] [Category D] [Category C'] [Category D']
    {F : C ⥤ D} {R : D ⥤ C} {G : C' ⥤ D'} {S : D' ⥤ C'}
    (ad : F ⊣ R) (bd : G ⊣ S) (U : C ⥤ C') (V : D ⥤ D')
    (e : F ⋙ V ≅ U ⋙ G) (K : C) :
    U.map (ad.unit.app K) ≫
        bd.homEquiv _ _ (e.inv.app (R.obj (F.obj K)) ≫ V.map (ad.counit.app (F.obj K))) ≫
        S.map (e.hom.app K) = bd.unit.app (U.obj K) := by
  have he := e.inv.naturality (ad.unit.app K)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at he
  have hh : G.map (U.map (ad.unit.app K)) ≫
      e.inv.app (R.obj (F.obj K)) ≫ V.map (ad.counit.app (F.obj K)) ≫
      e.hom.app K = 𝟙 _ := by
    rw [← Category.assoc, ← Category.assoc, he]
    rw [Category.assoc, Category.assoc, ← V.map_comp_assoc,
      ad.left_triangle_components, V.map_id, Category.id_comp, e.inv_hom_id_app]
    rfl
  rw [bd.homEquiv_apply]
  simp only [Category.assoc]
  rw [← bd.unit_naturality_assoc]
  simp only [← S.map_comp, Category.assoc]
  rw [hh, S.map_id, Category.comp_id]
  rfl

private theorem transported_natural_square
    {C C' Z Z' P P' : Type*}
    [Category C] [Category C'] [Category Z] [Category Z'] [Category P] [Category P']
    (F : C ⥤ C') (U : C ⥤ Z) (V : C' ⥤ Z')
    (S : Z ⥤ Z') (L : Z ⥤ P) (L' : Z' ⥤ P') (T : P ⥤ P')
    (e : L ⋙ T ≅ S ⋙ L') {K M : C} (η : K ⟶ M)
    (bK : S.obj (U.obj K) ⟶ V.obj (F.obj K))
    (bM : S.obj (U.obj M) ⟶ V.obj (F.obj M))
    {N Q : C'} (r : F.obj M ⟶ N) (h : N ⟶ Q) (u : F.obj K ⟶ Q)
    (hn : S.map (U.map η) ≫ bM = bK ≫ V.map (F.map η))
    (hu : F.map η ≫ r ≫ h = u) :
    T.map (L.map (U.map η)) ≫
        (e.hom.app (U.obj M) ≫ L'.map bM ≫ L'.map (V.map r)) ≫
          L'.map (V.map h) =
      e.hom.app (U.obj K) ≫ L'.map bK ≫ L'.map (V.map u) := by
  simp only [Category.assoc]
  rw [reassoc_of% e.hom.naturality]
  rw [← L'.map_comp_assoc, hn, L'.map_comp]
  simp only [Category.assoc, ← L'.map_comp, ← V.map_comp]
  rw [hu]

private theorem map_inverse_cancel
    {C D : Type*} [Category C] [Category D] [Preadditive C] (F : C ⥤ D)
    {K L : C} (b : K ⟶ L) [IsIso b] {N : D} (r : F.obj K ⟶ N) :
    F.map b ≫ (F.map (Sites.inverseOnDomain b) ≫ r) = r := by
  simp only [Sites.inverseOnDomain, dif_pos (inferInstance : IsIso b),
    ← F.map_comp_assoc, IsIso.hom_inv_id, F.map_id, Category.id_comp]

private theorem inverse_square
    {C : Type*} [Category C] {A B C₁ D E F : C}
    (a : A ≅ B) (b : B ≅ C₁) (c : C₁ ≅ D)
    (d : A ≅ E) (e : E ≅ F) (f : F ≅ D)
    (h : a.hom ≫ b.hom ≫ c.hom = d.hom ≫ e.hom ≫ f.hom) :
    f.hom ≫ c.inv ≫ b.inv = e.inv ≫ d.inv ≫ a.hom := by
  have hi : a ≪≫ b ≪≫ c = d ≪≫ e ≪≫ f := Iso.ext h
  have hh := congrArg (fun i ↦ f.hom ≫ i.inv ≫ a.hom) hi
  simpa only [Iso.trans_inv, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.hom_inv_id_assoc] using hh

private def siteAdjunction₂ (pro : Bool) (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) : Sites.tensor pro A X ⊣₂ Sites.hom pro A X where
  adj K := Sites.adj pro A X K
  unit_whiskerRight_map {K K'} f := by
    cases pro
    · simpa only [Sites.adj, Sites.tensor, Sites.hom, _root_.id,
        Etale.derivedTensorHomAdjunction] using
        (Etale.derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} A) X).unit_whiskerRight_map f
    · simpa only [Sites.adj, Sites.tensor, Sites.hom, _root_.id,
        ProEtale.derivedTensorHomAdjunction] using
        (ProEtale.derivedTensorHomAdjunction₂ (ModuleCat.{u + 1} A) X).unit_whiskerRight_map f

private theorem scalar_hom_evaluation
    (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (μ : Sites.TensorComparison pro φ X)
    (K M : Sites.D pro A X) :
    ((Sites.tensor pro B X).obj ((Sites.scalar pro φ X).obj K)).map
        (Sites.homMap pro φ X μ K M) ≫
        (Sites.adj pro B X ((Sites.scalar pro φ X).obj K)).counit.app
          ((Sites.scalar pro φ X).obj M) =
      μ.inv.app (K, ((Sites.hom pro A X).obj (op K)).obj M) ≫
        (Sites.scalar pro φ X).map ((Sites.adj pro A X K).counit.app M) := by
  dsimp only [Sites.homMap, Functor.id_obj, Functor.prod_obj]
  exact ((Sites.adj pro B X ((Sites.scalar pro φ X).obj K)).homEquiv _ _).symm_apply_apply _

private theorem site_tensor_inverse_app
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) (K M : Cat A X) :
    (siteTensor A X).inv.app (K, M) =
      (ProEtale.siteComparisonTensorIso (ModuleCat.{u + 1} A) X K).inv.app M := by
  with_unfolding_all
    exact nativeSiteTensor_inv_app (ModuleCat.{u + 1} A) X K M

private theorem native_site_hom_evaluation
    (C : Type (u + 2)) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar C X).PreservesFlat]
    (K M : DerivedCategory (Sheaf X.smallEtaleTopology C)) :
    ((ProEtale.derivedTensor C X).obj
        ((ProEtale.comparisonUpperStar C X).mapDerivedCategory.obj K)).map
          (ProEtale.siteComparisonEvaluationHom C X K M) ≫
      (ProEtale.derivedTensorHomAdjunction C
        ((ProEtale.comparisonUpperStar C X).mapDerivedCategory.obj K)).counit.app
          ((ProEtale.comparisonUpperStar C X).mapDerivedCategory.obj M) =
    (ProEtale.siteComparisonTensorIso C X K).inv.app (((Etale.derivedHom C X).obj (op K)).obj M) ≫
      (ProEtale.comparisonUpperStar C X).mapDerivedCategory.map
        ((Etale.derivedTensorHomAdjunction C K).counit.app M) := by
  let F := (ProEtale.comparisonUpperStar C X).mapDerivedCategory
  let ad := ProEtale.derivedTensorHomAdjunction C (F.obj K)
  let ev := (ProEtale.siteComparisonTensorIso C X K).inv.app
    (((Etale.derivedHom C X).obj (op K)).obj M) ≫
      F.map ((Etale.derivedTensorHomAdjunction C K).counit.app M)
  have he : ProEtale.siteComparisonEvaluationHom C X K M =
      (ad.homEquiv _ _) ev := by
    rw [ProEtale.siteComparisonEvaluationHom_eq_curry]
    rfl
  rw [he]
  simpa only [F, ad, ev, Functor.id_obj, Adjunction.homEquiv_counit] using
    (ad.homEquiv _ _).symm_apply_apply ev

private theorem site_hom_evaluation
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u}) (K M : Cat A X) :
    ((Sites.tensor true A X).obj ((Sites.nu A X).obj K)).map (Sites.siteHom A X K M) ≫
      (Sites.adj true A X ((Sites.nu A X).obj K)).counit.app ((Sites.nu A X).obj M) =
    (siteTensor A X).inv.app (K, ((Sites.hom false A X).obj (op K)).obj M) ≫
      (Sites.nu A X).map ((Sites.adj false A X K).counit.app M) := by
  rw [site_tensor_inverse_app]
  with_unfolding_all
    exact native_site_hom_evaluation (ModuleCat.{u + 1} A) X K M

private theorem hom_comparison_right_natural
    {C D : Type*} [Category C] [Category D]
    {TC : C ⥤ C ⥤ C} {HC : Cᵒᵖ ⥤ C ⥤ C}
    {TD : D ⥤ D ⥤ D} {HD : Dᵒᵖ ⥤ D ⥤ D}
    (ad : TC ⊣₂ HC) (bd : TD ⊣₂ HD) (F : C ⥤ D)
    (t : Functor.uncurry.obj TC ⋙ F ≅ F.prod F ⋙ Functor.uncurry.obj TD)
    (K : C) {M N : C} (g : M ⟶ N) :
    F.map ((HC.obj (op K)).map g) ≫ paramTensorComparisonHom ad bd F t K N =
      paramTensorComparisonHom ad bd F t K M ≫
        (HD.obj (op (F.obj K))).map (F.map g) := by
  unfold paramTensorComparisonHom
  apply ((bd.adj (F.obj K)).homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_naturality_left_symm,
    Adjunction.homEquiv_naturality_right_symm]
  simp only [Equiv.symm_apply_apply]
  have hn := t.inv.naturality (Prod.mkHom (𝟙 K) ((HC.obj (op K)).map g))
  simp only [Functor.comp_map, Functor.prod_map, Functor.prod_obj,
    Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, NatTrans.id_app,
    Category.id_comp] at hn
  rw [← Category.assoc, hn, Category.assoc, ← F.map_comp]
  simpa only [Functor.comp_map, Functor.id_map, Functor.map_comp, Category.assoc] using
    congrArg (fun z ↦ t.inv.app (K, (HC.obj (op K)).obj M) ≫ F.map z)
      ((ad.adj K).counit.naturality g)

private theorem scalar_hom_right_natural
    (pro : Bool) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) (μ : Sites.TensorComparison pro φ X)
    (K : Sites.D pro A X) {M N : Sites.D pro A X} (g : M ⟶ N) :
    (Sites.scalar pro φ X).map (((Sites.hom pro A X).obj (op K)).map g) ≫
      Sites.homMap pro φ X μ K N =
    Sites.homMap pro φ X μ K M ≫
      ((Sites.hom pro B X).obj (op ((Sites.scalar pro φ X).obj K))).map
        ((Sites.scalar pro φ X).map g) := by
  exact hom_comparison_right_natural (siteAdjunction₂ pro A X) (siteAdjunction₂ pro B X)
    (Sites.scalar pro φ X) μ K g

private theorem native_site_hom_right_natural
    (C : Type (u + 2)) [Category.{u + 1} C] [Abelian C]
    [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
    [MonoidalPreadditive C] [SymmetricCategory C] [MonoidalClosed C]
    [Abelian.HasFunctorialFlatResolution C]
    (X : Scheme.{u}) [(ProEtale.comparisonUpperStar C X).PreservesFlat]
    (K : DerivedCategory (Sheaf X.smallEtaleTopology C))
    {M N : DerivedCategory (Sheaf X.smallEtaleTopology C)} (g : M ⟶ N) :
    (ProEtale.comparisonUpperStar C X).mapDerivedCategory.map
        (((Etale.derivedHom C X).obj (op K)).map g) ≫
      ProEtale.siteComparisonEvaluationHom C X K N =
    ProEtale.siteComparisonEvaluationHom C X K M ≫
      ((ProEtale.derivedHom C X).obj
        (op ((ProEtale.comparisonUpperStar C X).mapDerivedCategory.obj K))).map
          ((ProEtale.comparisonUpperStar C X).mapDerivedCategory.map g) := by
  let F := (ProEtale.comparisonUpperStar C X).mapDerivedCategory
  let : F.Monoidal := ProEtale.siteComparisonDerivedMonoidal C X
  simpa only [F, Etale.derivedHom, ProEtale.derivedHom,
    MonoidalClosed.internalHom, ihom, Functor.comp_map, Functor.comp_obj,
    ProEtale.siteComparisonEvaluationHom] using
      (Functor.LaxMonoidal.ihomComparison F K).natTrans.naturality g

private theorem site_hom_right_natural
    (A : Type (u + 1)) [CommRing A] [Finite A] (X : Scheme.{u})
    (K : Cat A X) {M N : Cat A X} (g : M ⟶ N) :
    (Sites.nu A X).map (((Sites.hom false A X).obj (op K)).map g) ≫
      Sites.siteHom A X K N =
    Sites.siteHom A X K M ≫
      ((Sites.hom true A X).obj (op ((Sites.nu A X).obj K))).map
        ((Sites.nu A X).map g) := by
  with_unfolding_all
    exact native_site_hom_right_natural (ModuleCat.{u + 1} A) X K g

private theorem normalized_site_hom_square
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (X : Scheme.{u})
    (μet : Sites.TensorComparison false φ X) (μpro : Sites.TensorComparison true φ X)
    (het : Sites.NormalizedTensor false φ X μet)
    (hpro : Sites.NormalizedTensor true φ X μpro) (K M : Cat A X) :
    (Sites.scalar true φ X).map (Sites.siteHom A X K M) ≫
      Sites.homMap true φ X μpro ((Sites.nu A X).obj K) ((Sites.nu A X).obj M) ≫
      homAction (Sites.hom true B X) ((Sites.scalarSite φ X).inv.app K)
        ((Sites.scalarSite φ X).hom.app M) =
    (Sites.scalarSite φ X).hom.app (((Sites.hom false A X).obj (op K)).obj M) ≫
      (Sites.nu B X).map (Sites.homMap false φ X μet K M) ≫
      Sites.siteHom B X ((Etale.scalarExtension φ X).obj K)
        ((Etale.scalarExtension φ X).obj M) := by
  have he : μet = Etale.ExceptionalCoefficients.tensorIso φ X := eq_of_heq het
  subst μet
  have h := paramTensorComparisonHom_square_of_evaluation
    (siteAdjunction₂ false A X) (siteAdjunction₂ false B X)
    (siteAdjunction₂ true A X) (siteAdjunction₂ true B X)
    (Sites.scalar false φ X) (Sites.scalar true φ X) (Sites.nu A X) (Sites.nu B X)
    (Etale.ExceptionalCoefficients.tensorIso φ X) μpro (siteTensor A X) (siteTensor B X)
    (Sites.scalarSite φ X).symm
    (Sites.homMap false φ X (Etale.ExceptionalCoefficients.tensorIso φ X))
    (Sites.homMap true φ X μpro) (Sites.siteHom A X) (Sites.siteHom B X)
    (scalar_hom_evaluation false φ X _) (scalar_hom_evaluation true φ X _)
    (site_hom_evaluation A X) (site_hom_evaluation B X)
    (by
      intro U V
      have hs := normalized_site_tensor_square φ X μpro hpro U V
      rw [← siteTensor_hom_app, ← siteTensor_hom_app] at hs
      have hh := inverse_square ((Sites.scalarSite φ X).symm.app (U ⊗ V))
        ((Sites.scalar true φ X).mapIso ((siteTensor A X).app (U, V)))
        (μpro.app ((Sites.nu A X).obj U, (Sites.nu A X).obj V))
        ((Sites.nu B X).mapIso ((Etale.ExceptionalCoefficients.tensorIso φ X).app (U, V)))
        ((siteTensor B X).app ((Sites.scalar false φ X).obj U,
          (Sites.scalar false φ X).obj V))
        (MonoidalCategory.tensorIso ((Sites.scalarSite φ X).symm.app U)
          ((Sites.scalarSite φ X).symm.app V)) hs
      dsimp only [Iso.app, Functor.mapIso, MonoidalCategory.tensorIso, Iso.symm] at hh
      with_unfolding_all
        convert! hh using 1
        rfl) K M
  unfold homAction
  exact h

private theorem dual_square_pasting
    {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (H : C ⥤ C) (H₁ H₂ : D ⥤ D) (τ : H₁ ⟶ H₂)
    {U V Z : C} {A B W R S T : D}
    (w : U ⟶ V) (o : F.obj V ⟶ W) (e : F.obj U ⟶ A) (q : A ⟶ B) (b : B ⟶ W)
    (a₀ : Z ⟶ H.obj U) (b₀ : F.obj (H.obj U) ⟶ H₁.obj (F.obj U))
    (b₁ : F.obj (H.obj V) ⟶ H₁.obj (F.obj V))
    (d : F.obj Z ⟶ R) (c : R ⟶ S) (q' : S ⟶ T)
    (a₁ : S ⟶ H₂.obj A) (a₂ : T ⟶ H₂.obj B) (c' : R ⟶ T)
    (hw : F.map w ≫ o = e ≫ q ≫ b)
    (hn : F.map (H.map w) ≫ b₁ = b₀ ≫ H₁.map (F.map w))
    (hh : F.map a₀ ≫ b₀ ≫ τ.app (F.obj U) ≫ H₂.map e = d ≫ c ≫ a₁)
    (hs : q' ≫ a₂ = a₁ ≫ H₂.map q) (hc : c' = c ≫ q') :
    F.map (a₀ ≫ H.map w) ≫ (b₁ ≫ H₁.map o) ≫ τ.app W =
      d ≫ c' ≫ a₂ ≫ H₂.map b := by
  rw [hc]
  simp only [F.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← H₁.map_comp_assoc, τ.naturality, hw]
  simp only [H₂.map_comp]
  rw [reassoc_of% hh, ← reassoc_of% hs]

/-- The fixed coefficient/site bridges satisfy the four site squares.

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraphs 1--3;
(blueprint: lem-sf-normalized-stage-comparison-site-equations).

Proof: closed square: bounded constructibility makes the site-adjunction unit at `M`
invertible, naturality of the finite direct-image comparison transfers invertibility along
its closed exceptional image, right-mate naturality and the site-adjunction triangle
identify both sides. Dualizing square: the source omega bridge cancels against its
prescribed inverse. Hom square: the normalized scalar/site tensor square
(`normalized_site_tensor_square`) is transposed through the four evaluation maps by the
parametrized tensor-Hom square theorem. Verdier square: the Hom square at the etale
dualizing object, covariant naturality of the scalar and site Hom maps and the dualizing
square, combined by functoriality of internal Hom. -/
theorem normalized_stage_comparison_site_equations
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type (u + 1)) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (T X Z : Scheme.{u})
    [T.Over (Spec (.of D.k))] [X.Over (Spec (.of D.k))] [Z.Over (Spec (.of D.k))]
    [IsSeparated (T ↘ Spec (.of D.k))] [LocallyOfFiniteType (T ↘ Spec (.of D.k))]
    [QuasiCompact (T ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))] [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (Z ↘ Spec (.of D.k))] [LocallyOfFiniteType (Z ↘ Spec (.of D.k))]
    [QuasiCompact (Z ↘ Spec (.of D.k))]
    (f : T ⟶ X) [f.IsOver (Spec (.of D.k))]
    [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (.of D.k))]
    (c : Compactification (X ↘ Spec (.of D.k)))
    (μ : ∀ pro : Bool, ∀ {s t : Stage l E} (a : Arrow s t),
      Sites.TensorComparison pro a.ringMap X)
    (hμ : ∀ (pro : Bool) {s t : Stage l E} (a : Arrow s t),
      Sites.NormalizedTensor pro a.ringMap X (μ pro a))
    (σ : ∀ (pro : Bool) (s : Stage l E),
      Sites.tensor pro s.ring X ≅ (Sites.tensor pro s.ring X).flip)
    (hσ : ∀ (pro : Bool) (s : Stage l E),
      Sites.NormalizedSymmetry pro s.ring X (σ pro s))
    (hi : ∀ pro : Bool, Sites.StageComparisonIsomorphisms pro l E f i c (μ pro))
    (hsi : letI := c.hasCompactification
      Sites.StageComparisonSiteIsomorphisms l E f i c) :
    Sites.StageComparisonSiteEquations l E f i c (μ false) (μ true) := by
  clear hl hσ hi
  letI := c.hasCompactification
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s t a M hM
    with_unfolding_all
      let ad := ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} s.ring) X
      let bd := ProEtale.derivedComparisonAdjunction (ModuleCat.{u + 1} t.ring) X
      let η : M ⟶ (Sites.rnu s.ring X).obj ((Sites.nu s.ring X).obj M) :=
        ad.unit.app M
      have hplus : DerivedCategory.TStructure.t.plus M :=
        ((boundedConstructible_iff_source s.ring X M).1 hM.1).1.1
      have hη : IsIso η :=
        ProEtale.isIso_derivedComparisonAdjunction_unit_app _ X M hplus
      letI := hη
      let α : R(Etale.lowerStar (ModuleCat.{u + 1} s.ring) i) ⋙
          Etale.scalarExtension a.ringMap X ⟶
          Etale.scalarExtension a.ringMap Z ⋙
            R(Etale.lowerStar (ModuleCat.{u + 1} t.ring) i) := {
        app := Etale.finiteCoefficientDirectImageMap a.ringMap i
        naturality := fun _ _ g ↦
          Etale.finiteCoefficientDirectImageMap_naturality a.ringMap i g }
      haveI : IsIso (Etale.finiteCoefficientDirectImageMap a.ringMap i
          ((closedUpper s.ring i).obj M)) := hsi.closed_direct_iso a M hM
      haveI : IsIso (α.app ((closedUpper s.ring i).obj M)) := inferInstanceAs
        (IsIso (Etale.finiteCoefficientDirectImageMap a.ringMap i
          ((closedUpper s.ring i).obj M)))
      haveI : IsIso (α.app ((closedUpper s.ring i).obj
          ((Sites.rnu s.ring X).obj ((Sites.nu s.ring X).obj M)))) :=
        (NatTrans.isIso_app_iff_of_iso α ((closedUpper s.ring i).mapIso (asIso η))).1
          inferInstance
      haveI : IsIso (Etale.finiteCoefficientDirectImageMap a.ringMap i
          ((closedUpper s.ring i).obj ((Sites.rnu s.ring X).obj
            ((Sites.nu s.ring X).obj M)))) := inferInstanceAs
        (IsIso (α.app ((closedUpper s.ring i).obj
          ((Sites.rnu s.ring X).obj ((Sites.nu s.ring X).obj M)))))
      have hn := etale_closed_natural a.ringMap i (K := M) η
      have hu := mate_unit_square ad bd (Sites.scalar false a.ringMap X)
        (Sites.scalar true a.ringMap X) (Sites.scalarSite a.ringMap X) M
      exact transported_natural_square (Etale.scalarExtension a.ringMap X)
        (closedUpper s.ring i) (closedUpper t.ring i)
        (Etale.scalarExtension a.ringMap Z) (Sites.nu s.ring Z) (Sites.nu t.ring Z)
        (Sites.scalar true a.ringMap Z) (Sites.scalarSite a.ringMap Z) η
        (closedMap a.ringMap i M) (closedMap a.ringMap i _)
        (Sites.rnuScalar a.ringMap X _) ((Sites.rnu t.ring X).map
          ((Sites.scalarSite a.ringMap X).hom.app M)) (bd.unit.app _)
        hn hu
  · intro s t a
    haveI := omega_bridge_iso s.ring c
    with_unfolding_all
      exact map_inverse_cancel (Sites.scalar true a.ringMap X) (Sites.omegaBridge s.ring c)
        ((Sites.scalarSite a.ringMap X).hom.app (omega s.ring c) ≫
          (Sites.nu t.ring X).map (omegaMap a.ringMap c) ≫ Sites.omegaBridge t.ring c)
  · intro s t a K M _ _
    exact normalized_site_hom_square a.ringMap X (μ false a) (μ true a)
      (hμ false a) (hμ true a) K M
  · intro s t a K _
    with_unfolding_all
      let Φ := Sites.scalar true a.ringMap X
      let HB := Sites.hom true t.ring X
      let e := Sites.scalarSite a.ringMap X
      let NK := (Sites.nu s.ring X).obj K
      let SK := (Sites.scalar false a.ringMap X).obj K
      let WA := omega s.ring c
      let WB := omega t.ring c
      have hh := normalized_site_hom_square a.ringMap X (μ false a) (μ true a)
        (hμ false a) (hμ true a) K WA
      dsimp only [homAction] at hh
      have hn := scalar_hom_right_natural true a.ringMap X (μ true a) NK
        (Sites.omegaBridge s.ring c)
      have hs := site_hom_right_natural t.ring X SK (omegaMap a.ringMap c)
      haveI := omega_bridge_iso s.ring c
      have hw := map_inverse_cancel Φ (Sites.omegaBridge s.ring c)
        (e.hom.app WA ≫ (Sites.nu t.ring X).map (omegaMap a.ringMap c) ≫
          Sites.omegaBridge t.ring c)
      change Φ.map (Sites.omegaBridge s.ring c) ≫ Sites.stageOmegaMap true a c = _ at hw
      exact dual_square_pasting Φ ((Sites.hom true s.ring X).obj (op NK))
        (HB.obj (op (Φ.obj NK))) (HB.obj (op ((Sites.nu t.ring X).obj SK)))
        (HB.map (e.inv.app K).op)
        (Sites.omegaBridge s.ring c) (Sites.stageOmegaMap true a c)
        (e.hom.app WA) ((Sites.nu t.ring X).map (omegaMap a.ringMap c))
        (Sites.omegaBridge t.ring c) (Sites.siteHom s.ring X K WA)
        (Sites.homMap true a.ringMap X (μ true a) NK ((Sites.nu s.ring X).obj WA))
        (Sites.homMap true a.ringMap X (μ true a) NK (Sites.omega true s.ring c))
        (e.hom.app (((Sites.hom false s.ring X).obj (op K)).obj WA))
        ((Sites.nu t.ring X).map (Sites.homMap false a.ringMap X (μ false a) K WA))
        ((Sites.nu t.ring X).map
          (((Sites.hom false t.ring X).obj (op SK)).map (omegaMap a.ringMap c)))
        (Sites.siteHom t.ring X SK ((Etale.scalarExtension a.ringMap X).obj WA))
        (Sites.siteHom t.ring X SK WB)
        ((Sites.nu t.ring X).map (Sites.dualMap false a.ringMap c (μ false a)
          (Sites.stageOmegaMap false a c) K)) hw hn hh hs
        ((Sites.nu t.ring X).map_comp _ _)

end WeilConjectures.FiniteFreeCoefficients
