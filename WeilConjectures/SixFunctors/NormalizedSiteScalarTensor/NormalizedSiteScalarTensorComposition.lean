/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.Finite.Coefficient.FiniteCoefficientVerdierData
import all WeilConjectures.AlgebraicGeometry.ExceptionalCoefficients.ExceptionalCoefficientMaps
import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidalPresheaf
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.NaturalTransformationOplax
import all WeilConjectures.AlgebraicGeometry.Scalar.ScalarPullbackIsoExistence
import all WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorCoherence
import all WeilConjectures.AlgebraicGeometry.Etale.Scalar.EtaleScalarPullbackTensorKFlat
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition
import WeilConjectures.CategoryTheory.Exact.ExactRestrictionCompositionSupplement
import WeilConjectures.CategoryTheory.Adjunction.Derived.DerivedAdjointCochainCounit

/-! # Composition of the normalized scalar tensorator on an essentially small site

Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraph 3.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry WeilConjectures
open scoped CategoryTheory.Functor
namespace WeilConjectures.NormalizedSiteScalarTensor

attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
open AlgebraicGeometry.Etale.ExceptionalCoefficients

-- Generic adjunction and tensor calculations, adapted from EtaleScalarTensorComposition.
namespace CompositionProof

open AlgebraicGeometry.Etale

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem representative_transpose
    {C D V W : Type*} [Category C] [Category D] [Category V] [Category W]
    (QC : C ⥤ V) (QD : D ⥤ W) (FC : C ⥤ D) (UC : D ⥤ C)
    (E : V ⥤ W) (U : W ⥤ V) (adj : E ⊣ U)
    (a : FC ⊣ UC) (fac : UC ⋙ QC ≅ QD ⋙ U)
    (P : C) (K : D) (f : FC.obj P ⟶ K) :
    adj.homEquiv _ _
      ((adjointRepresentative QC QD FC UC E U adj a fac).app P ≫ QD.map f) =
    QC.map (a.homEquiv _ _ f) ≫ fac.hom.app K := by
  rw [adj.homEquiv_naturality_right]
  change adj.homEquiv _ _ ((adj.homEquiv _ _).symm _) ≫ _ = _
  rw [Equiv.apply_symm_apply]
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  have hn := fac.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, ← hn, ← Category.assoc, ← QC.map_comp, Adjunction.homEquiv_unit]

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem left_comp_unit
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} {L' : B ⥤ C} {R' : C ⥤ B}
    {L'' : A ⥤ C} {R'' : C ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (c : L'' ⊣ R'') (η : R' ⋙ R ≅ R'') (M : A) :
    (a.comp b).homEquiv M _ ((Adjunction.leftAdjointCompIso a b c η).hom.app M) ≫
      η.hom.app (L''.obj M) = c.unit.app M := by
  rw [Adjunction.homEquiv_unit, Category.assoc, η.hom.naturality, ← Category.assoc]
  have hu := unit_conjugateEquiv (a.comp b) c
    (Adjunction.leftAdjointCompIso a b c η).inv M
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv] at hu
  rw [hu, Category.assoc, ← R''.map_comp, Iso.inv_hom_id_app, R''.map_id]
  exact Category.comp_id _

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem left_comp_unique
    {A B C : Type*} [Category A] [Category B] [Category C]
    {L : A ⥤ B} {R : B ⥤ A} {L' : B ⥤ C} {R' : C ⥤ B}
    {L'' : A ⥤ C} {R'' : C ⥤ A}
    (a : L ⊣ R) (b : L' ⊣ R') (c : L'' ⊣ R'') (η : R' ⋙ R ≅ R'') :
    ((a.comp b).ofNatIsoRight η).leftAdjointUniq c =
      Adjunction.leftAdjointCompIso a b c η := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (((a.comp b).ofNatIsoRight η).homEquiv M _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_ofNatIsoRight_apply]
  exact (left_comp_unit a b c η M).symm

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem representative_composition
    {A B C DA DB DC : Type*}
    [Category A] [Category B] [Category C]
    [Category DA] [Category DB] [Category DC]
    (QA : A ⥤ DA) (QB : B ⥤ DB) (QC : C ⥤ DC)
    {F : A ⥤ B} {R : B ⥤ A} {G : B ⥤ C} {S : C ⥤ B}
    {H : A ⥤ C} {U : C ⥤ A}
    {FD : DA ⥤ DB} {RD : DB ⥤ DA} {GD : DB ⥤ DC} {SD : DC ⥤ DB}
    {HD : DA ⥤ DC} {UD : DC ⥤ DA}
    (a : F ⊣ R) (b : G ⊣ S) (c : H ⊣ U)
    (ad : FD ⊣ RD) (bd : GD ⊣ SD) (cd : HD ⊣ UD)
    (fA : R ⋙ QA ≅ QB ⋙ RD) (fB : S ⋙ QB ≅ QC ⋙ SD)
    (fC : U ⋙ QA ≅ QC ⋙ UD)
    (η : S ⋙ R ≅ U) (δ : SD ⋙ RD ≅ UD) (ν : F ⋙ G ⟶ H)
    (hν : ∀ P, (a.comp b).homEquiv _ _ (ν.app P) ≫
      η.hom.app (H.obj P) = c.unit.app P)
    (hρ : ∀ K, fA.hom.app (S.obj K) ≫ RD.map (fB.hom.app K) ≫
      δ.hom.app (QC.obj K) = QA.map (η.hom.app K) ≫ fC.hom.app K)
    (P : A) :
    (Adjunction.leftAdjointCompIso ad bd cd δ).hom.app (QA.obj P) ≫
        (adjointRepresentative QA QC H U HD UD cd c fC).app P =
      GD.map ((adjointRepresentative QA QB F R FD RD ad a fA).app P) ≫
        (adjointRepresentative QB QC G S GD SD bd b fB).app (F.obj P) ≫
        QC.map (ν.app P) := by
  rw [← left_comp_unique ad bd cd δ]
  simpa only [Category.assoc] using
    normalizedAdjunction_uniqueness (a.comp b) c (ad.comp bd) cd
    (fun K ↦ GD.map ((adjointRepresentative QA QB F R FD RD ad a fA).app K) ≫
      (adjointRepresentative QB QC G S GD SD bd b fB).app (F.obj K))
    (adjointRepresentative QA QC H U HD UD cd c fC).app
    (fun K ↦ fA.hom.app (S.obj K) ≫ RD.map (fB.hom.app K)) fC.hom.app
    (by
      intro K L f
      simpa only [Category.assoc] using
        normalizedAdjunction_composition a b ad bd
          (adjointRepresentative QA QB F R FD RD ad a fA)
          (adjointRepresentative QB QC G S GD SD bd b fB) fA.hom fB.hom
          (representative_transpose QA QB F R FD RD ad a fA)
          (representative_transpose QB QC G S GD SD bd b fB) K L f)
    (representative_transpose QA QC H U HD UD cd c fC) η δ ν.app hν
    (by intro K; simpa only [Category.assoc] using hρ K) P

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem complex_compositor_tensor
    {C D E : Type*}
    [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
    [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E] [BraidedCategory E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [F.IsLeftAdjoint] [G.IsLeftAdjoint] [H.IsLeftAdjoint]
    [F.Monoidal] [G.Monoidal] [H.Monoidal]
    (ν : F ⋙ G ≅ H) [NatTrans.IsMonoidal ν.hom] (K L : CochainComplex C ℤ) :
    (Functor.mapHomologicalComplexCompIso ν (.up ℤ)).hom.app (K ⊗ L) ≫
        complexTensorMap H K L =
      (G.mapHomologicalComplex (.up ℤ)).map (complexTensorMap F K L) ≫
        complexTensorMap G ((F.mapHomologicalComplex (.up ℤ)).obj K)
          ((F.mapHomologicalComplex (.up ℤ)).obj L) ≫
        ((Functor.mapHomologicalComplexCompIso ν (.up ℤ)).hom.app K ⊗ₘ
          (Functor.mapHomologicalComplexCompIso ν (.up ℤ)).hom.app L) := by
  have hn := Functor.mapHomologicalComplexδNatTrans_naturality ν.hom K L
  rw [Functor.mapHomologicalComplexδNatTrans_comp] at hn
  have he (M) : (Functor.mapHomologicalComplexCompIso ν (.up ℤ)).hom.app M =
      (NatTrans.mapHomologicalComplex ν.hom (.up ℤ)).app M := by
    ext i
    rfl
  simpa only [complexTensorMap, he, Category.assoc] using hn

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem normalized_composition_tensor
    {C D E C' D' E' : Type*}
    [Category C] [Category D] [Category E] [Category C'] [Category D'] [Category E']
    [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E]
    [MonoidalCategory C'] [MonoidalCategory D'] [MonoidalCategory E']
    (Q : C ⥤ C') (R : D ⥤ D') (S : E ⥤ E')
    [Q.LaxMonoidal] [R.LaxMonoidal] [S.LaxMonoidal]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    (dF₀ : ∀ X Y, F.obj (X ⊗ Y) ⟶ F.obj X ⊗ F.obj Y)
    (dG₀ : ∀ X Y, G.obj (X ⊗ Y) ⟶ G.obj X ⊗ G.obj Y)
    (dH₀ : ∀ X Y, H.obj (X ⊗ Y) ⟶ H.obj X ⊗ H.obj Y)
    (LF : C' ⥤ D') (LG : D' ⥤ E') (LH : C' ⥤ E')
    (rF : Q ⋙ LF ⟶ F ⋙ R) (rG : R ⋙ LG ⟶ G ⋙ S) (rH : Q ⋙ LH ⟶ H ⋙ S)
    (dF : ∀ X Y, LF.obj (X ⊗ Y) ⟶ LF.obj X ⊗ LF.obj Y)
    (dG : ∀ X Y, LG.obj (X ⊗ Y) ⟶ LG.obj X ⊗ LG.obj Y)
    (dH : ∀ X Y, LH.obj (X ⊗ Y) ⟶ LH.obj X ⊗ LH.obj Y)
    (hF : ∀ P T, dF (Q.obj P) (Q.obj T) ≫ (rF.app P ⊗ₘ rF.app T) ≫
      Functor.LaxMonoidal.μ R (F.obj P) (F.obj T) =
      LF.map (Functor.LaxMonoidal.μ Q P T) ≫ rF.app (P ⊗ T) ≫ R.map (dF₀ P T))
    (hG : ∀ P T, dG (R.obj P) (R.obj T) ≫ (rG.app P ⊗ₘ rG.app T) ≫
      Functor.LaxMonoidal.μ S (G.obj P) (G.obj T) =
      LG.map (Functor.LaxMonoidal.μ R P T) ≫ rG.app (P ⊗ T) ≫ S.map (dG₀ P T))
    (hH : ∀ P T, dH (Q.obj P) (Q.obj T) ≫ (rH.app P ⊗ₘ rH.app T) ≫
      Functor.LaxMonoidal.μ S (H.obj P) (H.obj T) =
      LH.map (Functor.LaxMonoidal.μ Q P T) ≫ rH.app (P ⊗ T) ≫ S.map (dH₀ P T))
    (hn : ∀ {X X' Y Y' : D'} (f : X ⟶ X') (g : Y ⟶ Y'),
      LG.map (f ⊗ₘ g) ≫ dG X' Y' = dG X Y ≫ (LG.map f ⊗ₘ LG.map g))
    (a : LF ⋙ LG ≅ LH) (t : F ⋙ G ≅ H)
    (ht : ∀ P T, t.hom.app (P ⊗ T) ≫ dH₀ P T =
      G.map (dF₀ P T) ≫ dG₀ (F.obj P) (F.obj T) ≫ (t.hom.app P ⊗ₘ t.hom.app T))
    (hr : ∀ K, a.hom.app (Q.obj K) ≫ rH.app K =
      LG.map (rF.app K) ≫ rG.app (F.obj K) ≫ S.map (t.hom.app K))
    (P T : C) [IsIso (Functor.LaxMonoidal.μ Q P T)] [IsIso (rH.app (P ⊗ T))]
    [IsIso (dH₀ P T)] [IsIso (dH (Q.obj P) (Q.obj T))] :
    a.hom.app (Q.obj P ⊗ Q.obj T) ≫ dH (Q.obj P) (Q.obj T) =
      LG.map (dF (Q.obj P) (Q.obj T)) ≫ dG (LF.obj (Q.obj P)) (LF.obj (Q.obj T)) ≫
        (Functor.uncurry.obj (curriedTensor E')).map
          (Prod.mkHom (a.hom.app (Q.obj P)) (a.hom.app (Q.obj T))) := by
  let rFG : Q ⋙ (LF ⋙ LG) ⟶ (F ⋙ G) ⋙ S :=
    Functor.whiskerRight rF LG ≫ Functor.whiskerLeft F rG
  let dFG := fun K L ↦ LG.map (dF K L) ≫ dG (LF.obj K) (LF.obj L)
  let dFG₀ := fun K L ↦ G.map (dF₀ K L) ≫ dG₀ (F.obj K) (F.obj L)
  have hcomp := normalized_tensor_comp Q R S F G dF₀ dG₀ LF LG rF rG dF dG hF hG hn
  have : IsIso (dH (Q.obj P) (Q.obj T) ≫ (rH.app P ⊗ₘ rH.app T) ≫
      Functor.LaxMonoidal.μ S (H.obj P) (H.obj T)) := by
    rw [hH]
    infer_instance
  have : IsIso ((rH.app P ⊗ₘ rH.app T) ≫
      Functor.LaxMonoidal.μ S (H.obj P) (H.obj T)) :=
    IsIso.of_isIso_comp_left (dH (Q.obj P) (Q.obj T)) _
  have hc := normalized_tensor_transport Q S (F ⋙ G) H dFG₀ dH₀ (LF ⋙ LG) LH
    a.hom t.hom rFG rH dFG dH
    (by simpa only [rFG, dFG, dFG₀, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.comp_obj, Functor.comp_map] using hcomp)
    hH (by intro K L; simpa only [dFG₀, Category.assoc] using ht K L) P T
    (by simpa only [rFG, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc] using hr P)
    (by simpa only [rFG, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc] using hr T)
    (by simpa only [rFG, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Category.assoc] using hr (P ⊗ T))
  simpa only [dFG, Functor.uncurry_obj_map, curriedTensor_map_app,
    curriedTensor_obj_map, MonoidalCategory.tensorHom_def, Category.assoc] using hc

attribute [-instance] CategoryTheory.catToReflQuiver in
private theorem normalized_cochain_composition
    {C D E : Type*}
    [Category.{u + 1} C] [Abelian C] [IsGrothendieckAbelian.{u + 1} C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
    [HasDerivedCategory.{u + 1} C] [Abelian.HasFunctorialFlatResolution C]
    [Category.{u + 1} D] [Abelian D] [IsGrothendieckAbelian.{u + 1} D]
    [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalClosed D] [BraidedCategory D]
    [HasDerivedCategory.{u + 1} D] [Abelian.HasFunctorialFlatResolution D]
    [Category.{u + 1} E] [Abelian E] [IsGrothendieckAbelian.{u + 1} E]
    [MonoidalCategory E] [MonoidalPreadditive E] [MonoidalClosed E] [BraidedCategory E]
    [HasDerivedCategory.{u + 1} E] [Abelian.HasFunctorialFlatResolution E]
    (F : C ⥤ D) (G : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [G.Additive] [H.Additive]
    [F.IsLeftAdjoint] [G.IsLeftAdjoint] [H.IsLeftAdjoint]
    [F.Monoidal] [G.Monoidal] [H.Monoidal]
    (LF : _root_.DerivedCategory C ⥤ _root_.DerivedCategory D)
    (LG : _root_.DerivedCategory D ⥤ _root_.DerivedCategory E)
    (LH : _root_.DerivedCategory C ⥤ _root_.DerivedCategory E)
    (rF : _root_.DerivedCategory.Q ⋙ LF ⟶
      F.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q)
    (rG : _root_.DerivedCategory.Q ⋙ LG ⟶
      G.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q)
    (rH : _root_.DerivedCategory.Q ⋙ LH ⟶
      H.mapHomologicalComplex (.up ℤ) ⋙ _root_.DerivedCategory.Q)
    (repF : ∀ K, LF.obj (_root_.DerivedCategory.Q.obj K) ⟶
      _root_.DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K))
    (repG : ∀ K, LG.obj (_root_.DerivedCategory.Q.obj K) ⟶
      _root_.DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj K))
    (repH : ∀ K, LH.obj (_root_.DerivedCategory.Q.obj K) ⟶
      _root_.DerivedCategory.Q.obj ((H.mapHomologicalComplex (.up ℤ)).obj K))
    (hrF : ∀ K, rF.app K = repF K) (hrG : ∀ K, rG.app K = repG K)
    (hrH : ∀ K, rH.app K = repH K)
    (δF : Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ LF ≅
      LF.prod LF ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory D)))
    (δG : Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory D)) ⋙ LG ≅
      LG.prod LG ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory E)))
    (δH : Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory C)) ⋙ LH ≅
      LH.prod LH ⋙ Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory E)))
    (hF : TensorNormalizationAux F LF repF δF)
    (hG : TensorNormalizationAux G LG repG δG)
    (hH : TensorNormalizationAux H LH repH δH)
    (a : LF ⋙ LG ≅ LH) (ν : F ⋙ G ≅ H) [NatTrans.IsMonoidal ν.hom]
    (hrep : ∀ K, a.hom.app (_root_.DerivedCategory.Q.obj K) ≫ repH K =
      LG.map (repF K) ≫ repG ((F.mapHomologicalComplex (.up ℤ)).obj K) ≫
        _root_.DerivedCategory.Q.map
          ((Functor.mapHomologicalComplexCompIso ν (.up ℤ)).hom.app K))
    (hiso : ∀ K, (HomologicalComplex.quasiIso C (.up ℤ)).kFlat K → IsIso (rH.app K))
    (P Q : CochainComplex C ℤ)
    (hP : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso C (.up ℤ)).kFlat Q) :
    a.hom.app (_root_.DerivedCategory.Q.obj P ⊗ _root_.DerivedCategory.Q.obj Q) ≫
        δH.hom.app (_root_.DerivedCategory.Q.obj P, _root_.DerivedCategory.Q.obj Q) =
      LG.map (δF.hom.app (_root_.DerivedCategory.Q.obj P, _root_.DerivedCategory.Q.obj Q)) ≫
        δG.hom.app (LF.obj (_root_.DerivedCategory.Q.obj P),
          LF.obj (_root_.DerivedCategory.Q.obj Q)) ≫
        (Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory E))).map
          (Prod.mkHom (a.hom.app (_root_.DerivedCategory.Q.obj P))
            (a.hom.app (_root_.DerivedCategory.Q.obj Q))) := by
  have : IsIso (Functor.LaxMonoidal.μ _root_.DerivedCategory.Q P Q) := by
    rw [AlgebraicGeometry.Etale.quotient_tensorator]
    exact DerivedMonoidal.isIso_counit_app_app_of_kFlat_left _root_.DerivedCategory.Qh
      (HomotopyCategory.quasiIso C (.up ℤ)) _ _
      ((HomotopyCategory.kFlat_quotient_obj_iff P).2 hP)
  have := hiso (P ⊗ Q) (ObjectProperty.prop_tensor hP hQ)
  apply normalized_composition_tensor
    _root_.DerivedCategory.Q _root_.DerivedCategory.Q _root_.DerivedCategory.Q
    (F.mapHomologicalComplex (.up ℤ)) (G.mapHomologicalComplex (.up ℤ))
    (H.mapHomologicalComplex (.up ℤ)) (complexTensorMap F) (complexTensorMap G)
    (complexTensorMap H) LF LG LH rF rG rH
    (fun K L ↦ δF.hom.app (K, L)) (fun K L ↦ δG.hom.app (K, L))
    (fun K L ↦ δH.hom.app (K, L))
    (by intro K L; simpa only [hrF, complexTensorMap] using hF K L)
    (by intro K L; simpa only [hrG, complexTensorMap] using hG K L)
    (by intro K L; simpa only [hrH, complexTensorMap] using hH K L)
    (uncurried_tensor_naturality LG δG.hom) a
    (Functor.mapHomologicalComplexCompIso ν (.up ℤ))
    (complex_compositor_tensor F G H ν)
    (by intro K; simpa only [hrF, hrG, hrH] using hrep K) P Q

end CompositionProof

variable {V : Type (u + 1)} [Category.{u} V] [EssentiallySmall.{u + 1} V]

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
private def ordinaryComp
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    (J : GrothendieckTopology V) :
    finiteVerdierOrdinaryExtension J φ ⋙ finiteVerdierOrdinaryExtension J ψ ≅
      finiteVerdierOrdinaryExtension J χ :=
  Adjunction.leftAdjointCompIso
    (finiteVerdierOrdinaryAdjunction J φ)
    (finiteVerdierOrdinaryAdjunction J ψ)
    (finiteVerdierOrdinaryAdjunction J χ)
    (Sheaf.restrictScalarsCompIso J φ ψ χ hχ)

section OrdinaryComposition
attribute [local instance] Sheaf.monoidalCategory Sheaf.braidedCategory
open Functor.LaxMonoidal
variable {R₁ R₂ R₃ : Type (u + 1)} [CommRing R₁] [CommRing R₂] [CommRing R₃]
  (f : R₁ →+* R₂) (g : R₂ →+* R₃) (J : GrothendieckTopology V)

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
private theorem restrictScalars_tensor_comp (M N : ModuleCat.{u + 1} R₃) :
    «μ» (ModuleCat.restrictScalars.{u + 1} f) ((ModuleCat.restrictScalars.{u + 1} g).obj M)
        ((ModuleCat.restrictScalars.{u + 1} g).obj N) ≫
      (ModuleCat.restrictScalars.{u + 1} f).map («μ» (ModuleCat.restrictScalars.{u + 1} g) M N) =
    «μ» (ModuleCat.restrictScalars.{u + 1} (g.comp f)) M N := by
  refine ModuleCat.MonoidalCategory.tensor_ext fun s t ↦ ?_
  have h₁ := ModuleCat.restrictScalars_μ_tmul f ((ModuleCat.restrictScalars.{u + 1} g).obj M)
    ((ModuleCat.restrictScalars.{u + 1} g).obj N) s t
  have h₂ := ModuleCat.restrictScalars_μ_tmul g M N s t
  have h₃ := ModuleCat.restrictScalars_μ_tmul (g.comp f) M N s t
  exact (congrArg (fun x ↦ ((ModuleCat.restrictScalars.{u + 1} f).map
    («μ» (ModuleCat.restrictScalars.{u + 1} g) M N)).hom x) h₁).trans (h₂.trans h₃.symm)

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
/-- Restriction of scalars of sheaves along `g` and then `f` is restriction of scalars along
`g ∘ f`. -/
private def restrictionComp :
    sheafCompose J (ModuleCat.restrictScalars.{u + 1} g) ⋙
        sheafCompose J (ModuleCat.restrictScalars.{u + 1} f) ≅
      sheafCompose J (ModuleCat.restrictScalars.{u + 1} (g.comp f)) :=
  Iso.refl _

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
omit [EssentiallySmall.{u + 1} V] in
/-- The identification of the restrictions of scalars along `f ∘ g` in one or two steps is
monoidal. -/
private theorem restrictionComp_monoidal :
    NatTrans.IsMonoidal (restrictionComp f g J).hom where
  unit := by
    apply Sheaf.hom_ext_of_ε_comp
    have h₁ := Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose J
      (ModuleCat.restrictScalars.{u + 1} (g.comp f))
    have h₂ := Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose J
      (ModuleCat.restrictScalars.{u + 1} f)
    have h₃ := Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose J
      (ModuleCat.restrictScalars.{u + 1} g)
    simp only [comp_ε, restrictionComp, Iso.refl_hom, NatTrans.id_app,
      Category.comp_id, Functor.map_comp]
    rw [h₁, reassoc_of% h₂]
    rw [show (sheafToPresheaf _ _).map ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1}
        f)).map (ε (sheafCompose J
          (ModuleCat.restrictScalars.{u + 1} g)))) =
        ((Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars.{u + 1} f)).map
          ((sheafToPresheaf _ _).map (ε (sheafCompose J
          (ModuleCat.restrictScalars.{u + 1} g)))) from rfl, ← Functor.map_comp, h₃]
    have key : ε ((Functor.whiskeringRight Vᵒᵖ _ _).obj
          (ModuleCat.restrictScalars.{u + 1} f)) ≫
        ((Functor.whiskeringRight Vᵒᵖ _ _).obj (ModuleCat.restrictScalars.{u + 1} f)).map
          (ε ((Functor.whiskeringRight Vᵒᵖ _ _).obj (ModuleCat.restrictScalars.{u + 1} g))) =
        ε ((Functor.whiskeringRight Vᵒᵖ _ _).obj
          (ModuleCat.restrictScalars.{u + 1} (g.comp f))) := by
      ext U : 2
      apply ModuleCat.hom_ext
      ext
      simp only [NatTrans.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply]
      erw [ModuleCat.restrictScalars_η, ModuleCat.restrictScalars_η, ModuleCat.restrictScalars_η]
      rfl
    rw [Functor.map_comp, ← Category.assoc]
    erw [key]
    rfl
  tensor P Q := by
    apply Sheaf.hom_ext_of_μ_comp
    have h₁ := Sheaf.μ_sheafToPresheaf_comp_map_μ_sheafCompose J
      (ModuleCat.restrictScalars.{u + 1} (g.comp f)) P Q
    have h₂ := Sheaf.μ_sheafToPresheaf_comp_map_μ_sheafCompose J
      (ModuleCat.restrictScalars.{u + 1} f)
      ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1} g)).obj P)
      ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1} g)).obj Q)
    have h₃ := Sheaf.μ_sheafToPresheaf_comp_map_μ_sheafCompose J
      (ModuleCat.restrictScalars.{u + 1} g) P Q
    simp only [comp_μ, restrictionComp, Iso.refl_hom, NatTrans.id_app,
      Category.comp_id, Functor.map_comp, tensorHom_id, id_whiskerRight, Category.id_comp]
    erw [h₁]
    erw [reassoc_of% h₂]
    rw [show (sheafToPresheaf _ _).map ((sheafCompose _ (ModuleCat.restrictScalars.{u + 1}
        f)).map («μ» (sheafCompose J
          (ModuleCat.restrictScalars.{u + 1} g)) P Q)) =
        ((Functor.whiskeringRight _ _ _).obj (ModuleCat.restrictScalars.{u + 1} f)).map
          ((sheafToPresheaf _ _).map («μ» (sheafCompose J
          (ModuleCat.restrictScalars.{u + 1} g)) P Q)) from rfl, ← Functor.map_comp, h₃]
    have key : «μ» ((Functor.whiskeringRight Vᵒᵖ _ _).obj
          (ModuleCat.restrictScalars.{u + 1} f)) _ _ ≫
        ((Functor.whiskeringRight Vᵒᵖ _ _).obj (ModuleCat.restrictScalars.{u + 1} f)).map
          («μ» ((Functor.whiskeringRight Vᵒᵖ _ _).obj
            (ModuleCat.restrictScalars.{u + 1} g)) P.obj Q.obj) =
        «μ» ((Functor.whiskeringRight Vᵒᵖ _ _).obj
          (ModuleCat.restrictScalars.{u + 1} (g.comp f))) P.obj Q.obj := by
      ext U : 2
      exact restrictScalars_tensor_comp f g _ _
    rw [Functor.map_comp, ← Category.assoc]
    erw [key]
    rfl

end OrdinaryComposition

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
private theorem ordinaryComp_monoidal
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    (J : GrothendieckTopology V) : NatTrans.IsMonoidal (ordinaryComp φ ψ χ hχ J).hom := by
  subst χ
  have he : Sheaf.restrictScalarsCompIso J φ ψ (ψ.comp φ) rfl =
      restrictionComp φ ψ J := by
    apply Iso.ext
    ext P U x
    rfl
  have hm := restrictionComp_monoidal φ ψ J
  rw [← he] at hm
  let a := finiteVerdierOrdinaryAdjunction J φ
  let b := finiteVerdierOrdinaryAdjunction J ψ
  let c := finiteVerdierOrdinaryAdjunction J (ψ.comp φ)
  let η := Sheaf.restrictScalarsCompIso J φ ψ (ψ.comp φ) rfl
  have hm' : NatTrans.IsMonoidal η.hom := hm
  have := CategoryTheory.Adjunction.isMonoidal_ofNatIsoRight (a.comp b) η
  rw [ordinaryComp, ← CompositionProof.left_comp_unique]
  exact Adjunction.isMonoidal_leftAdjointUniq_hom _ c

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
private theorem scalar_comp_rep
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    (J : GrothendieckTopology V)
    (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ) :
    (ProEtale.pbcFixedScalarExtensionComp J φ ψ χ hχ).hom.app
        (_root_.DerivedCategory.Q.obj P) ≫ finiteVerdierScalarRepresentative J χ P =
    (ProEtale.pbcFixedScalarExtension J ψ).map (finiteVerdierScalarRepresentative J φ P) ≫
      finiteVerdierScalarRepresentative J ψ
        (((finiteVerdierOrdinaryExtension J φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
      _root_.DerivedCategory.Q.map
        ((Functor.mapHomologicalComplexCompIso (ordinaryComp φ ψ χ hχ J) (.up ℤ)).hom.app P) := by
  let a := finiteVerdierOrdinaryAdjunction J φ
  let b := finiteVerdierOrdinaryAdjunction J ψ
  let c := finiteVerdierOrdinaryAdjunction J χ
  let R := Sheaf.restrictScalars J φ
  let S := Sheaf.restrictScalars J ψ
  let W := Sheaf.restrictScalars J χ
  let ad := Adjunction.ofIsRightAdjoint R.mapDerivedCategory
  let bd := Adjunction.ofIsRightAdjoint S.mapDerivedCategory
  let cd := Adjunction.ofIsRightAdjoint W.mapDerivedCategory
  let ac := a.mapHomologicalComplex (.up ℤ)
  let bc := b.mapHomologicalComplex (.up ℤ)
  let cc := c.mapHomologicalComplex (.up ℤ)
  let rA := AlgebraicGeometry.Etale.ExceptionalCoefficients.adjointRepresentative
      _root_.DerivedCategory.Q _root_.DerivedCategory.Q
    _ _ _ _ ad ac R.mapDerivedCategoryFactors.symm
  let rB := AlgebraicGeometry.Etale.ExceptionalCoefficients.adjointRepresentative
      _root_.DerivedCategory.Q _root_.DerivedCategory.Q
    _ _ _ _ bd bc S.mapDerivedCategoryFactors.symm
  let rC := AlgebraicGeometry.Etale.ExceptionalCoefficients.adjointRepresentative
      _root_.DerivedCategory.Q _root_.DerivedCategory.Q
    _ _ _ _ cd cc W.mapDerivedCategoryFactors.symm
  have hrA (K) : rA.app K = finiteVerdierScalarRepresentative J φ K := by
    unfold finiteVerdierScalarRepresentative finiteVerdierScalarRepresentativeAux
    rw [← Etale.mapComplex_unit_formula]
    rfl
  have hrB (K) : rB.app K = finiteVerdierScalarRepresentative J ψ K := by
    unfold finiteVerdierScalarRepresentative finiteVerdierScalarRepresentativeAux
    rw [← Etale.mapComplex_unit_formula]
    rfl
  have hrC (K) : rC.app K = finiteVerdierScalarRepresentative J χ K := by
    unfold finiteVerdierScalarRepresentative finiteVerdierScalarRepresentativeAux
    rw [← Etale.mapComplex_unit_formula]
    rfl
  let η := Sheaf.restrictScalarsCompIso J φ ψ χ hχ
  let ηc := Functor.mapHomologicalComplexCompIso η (.up ℤ)
  let νc := Functor.mapHomologicalComplexCompIso (ordinaryComp φ ψ χ hχ J) (.up ℤ)
  have hn : ∀ K, (ac.comp bc).homEquiv _ _ (νc.hom.app K) ≫
      ηc.hom.app _ = cc.unit.app K := by
    intro K
    apply HomologicalComplex.hom_ext
    intro i
    have h := CompositionProof.left_comp_unit a b c η (K.X i)
    rw [Adjunction.homEquiv_unit] at h ⊢
    exact h
  have h :
      (Adjunction.leftAdjointCompIso ad bd cd
        (Sheaf.derivedRestrictScalarsCompIso J hχ)).hom.app
          (_root_.DerivedCategory.Q.obj P) ≫ rC.app P =
        (ProEtale.pbcFixedScalarExtension J ψ).map (rA.app P) ≫
          rB.app (((finiteVerdierOrdinaryExtension J φ).mapHomologicalComplex (.up ℤ)).obj P) ≫
          _root_.DerivedCategory.Q.map (νc.hom.app P) :=
    CompositionProof.representative_composition
        _root_.DerivedCategory.Q _root_.DerivedCategory.Q
      _root_.DerivedCategory.Q ac bc cc ad bd cd
      R.mapDerivedCategoryFactors.symm S.mapDerivedCategoryFactors.symm
      W.mapDerivedCategoryFactors.symm ηc
      (Sheaf.derivedRestrictScalarsCompIso J hχ) νc.hom hn
      (by
        intro K
        have hv : ηc.hom.app K = (NatIso.mapHomologicalComplex η (.up ℤ)).hom.app K := by
          ext i
          rfl
        rw [hv]
        dsimp only [Sheaf.derivedRestrictScalarsCompIso, Iso.symm_hom]
        exact Functor.exactDerivedRestrictionComposition_inv_factors S R W η K) P
  simpa only [hrA, hrB, hrC, ad, bd, cd, νc, ordinaryComp,
    ProEtale.pbcFixedScalarExtensionComp,
    ProEtale.pbcFixedScalarExtension, Sheaf.derivedRestrictScalars, Category.assoc] using h

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
private theorem extension_preservesKFlatQuasiIso {R S : Type (u + 1)}
    [CommRing R] [CommRing S] (φ : R →+* S) (J : GrothendieckTopology V) :
    (finiteVerdierOrdinaryExtension J φ).PreservesKFlatQuasiIso := by
  classical
  let E : Sheaf J (ModuleCat.{u + 1} R) ⥤ Sheaf J
    (ModuleCat.{u + 1} S) :=
    Sheaf.composeAndSheafify J (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  let U := Sheaf.restrictScalars J φ
  let adj : E ⊣ U :=
    Sheaf.adjunction J (ModuleCat.extendRestrictScalarsAdj.{u + 1, u + 1, u +
      1} φ)
  have : E.Additive := adj.left_adjoint_additive
  let B := (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ).obj (ModuleCat.of S S)
  let coeff := (Functor.const Vᵒᵖ).obj B
  let a := presheafToSheaf J (ModuleCat.{u + 1} R)
  let a' := presheafToSheaf J (ModuleCat.{u + 1} S)
  let F := sheafToPresheaf J (ModuleCat.{u + 1} R)
  let W := (Functor.whiskeringRight Vᵒᵖ _ _).obj
    (ModuleCat.extendScalars.{u + 1, u + 1, u + 1} φ)
  have : J.PreservesSheafification (ModuleCat.restrictScalars.{u + 1, u + 1, u
    + 1} φ) :=
    Sheaf.preservesSheafification_of_adjunction J
      (ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ)
  let e : E ⋙ U ≅ MonoidalCategory.tensorRight (a.obj coeff) :=
    Functor.associator F (W ⋙ a') U ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W a' U) ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerLeft W
        (sheafComposeNatIso J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} φ)
          (sheafificationAdjunction J (ModuleCat.{u + 1} S))
          (sheafificationAdjunction J (ModuleCat.{u + 1} R))).symm) ≪≫
      Functor.isoWhiskerLeft F (Functor.associator W _ a).symm ≪≫
      Functor.isoWhiskerLeft F (Functor.isoWhiskerRight
        (Functor.whiskeringRightObjCompIso _ _ ≪≫
          (Functor.whiskeringRight _ _ _).mapIso
            (ModuleCat.extendScalarsCompRestrictScalarsIso.{u + 1} φ) ≪≫
          whiskeringRightTensorRightIso _) a) ≪≫
      Functor.isoWhiskerLeft F (Sheaf.presheafToSheafCompTensorRightIso coeff).symm ≪≫
      (Functor.associator F a (MonoidalCategory.tensorRight (a.obj coeff))).symm ≪≫
      Functor.isoWhiskerRight
        (asIso (sheafificationAdjunction J (ModuleCat.{u + 1} R)).counit)
        (MonoidalCategory.tensorRight (a.obj coeff)) ≪≫ Functor.leftUnitor _
  have hU : U.Faithful := inferInstance
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf J (ModuleCat.{u + 1} R)) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{0, 0} (Sheaf J (ModuleCat.{u + 1} R)) :=
    hasColimitsOfSizeShrink.{0, 0, u + 1, u + 1} _
  have : HasCountableCoproducts (Sheaf J (ModuleCat.{u + 1} R)) :=
    ⟨fun K _ ↦ HasColimitsOfSize.has_colimits_of_shape (Discrete K)⟩
  have hE : E.PreservesKFlatQuasiIso := by
    apply CategoryTheory.Functor.PreservesKFlatQuasiIso.mk'
    intro K hK hKa
    have ht := CochainComplex.acyclic_tensorRight_of_kFlat K hK hKa (a.obj coeff)
    have hEU := ht.of_iso
      ((NatIso.mapHomologicalComplex e (.up ℤ)).app K).symm
    have hUK : ((U.mapHomologicalComplex (.up ℤ)).obj
        ((E.mapHomologicalComplex (.up ℤ)).obj K)).Acyclic :=
      hEU.of_iso ((CategoryTheory.Functor.mapHomologicalComplexCompIso
        (Iso.refl (E ⋙ U)) (.up ℤ)).app K)
    intro n
    exact (ShortComplex.exact_map_iff_of_faithful _ U).1 (hUK n)
  exact hE

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
private def representative
    (J : GrothendieckTopology V) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) :
    _root_.DerivedCategory.Q ⋙ ProEtale.pbcFixedScalarExtension J φ ⟶
      (finiteVerdierOrdinaryExtension J φ).mapHomologicalComplex (.up ℤ) ⋙
        _root_.DerivedCategory.Q :=
  Etale.cochainAdjointComparison (finiteVerdierOrdinaryExtension J φ)
    (Sheaf.restrictScalars J φ) (finiteVerdierOrdinaryAdjunction J φ)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J φ))

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
private theorem representative_app
    (J : GrothendieckTopology V) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ) :
    (representative J φ).app P = finiteVerdierScalarRepresentative J φ P := rfl

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
private theorem representative_iso
    (J : GrothendieckTopology V) {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (P : CochainComplex (Sheaf J (ModuleCat.{u + 1} A)) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    IsIso ((representative J φ).app P) := by
  let : (finiteVerdierOrdinaryExtension J φ).PreservesKFlatQuasiIso :=
    extension_preservesKFlatQuasiIso φ J
  exact Etale.cochainAdjointComparison_isIso _ _ (finiteVerdierOrdinaryAdjunction J φ)
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars J φ)) P hP

attribute [-instance] CategoryTheory.catToReflQuiver in
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints in
/-- Normalized scalar tensorators compose through the fixed derived scalar compositor.
Source: blueprint latest, lem-coef-finite-free-extension.proof.md, paragraph 3.
(blueprint: lem-sf-normalized-site-scalar-tensor-composition).

Proof: restriction composition is monoidal, as can be checked on the unit and on pure
module tensors. Its left adjoint compositor is therefore monoidal. Transpose the
ordinary units to compare the localized cochain scalar representatives; uniqueness of
adjoints gives their compatibility with the fixed derived compositor. Ordinary scalar
extension preserves acyclic K-flat complexes, since after faithful exact restriction
it is tensoring with the constant target ring. Hence the scalar representative is
invertible on K-flat complexes. Paste the three given tensor normalization equations
with the ordinary monoidal compositor and the representative-composition equation.
Cancel on K-flat tensor products, then use naturality along flat K-flat resolutions
in both variables to obtain the equation on all derived objects. -/
theorem scalar_tensor_comp
    {V : Type (u + 1)} [Category.{u} V] [EssentiallySmall.{u + 1} V]
    (J : GrothendieckTopology V)
    {A B C : Type (u + 1)} [CommRing A] [CommRing B] [CommRing C]
    (φ : A →+* B) (ψ : B →+* C) (χ : A →+* C) (hχ : χ = ψ.comp φ)
    (δφ : Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory
      (Sheaf J (ModuleCat.{u + 1} A)))) ⋙ ProEtale.pbcFixedScalarExtension J φ ≅
      (ProEtale.pbcFixedScalarExtension J φ).prod (ProEtale.pbcFixedScalarExtension J φ) ⋙
        Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory
          (Sheaf J (ModuleCat.{u + 1} B)))))
    (δψ : Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory
      (Sheaf J (ModuleCat.{u + 1} B)))) ⋙ ProEtale.pbcFixedScalarExtension J ψ ≅
      (ProEtale.pbcFixedScalarExtension J ψ).prod (ProEtale.pbcFixedScalarExtension J ψ) ⋙
        Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory
          (Sheaf J (ModuleCat.{u + 1} C)))))
    (δχ : Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory
      (Sheaf J (ModuleCat.{u + 1} A)))) ⋙ ProEtale.pbcFixedScalarExtension J χ ≅
      (ProEtale.pbcFixedScalarExtension J χ).prod (ProEtale.pbcFixedScalarExtension J χ) ⋙
        Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory
          (Sheaf J (ModuleCat.{u + 1} C)))))
    (hφ : letI := (finiteVerdierOrdinaryAdjunction J φ).isLeftAdjoint
      TensorNormalizationAux (finiteVerdierOrdinaryExtension J φ)
        (ProEtale.pbcFixedScalarExtension J φ) (finiteVerdierScalarRepresentative J φ) δφ)
    (hψ : letI := (finiteVerdierOrdinaryAdjunction J ψ).isLeftAdjoint
      TensorNormalizationAux (finiteVerdierOrdinaryExtension J ψ)
        (ProEtale.pbcFixedScalarExtension J ψ) (finiteVerdierScalarRepresentative J ψ) δψ)
    (hχ' : letI := (finiteVerdierOrdinaryAdjunction J χ).isLeftAdjoint
      TensorNormalizationAux (finiteVerdierOrdinaryExtension J χ)
        (ProEtale.pbcFixedScalarExtension J χ) (finiteVerdierScalarRepresentative J χ) δχ)
    (K M : _root_.DerivedCategory (Sheaf J (ModuleCat.{u + 1} A))) :
    (ProEtale.pbcFixedScalarExtensionComp J φ ψ χ hχ).hom.app (K ⊗ M) ≫
        δχ.hom.app (K, M) =
      (ProEtale.pbcFixedScalarExtension J ψ).map (δφ.hom.app (K, M)) ≫
        δψ.hom.app ((ProEtale.pbcFixedScalarExtension J φ).obj K,
          (ProEtale.pbcFixedScalarExtension J φ).obj M) ≫
        (Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory
          (Sheaf J (ModuleCat.{u + 1} C))))).map
          (Prod.mkHom ((ProEtale.pbcFixedScalarExtensionComp J φ ψ χ hχ).hom.app K)
            ((ProEtale.pbcFixedScalarExtensionComp J φ ψ χ hχ).hom.app M)) := by
  let LF := ProEtale.pbcFixedScalarExtension J φ
  let LG := ProEtale.pbcFixedScalarExtension J ψ
  let LH := ProEtale.pbcFixedScalarExtension J χ
  let TA := Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory
    (Sheaf J (ModuleCat.{u + 1} A))))
  let TC := Functor.uncurry.obj (curriedTensor (_root_.DerivedCategory
    (Sheaf J (ModuleCat.{u + 1} C))))
  let a := ProEtale.pbcFixedScalarExtensionComp J φ ψ χ hχ
  let α : TA ⋙ LF ⋙ LG ⟶ LH.prod LH ⋙ TC :=
    Functor.whiskerLeft TA a.hom ≫ δχ.hom
  let β : TA ⋙ LF ⋙ LG ⟶ LH.prod LH ⋙ TC :=
    Functor.whiskerRight δφ.hom LG ≫
      Functor.whiskerLeft (LF.prod LF) δψ.hom ≫
      Functor.whiskerRight (NatTrans.prod a.hom a.hom) TC
  have hab : α = β := by
    apply Etale.natTrans_ext_flat α β
    intro P Q hP hQ _ _
    have := ordinaryComp_monoidal φ ψ χ hχ J
    have h := CompositionProof.normalized_cochain_composition
      (finiteVerdierOrdinaryExtension J φ) (finiteVerdierOrdinaryExtension J ψ)
      (finiteVerdierOrdinaryExtension J χ) LF LG LH
      (representative J φ) (representative J ψ) (representative J χ)
      (finiteVerdierScalarRepresentative J φ) (finiteVerdierScalarRepresentative J ψ)
      (finiteVerdierScalarRepresentative J χ)
      (representative_app J φ) (representative_app J ψ) (representative_app J χ)
      δφ δψ δχ hφ hψ hχ' a (ordinaryComp φ ψ χ hχ J)
      (scalar_comp_rep φ ψ χ hχ J) (representative_iso J χ) P Q hP hQ
    simpa only [α, β, LF, LG, LH, TA, TC, a, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, NatTrans.comp_app, Functor.comp_obj,
      Functor.prod_obj, curriedTensor_obj_obj, curriedTensor_map_app,
      curriedTensor_obj_map, Functor.uncurry_obj_obj, Functor.uncurry_obj_map,
      NatTrans.prod, MonoidalCategory.tensorHom_def, Category.assoc] using h
  exact congrArg (fun t ↦ t.app (K, M)) hab

end WeilConjectures.NormalizedSiteScalarTensor
