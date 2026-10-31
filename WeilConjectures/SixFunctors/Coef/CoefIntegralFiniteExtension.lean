/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionCore
import WeilConjectures.SixFunctors.IntegralVerdier.IntegralVerdierSignedCalculus
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionReductionPairing
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionTriangulatedPrecomp
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionFiniteUIsInvertible
import WeilConjectures.SixFunctors.Sf.SfIntegralReductionConservative
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionIdentityE
import all WeilConjectures.SixFunctors.IntegralFiniteExtension.IntegralScalarQuotientComposition
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionTranspose
import WeilConjectures.SmoothPurity.Integral.Scalar.IntegralScalarExtensionConstructibleIntrinsic
import WeilConjectures.SixFunctors.IntegralFiniteExtension.CoefIntegralFiniteExtensionHomMapInvertibility

/-! # Integral duality under finite coefficient extension

Source: current blueprint, sec-smooth-purity/sk-lem-sp-tower, order 2494
(blueprint: lem-coef-integral-finite-extension).

The defining comparisons are publicly re-exported from the models module.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [local irreducible] CategoryTheory.derivedInternalHomOfUniverses
  CategoryTheory.homComplexFunctor
  CategoryTheory.sheafCompose CategoryTheory.presheafToSheaf
  CategoryTheory.Functor.leftAdjoint SheafOfModules.changeOfRings
  WeilConjectures.IntegralHom.totalTensor WeilConjectures.IntegralHom.homModelMap
  WeilConjectures.IntegralHom.projection WeilConjectures.IntegralHom.evaluate

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralFiniteExtension

namespace DirectScalarCoherence

attribute [local irreducible] Padic completedCoefficientMap
  completedIntegralCommRingSheafUnrestricted completedIntegralCoefficientSheafUnrestricted
  comp unit completion integralScalarExtensionOfUniverses
  PurCompactSupport.tensorComposition PurCompactSupport.tensorIdentity
  completedScalarComparison completedScalarChangeData
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors

attribute [local irreducible] HasDerivedCategory.standard reductionDerivedChange
  pbcDerivedScalarAdjunction
attribute [local instance 5000] proEtaleRingModules_hasDerivedCategory


private theorem derived_left_unit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (V : B ⥤ A) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (U : A ⥤ A) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (ρ : U ≅ 𝟭 A) :
    (Functor.mapDerivedCategoryCompIso V U).symm ≪≫
        Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerLeft V ρ) =
      Functor.isoWhiskerLeft V.mapDerivedCategory
          (Functor.mapDerivedCategoryNatIso ρ ≪≫ Functor.mapDerivedCategoryIdIso A) ≪≫
        Functor.rightUnitor V.mapDerivedCategory := by
  apply Iso.ext
  ext X
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerLeft V ρ) X
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_comp_id V) X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at hn hu
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso V U).hom.app X)).mp
  rw [Iso.hom_inv_id_app_assoc]
  simp only [← Category.assoc]
  rw [← hn]
  simp only [Category.assoc]
  simp only [NatTrans.id_app] at hu
  rw [reassoc_of% hu]
  erw [Category.comp_id, Category.comp_id]

private theorem derived_right_unit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B]
    (U : B ⥤ B) [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (V : B ⥤ A) [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (ρ : U ≅ 𝟭 B) :
    (Functor.mapDerivedCategoryCompIso U V).symm ≪≫
        Functor.mapDerivedCategoryNatIso (Functor.isoWhiskerRight ρ V) =
      Functor.isoWhiskerRight
          (Functor.mapDerivedCategoryNatIso ρ ≪≫ Functor.mapDerivedCategoryIdIso B)
          V.mapDerivedCategory ≪≫ Functor.leftUnitor V.mapDerivedCategory := by
  apply Iso.ext
  ext X
  have hn := congr_app (Functor.mapDerivedCategoryNatIso_isoWhiskerRight ρ V) X
  have hu := congr_app (Functor.mapDerivedCategoryCompIso_id_comp V) X
  simp only [NatTrans.comp_app, Functor.whiskerRight_app] at hn hu
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  apply (cancel_epi ((Functor.mapDerivedCategoryCompIso U V).hom.app X)).mp
  rw [Iso.hom_inv_id_app_assoc]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hn]
  simp only [NatTrans.id_app] at hu
  rw [reassoc_of% hu]
  erw [Category.comp_id, Category.comp_id]

private theorem comparison_unit
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    {U : B ⥤ A} {V : C ⥤ B} {W : C ⥤ A}
    (a : F ⊣ U) (b : G ⊣ V) (c : H ⊣ W) (d : V ⋙ U ≅ W) (M : A) :
    (a.comp b).homEquiv M _ ((a.leftAdjointCompIso b c d).hom.app M) ≫
      d.hom.app (H.obj M) = c.unit.app M := by
  rw [Adjunction.homEquiv_unit, Category.assoc, d.hom.naturality, ← Category.assoc]
  have hu := unit_conjugateEquiv (a.comp b) c (a.leftAdjointCompIso b c d).inv M
  rw [Adjunction.conjugateEquiv_leftAdjointCompIso_inv] at hu
  rw [hu, Category.assoc, ← W.map_comp, Iso.inv_hom_id_app, W.map_id]
  exact Category.comp_id _

private theorem normalizedComparison_eq
    {A B C : Type*} [Category A] [Category B] [Category C]
    {F : A ⥤ B} {G : B ⥤ C} {H : A ⥤ C}
    {U : B ⥤ A} {V : C ⥤ B} {W : C ⥤ A}
    (a : F ⊣ U) (b : G ⊣ V) (c : H ⊣ W) (d : V ⋙ U ≅ W) :
    ((a.comp b).ofNatIsoRight d).leftAdjointUniq c =
      a.leftAdjointCompIso b c d := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply (((a.comp b).ofNatIsoRight d).homEquiv M _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_ofNatIsoRight_apply]
  exact (comparison_unit a b c d M).symm

-- Transfer the restriction-unit constraints through uniqueness of left adjoints.

private theorem identityConjugate {A : Type*} [Category A]
    {F U : A ⥤ A} (a : F ⊣ U) (e : U ≅ 𝟭 A) :
    a.leftAdjointIdIso e = ((conjugateIsoEquiv a Adjunction.id).symm e).symm := by
  rfl

private theorem tensorComposition_unit_left {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (r : R ⟶ S) :
    PurCompactSupport.tensorComposition (𝟙 R) r r (Category.id_comp _) =
      Functor.isoWhiskerRight (PurCompactSupport.tensorIdentity R) (pbcDerivedExtend r) ≪≫
        Functor.leftUnitor (pbcDerivedExtend r) := by
  let ρ := (PurCompactSupport.restrictIdentity_existsUnique.{u} R).exists.choose
  let δ := Functor.mapDerivedCategoryNatIso ρ ≪≫ Functor.mapDerivedCategoryIdIso _
  have he : pbcRestrictComp (𝟙 R) r r (Category.id_comp _) =
      Functor.isoWhiskerLeft (pbcRestrict r) ρ := by
    apply Iso.ext
    ext M U x
    exact (pbcRestrictComp_exists (𝟙 R) r r
      (Category.id_comp _)).exists.choose_spec M U x |>.trans
        ((PurCompactSupport.restrictIdentity_existsUnique R).exists.choose_spec
          ((pbcRestrict r).obj M) U x).symm
  have hd : pbcDerivedRestrictComp (𝟙 R) r r (Category.id_comp _) =
      Functor.isoWhiskerLeft (pbcDerivedRestrict r) δ ≪≫
        Functor.rightUnitor (pbcDerivedRestrict r) := by
    unfold pbcDerivedRestrictComp
    rw [he]
    exact derived_left_unit (pbcRestrict r) (pbcRestrict (𝟙 R)) ρ
  unfold PurCompactSupport.tensorComposition
  rw [normalizedComparison_eq]
  have hu : (pbcDerivedScalarAdjunction (𝟙 R)).leftAdjointIdIso δ =
      PurCompactSupport.tensorIdentity R := by
    unfold PurCompactSupport.tensorIdentity
    exact identityConjugate _ _
  rw [← hu]
  exact Adjunction.leftAdjointCompIso_id_comp (pbcDerivedScalarAdjunction (𝟙 R))
    (pbcDerivedScalarAdjunction r) _ δ hd

private theorem tensorComposition_unit_right {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}} (r : R ⟶ S) :
    PurCompactSupport.tensorComposition r (𝟙 S) r (Category.comp_id _) =
      Functor.isoWhiskerLeft (pbcDerivedExtend r) (PurCompactSupport.tensorIdentity S) ≪≫
        Functor.rightUnitor (pbcDerivedExtend r) := by
  let ρ := (PurCompactSupport.restrictIdentity_existsUnique.{u} S).exists.choose
  let δ := Functor.mapDerivedCategoryNatIso ρ ≪≫ Functor.mapDerivedCategoryIdIso _
  have he : pbcRestrictComp r (𝟙 S) r (Category.comp_id _) =
      Functor.isoWhiskerRight ρ (pbcRestrict r) := by
    apply Iso.ext
    ext M U x
    exact (pbcRestrictComp_exists r (𝟙 S) r
      (Category.comp_id _)).exists.choose_spec M U x |>.trans
        ((PurCompactSupport.restrictIdentity_existsUnique S).exists.choose_spec M U x).symm
  have hd : pbcDerivedRestrictComp r (𝟙 S) r (Category.comp_id _) =
      Functor.isoWhiskerRight δ (pbcDerivedRestrict r) ≪≫
        Functor.leftUnitor (pbcDerivedRestrict r) := by
    unfold pbcDerivedRestrictComp
    rw [he]
    exact derived_right_unit (pbcRestrict (𝟙 S)) (pbcRestrict r) ρ
  unfold PurCompactSupport.tensorComposition
  rw [normalizedComparison_eq]
  have hu : (pbcDerivedScalarAdjunction (𝟙 S)).leftAdjointIdIso δ =
      PurCompactSupport.tensorIdentity S := by
    unfold PurCompactSupport.tensorIdentity
    exact identityConjugate _ _
  rw [← hu]
  exact Adjunction.leftAdjointCompIso_comp_id (pbcDerivedScalarAdjunction r)
    (pbcDerivedScalarAdjunction (𝟙 S)) _ δ hd


private theorem tensorComposition_source_unit {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ R) (ha : a = 𝟙 R) (b : R ⟶ S) (h : a ≫ b = b)
    (K : DerivedCategory.{u + 2} (pbcModules W R)) :
    (PurCompactSupport.tensorComposition a b b h).hom.app K =
      (pbcDerivedExtend b).map
        ((eqToIso (congrArg (fun x ↦ pbcDerivedExtend x) ha) ≪≫
          PurCompactSupport.tensorIdentity R).hom.app K) := by
  cases ha
  rw [tensorComposition_unit_left]
  simp

private theorem tensorComposition_target_unit {W : Scheme.{u}}
    {R S : Sheaf (ProEt.topology W) CommRingCat.{u + 1}}
    (a : R ⟶ S) (b : S ⟶ S) (hb : b = 𝟙 S) (h : a ≫ b = a)
    (K : DerivedCategory.{u + 2} (pbcModules W R)) :
    (PurCompactSupport.tensorComposition a b a h).hom.app K =
      ((eqToIso (congrArg (fun x ↦ pbcDerivedExtend x) hb) ≪≫
        PurCompactSupport.tensorIdentity S).hom.app ((pbcDerivedExtend a).obj K)) := by
  cases hb
  rw [tensorComposition_unit_right]
  simp

private theorem source_unit_transport
    {A B : Type*} [Category A] [Category B]
    (P T : A ⥤ B) (K K' : A) (e : P.obj K ≅ T.obj K)
    (e' : P.obj K' ≅ T.obj K') (f : K' ⟶ K)
    (h : P.map f ≫ e.hom = e'.hom ≫ T.map f) :
    e'.inv ≫ P.map f ≫ e.hom = T.map f := by
  rw [h, Iso.inv_hom_id_assoc]

private theorem associator_transport
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    (P : A ⥤ B) (Q : B ⥤ C) (R : C ⥤ D)
    (J : A ⥤ C) (H : B ⥤ D) (W : A ⥤ D) (V : C ⥤ D)
    (α : P ⋙ Q ≅ J) (β : Q ⋙ R ≅ H)
    (γ : J ⋙ R ≅ W) (δ : P ⋙ H ≅ W) (K : A)
    (ha : R.map (α.hom.app K) ≫ γ.hom.app K =
      β.hom.app (P.obj K) ≫ δ.hom.app K)
    {TK : B} {UTK JK : C} {HTK WK : D}
    (cP : P.obj K ≅ TK) (cQ : Q.obj TK ≅ UTK)
    (cJ : J.obj K ≅ JK) (cR : R.obj UTK ≅ V.obj UTK)
    (cRJ : R.obj JK ≅ V.obj JK) (cH : H.obj TK ≅ HTK) (cW : W.obj K ≅ WK)
    (f : UTK ⟶ JK)
    (hf : f = cQ.inv ≫ Q.map cP.inv ≫ α.hom.app K ≫ cJ.hom)
    (hn : R.map f ≫ cRJ.hom = cR.hom ≫ V.map f) :
    V.map f ≫ (cRJ.inv ≫ R.map cJ.inv ≫ γ.hom.app K ≫ cW.hom) =
      (cR.inv ≫ R.map cQ.inv ≫ β.hom.app TK ≫ cH.hom) ≫
        (cH.inv ≫ H.map cP.inv ≫ δ.hom.app K ≫ cW.hom) := by
  have hn' : V.map f ≫ cRJ.inv = cR.inv ≫ R.map f := by
    apply (cancel_mono cRJ.hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hn, Iso.inv_hom_id_assoc]
  rw [← Category.assoc (V.map f), hn', hf]
  simp only [Functor.map_comp, Category.assoc]
  rw [← R.map_comp_assoc cJ.hom cJ.inv, Iso.hom_inv_id, R.map_id,
    Category.id_comp]
  rw [reassoc_of% ha]
  have hb := β.hom.naturality cP.inv
  dsimp only [Functor.comp_map] at hb
  rw [reassoc_of% hb]
  simp only [Iso.hom_inv_id_assoc]

attribute [local instance 6000] integralTowerHasDerivedCategory

private theorem comp_factor
    (l : ℕ) [Fact l.Prime]
    (E L F : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] F) (X : Scheme.{u})
    (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K) :
    (comp l E L i X F j K hK).hom =
      (completion l L F j X _ (extension_complete l E L i X K hK)).inv ≫
        (pbcDerivedExtend (completedCoefficientMap l L F j X)).map
          (completion l E L i X K hK).inv ≫
        (PurCompactSupport.tensorComposition (completedCoefficientMap l E L i X)
          (completedCoefficientMap l L F j X) (completedCoefficientMap l E F (j.comp i) X)
          (PurCompactSupport.completedMap_composition l E L i F j X)).hom.app K ≫
        (completion l E F (j.comp i) X K hK).hom := by
  unfold comp
  rfl


private theorem unit_factor
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (K : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) :
    (unit l E X K hK).hom =
      (completion l E E (AlgHom.id (Padic l) E) X K hK).inv ≫
        (eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
          (PurCompactSupport.completedMap_identity l E X)) ≪≫
            PurCompactSupport.tensorIdentity
              (completedIntegralCommRingSheafUnrestricted l E X)).hom.app K := by
  unfold unit
  have h := NatIso.trans_app
    (eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ)
      (PurCompactSupport.completedMap_identity l E X)))
    (PurCompactSupport.tensorIdentity (completedIntegralCommRingSheafUnrestricted l E X)) K
  exact (congrArg (fun e ↦
    (completion l E E (AlgHom.id (Padic l) E) X K hK).inv ≫ e.hom) h).symm


private theorem completion_naturality
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L) (X : Scheme.{u})
    (K M : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) (hM : IsSfDerivedComplete l E X M) (f : K ⟶ M) :
    (pbcDerivedExtend (completedCoefficientMap l E L i X)).map f ≫
        (completion l E L i X M hM).hom =
      (completion l E L i X K hK).hom ≫
        (integralScalarExtensionOfUniverses l E L i X).map f := by
  unfold completion
  with_unfolding_all
    exact (completedScalarComparison l E L i X).naturality f

private theorem source_unit
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L) (X : Scheme.{u})
    (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K) :
    (comp l E E (AlgHom.id (Padic l) E) X L i K hK).hom =
      (integralScalarExtensionOfUniverses l E L i X).map (unit l E X K hK).hom := by
  let e := eqToIso (congrArg (fun x ↦ pbcDerivedExtend x)
    (PurCompactSupport.completedMap_identity l E X)) ≪≫
      PurCompactSupport.tensorIdentity (completedIntegralCommRingSheafUnrestricted l E X)
  have h := tensorComposition_source_unit _
    (PurCompactSupport.completedMap_identity l E X)
    (completedCoefficientMap l E L i X)
    (PurCompactSupport.completedMap_composition l E E (AlgHom.id (Padic l) E) L i X) K
  rw [comp_factor]
  dsimp only [AlgHom.comp_id] at h ⊢
  rw [h]
  have he : (unit l E X K hK).hom =
      (completion l E E (AlgHom.id (Padic l) E) X K hK).inv ≫ e.hom.app K := by
    exact unit_factor l E X K hK
  rw [he]
  simp only [← Functor.map_comp_assoc]
  exact source_unit_transport _ _ _ _ _ _ _
    (completion_naturality l E L i X _ K
      (extension_complete l E E (AlgHom.id (Padic l) E) X K hK) hK _)

private theorem target_unit
    (l : ℕ) [Fact l.Prime]
    (E L : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (i : E →ₐ[Padic l] L) (X : Scheme.{u})
    (K : IntegralVerdier.Ambient l E X) (hK : IsSfDerivedComplete l E X K) :
    (comp l E L i X L (AlgHom.id (Padic l) L) K hK).hom =
      (unit l L X ((integralScalarExtensionOfUniverses l E L i X).obj K)
        (extension_complete l E L i X K hK)).hom := by
  let e := eqToIso (congrArg (fun x ↦ pbcDerivedExtend x)
    (PurCompactSupport.completedMap_identity l L X)) ≪≫
      PurCompactSupport.tensorIdentity (completedIntegralCommRingSheafUnrestricted l L X)
  have h := tensorComposition_target_unit (completedCoefficientMap l E L i X) _
    (PurCompactSupport.completedMap_identity l L X)
    (PurCompactSupport.completedMap_composition l E L i L (AlgHom.id (Padic l) L) X) K
  rw [comp_factor, unit_factor]
  dsimp only [AlgHom.id_comp] at h ⊢
  rw [h]
  have hn := e.hom.naturality (completion l E L i X K hK).inv
  dsimp only [Functor.comp_map, Functor.id_map] at hn
  rw [reassoc_of% hn]
  simp only [Iso.inv_hom_id, Category.comp_id]
  simp only [e, Iso.trans_hom, NatTrans.comp_app]

private theorem associativity
    (l : ℕ) [Fact l.Prime]
    (E L F G : Type u)
    [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
    [Field G] [Algebra (Padic l) G] [FiniteDimensional (Padic l) G]
    (i : E →ₐ[Padic l] L) (j : L →ₐ[Padic l] F) (k : F →ₐ[Padic l] G)
    (X : Scheme.{u}) (K : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) :
    (integralScalarExtensionOfUniverses l F G k X).map
        (comp l E L i X F j K hK).hom ≫
        (comp l E F (j.comp i) X G k K hK).hom =
      (comp l L F j X G k ((integralScalarExtensionOfUniverses l E L i X).obj K)
        (extension_complete l E L i X K hK)).hom ≫
        (comp l E L i X G (k.comp j) K hK).hom := by
  let ai := completedCoefficientMap l E L i X
  let aj := completedCoefficientMap l L F j X
  let ak := completedCoefficientMap l F G k X
  let aij := completedCoefficientMap l E F (j.comp i) X
  let ajk := completedCoefficientMap l L G (k.comp j) X
  let aijk := completedCoefficientMap l E G (k.comp (j.comp i)) X
  let α := PurCompactSupport.tensorComposition ai aj aij
    (PurCompactSupport.completedMap_composition l E L i F j X)
  let β := PurCompactSupport.tensorComposition aj ak ajk
    (PurCompactSupport.completedMap_composition l L F j G k X)
  let γ := PurCompactSupport.tensorComposition aij ak aijk
    (PurCompactSupport.completedMap_composition l E F (j.comp i) G k X)
  let δ := PurCompactSupport.tensorComposition ai ajk aijk
    (PurCompactSupport.completedMap_composition l E L i G (k.comp j) X)
  have h := associator_transport
    (pbcDerivedExtend ai) (pbcDerivedExtend aj) (pbcDerivedExtend ak)
    (pbcDerivedExtend aij) (pbcDerivedExtend ajk) (pbcDerivedExtend aijk)
    (integralScalarExtensionOfUniverses l F G k X) α β γ δ K
    (tensorComposition_assoc ai aj ak aij ajk aijk _ _ _ _ K)
    (completion l E L i X K hK)
    (completion l L F j X _ (extension_complete l E L i X K hK))
    (completion l E F (j.comp i) X K hK)
    (completion l F G k X _
      (extension_complete l L F j X _ (extension_complete l E L i X K hK)))
    (completion l F G k X _ (extension_complete l E F (j.comp i) X K hK))
    (completion l L G (k.comp j) X _ (extension_complete l E L i X K hK))
    (completion l E G (k.comp (j.comp i)) X K hK)
    (comp l E L i X F j K hK).hom (comp_factor l E L F i j X K hK)
    (completion_naturality l F G k X _ _
      (extension_complete l L F j X _ (extension_complete l E L i X K hK))
      (extension_complete l E F (j.comp i) X K hK) _)
  simpa only [comp_factor, ai, aj, ak, aij, ajk, aijk, β, γ, δ,
    AlgHom.comp_assoc] using h

end DirectScalarCoherence

private theorem evaluation_transport
    {C : Type*} [Category C] (T : C × C ⥤ C) (H : Cᵒᵖ × C ⥤ C)
    (adj : ∀ K : C, (Functor.curry.obj T).obj K ⊣ (Functor.curry.obj H).obj (op K))
    (hn : ∀ (K K' M : C) (f : K' ⟶ K),
      T.map (Prod.mkHom (𝟙 K') (H.map (Prod.mkHom f.op (𝟙 M)))) ≫
          (adj K').counit.app M =
        T.map (Prod.mkHom f (𝟙 _)) ≫ (adj K).counit.app M)
    (K K' M M' : C) (f : K' ⟶ K) (g : M ⟶ M') :
    T.map (Prod.mkHom (𝟙 K') (H.map (Prod.mkHom f.op g))) ≫
        (adj K').counit.app M' =
      T.map (Prod.mkHom f (𝟙 (H.obj (op K, M)))) ≫
        (adj K).counit.app M ≫ g := by
  have hh : H.map (Prod.mkHom f.op g) =
      H.map (Prod.mkHom (𝟙 (op K)) g) ≫ H.map (Prod.mkHom f.op (𝟙 M')) := by
    rw [← H.map_comp]
    simp only [prod_comp, Category.id_comp, Category.comp_id]
  rw [hh]
  have ht : T.map (Prod.mkHom (𝟙 K')
      (H.map (Prod.mkHom (𝟙 (op K)) g) ≫ H.map (Prod.mkHom f.op (𝟙 M')))) =
      T.map (Prod.mkHom (𝟙 K') (H.map (Prod.mkHom (𝟙 (op K)) g))) ≫
        T.map (Prod.mkHom (𝟙 K') (H.map (Prod.mkHom f.op (𝟙 M')))) := by
    rw [← T.map_comp]
    simp only [prod_comp, Category.id_comp]
  rw [ht, Category.assoc, hn]
  have ht' : T.map (Prod.mkHom (𝟙 K') (H.map (Prod.mkHom (𝟙 (op K)) g))) ≫
      T.map (Prod.mkHom f (𝟙 _)) =
      T.map (Prod.mkHom f (𝟙 _)) ≫
        T.map (Prod.mkHom (𝟙 K) (H.map (Prod.mkHom (𝟙 (op K)) g))) := by
    simp only [← T.map_comp, prod_comp, Category.id_comp, Category.comp_id]
  erw [← Category.assoc, ht', Category.assoc]
  congr 1
  exact (adj K).counit.naturality g

private theorem v_evaluation
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (a : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l E X))
    (b : IntegralHom.TensorPresentation.{u, u} X
      (completedIntegralCommRingSheafUnrestricted l L X))
    (hn : ∀ (K K' M : IntegralVerdier.Ambient l L X) (f : K' ⟶ K),
      b.tensor.map (Prod.mkHom (𝟙 K')
          ((IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l L X)).map
            (Prod.mkHom f.op (𝟙 M)))) ≫ (b.adjunction K').counit.app M =
        b.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (b.adjunction K).counit.app M)
    (K M : IntegralVerdier.Ambient l E X)
    (hK : IsSfDerivedComplete l E X K) (hM : IsSfDerivedComplete l E X M) :
    b.tensor.map (Prod.mkHom (𝟙 _) (v l E L ι X a b K M hK hM)) ≫
        (b.adjunction _).counit.app _ =
      extendedEvaluation l E L ι X a b K M hK hM := by
  let T := integralScalarExtensionOfUniverses l E L ι X
  let F := pbcDerivedExtend (completedCoefficientMap l E L ι X)
  let H := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)
  let cK := completion l E L ι X K hK
  let cM := completion l E L ι X M hM
  let cH := completion l E L ι X _ (scalarInternalHom_complete l E X K M hM)
  change b.tensor.map (Prod.mkHom (𝟙 _)
      (cH.inv ≫ homMap X (completedCoefficientMap l E L ι X) a b K M ≫
        H.map (Prod.mkHom cK.inv.op cM.hom))) ≫ _ = _
  have ht : b.tensor.map (Prod.mkHom (𝟙 (T.obj K))
      (cH.inv ≫ homMap X (completedCoefficientMap l E L ι X) a b K M ≫
        H.map (Prod.mkHom cK.inv.op cM.hom))) =
      b.tensor.map (Prod.mkHom (𝟙 (T.obj K)) cH.inv) ≫
        b.tensor.map (Prod.mkHom (𝟙 (T.obj K))
          (homMap X (completedCoefficientMap l E L ι X) a b K M)) ≫
        b.tensor.map (Prod.mkHom (𝟙 (T.obj K))
          (H.map (Prod.mkHom cK.inv.op cM.hom))) := by
    simp only [← Functor.map_comp, prod_comp, Category.id_comp]
  rw [ht, Category.assoc, Category.assoc,
    evaluation_transport b.tensor H b.adjunction hn _ _ _ _ cK.inv cM.hom]
  have ht' : b.tensor.map (Prod.mkHom (𝟙 (T.obj K)) cH.inv) ≫
      b.tensor.map (Prod.mkHom (𝟙 (T.obj K))
        (homMap X (completedCoefficientMap l E L ι X) a b K M)) ≫
      b.tensor.map (Prod.mkHom cK.inv (𝟙 _)) =
      b.tensor.map (Prod.mkHom cK.inv cH.inv) ≫
        b.tensor.map (Prod.mkHom (𝟙 (F.obj K))
          (homMap X (completedCoefficientMap l E L ι X) a b K M)) := by
    simp only [← Functor.map_comp, prod_comp, Category.id_comp, Category.comp_id]
    erw [Category.comp_id]
  have he := congrArg (fun f ↦ f ≫
    (b.adjunction (F.obj K)).counit.app (F.obj M) ≫ cM.hom) ht'
  simp only [Category.assoc] at he
  erw [he]
  have htrans : b.tensor.map (Prod.mkHom (𝟙 (F.obj K))
      (homMap X (completedCoefficientMap l E L ι X) a b K M)) ≫
      (b.adjunction (F.obj K)).counit.app (F.obj M) =
      (PurCompactSupport.scalarTensor (completedCoefficientMap l E L ι X)
        (tensorModel X a) (tensorModel X b)).inv.app
          (K, (IntegralHom.hom.{u, u} X
            (completedIntegralCommRingSheafUnrestricted l E X)).obj (op K, M)) ≫
        F.map ((a.adjunction K).counit.app M) := by
    exact ((b.adjunction (F.obj K)).homEquiv _ _).symm_apply_apply _
  have htrans' := congrArg
    (fun f ↦ b.tensor.map (Prod.mkHom cK.inv cH.inv) ≫ f ≫ cM.hom) htrans
  simpa only [Category.assoc, extendedEvaluation, cK, cH, cM, F] using htrans'

end WeilConjectures.IntegralFiniteExtension

namespace WeilConjectures
open IntegralFiniteExtension

/-- The canonical integral coefficient comparisons and all their normalization equations.
Source: current blueprint sec-smooth-purity/sk-lem-sp-tower, order 2494
(blueprint: lem-coef-integral-finite-extension).
Proof:
1. Finite freeness identifies strict completed extension with ordinary derived tensor
on complete inputs. Ordinary tensor and the Roos completion are triangulated. The
normalized finite quotient calculations preserve the uniform constructible bounds.
2. Construct the finite maps by transposing the compact-support counit comparisons.
Their identity and quotient composition equations give a coherent map on the full
S-tower, including levels between the ramification-multiple exponents. Take its
total limit and use the normalized counits. This gives the map u defined above,
not an arbitrary isomorphism; all its finite reductions are isomorphisms.
3. Finite freeness computes the evaluation transpose on a K-injective representative
as the finite-basis Hom identity. Completion gives precisely v. It is invertible
for constructible inputs. Composing with RHom(TK,u) gives beta and its invertibility.
4. Transpose the scalar-extended evaluation equation under the tensor-Hom adjunction.
The signed symmetry defines the actual delta; its transpose is evaluation, so the
same equation gives the displayed double-dual square. The coefficient tensor
associators identify these transposes after each finite reduction. Together with
the finite counit squares for u this gives all three quotient equations.
5. On local pure tensors, identity extension is multiplication and iterated extension
sends c tensor (b tensor x) to c*j(b) tensor x. These formulas give all three unit
and composition equations. Three successive extensions multiply coefficients in
the same order, proving the associator pentagon. The normalized completion maps
cancel in the intermediate positions. Localization and coherent total limit
preserve these equations. This includes identity fields, zero objects and empty X.
The further presentation c is assumed natural in the first tensor variable, as
the chosen a and b are; otherwise its adjunction is free off K-flat complexes. -/
theorem coef_integral_finite_extension
    (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (L : Type u) [Field L] [Algebra (Padic l) L] [FiniteDimensional (Padic l) L]
    (ι : E →ₐ[Padic l] L) (X : Scheme.{u})
    (D : FiniteFieldDatum.{u}) (hl : l ≠ D.p)
    [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))] [IsSeparated (X ↘ Spec (.of D.k))]
    (wE : DualizingDatum l X D hl E) (wL : DualizingDatum l X D hl L) :
    ∃ (a : IntegralHom.TensorPresentation.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l E X))
      (b : IntegralHom.TensorPresentation.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l L X))
      (sE : IntegralVerdier.SignedSymmetry X _ a)
      (sL : IntegralVerdier.SignedSymmetry X _ b)
      (mE : ∀ n : ℕ, IntegralHom.ReductionPresentation l E X D hl a n)
      (mL : ∀ n : ℕ, IntegralHom.ReductionPresentation l L X D hl b n),
      Conclusion l E L ι X D hl wE wL a b sE sL mE mL ∧
      IdentityConclusion l E X D hl wE a ∧ IdentityConclusion l L X D hl wL b ∧
      (∀ (F : Type u) [Field F] [Algebra (Padic l) F] [FiniteDimensional (Padic l) F]
        (j : L →ₐ[Padic l] F) (wF : DualizingDatum l X D hl F)
        (c : IntegralHom.TensorPresentation.{u, u} X
          (completedIntegralCommRingSheafUnrestricted l F X)),
        (∀ (K K' M : IntegralVerdier.Ambient l F X) (f : K' ⟶ K),
          c.tensor.map (Prod.mkHom (𝟙 K')
              ((IntegralHom.hom.{u, u} X
                (completedIntegralCommRingSheafUnrestricted l F X)).map
                (Prod.mkHom f.op (𝟙 M)))) ≫ (c.adjunction K').counit.app M =
            c.tensor.map (Prod.mkHom f (𝟙 _)) ≫ (c.adjunction K).counit.app M) →
        CompositionConclusion l E L ι X D hl wE wL a b F j wF c) := by
  obtain ⟨a, sE, mE, _, hnatE, hevalE, _, hfinE⟩ := IntegralVerdier.signedCalculus D l hl E X
  obtain ⟨b, sL, mL, _, hnatL, hn, _, hfinL⟩ := IntegralVerdier.signedCalculus D l hl L X
  obtain ⟨hdelta, hvred, hbred⟩ := reductionPairing l E L ι X D hl wE wL
    a b sE sL mE mL hnatE hnatL hevalE hn hfinE hfinL
  have htri : ∃ (_ : (integralScalarExtensionOfUniverses l E L ι X).CommShift ℤ),
      (integralScalarExtensionOfUniverses l E L ι X).IsTriangulated := by
    obtain ⟨c, h⟩ := comparison_precomp_triangulated l E L ι X
    let c' := c
    let h' := h
    exact ⟨c', Functor.isTriangulated_of_precomp (DerivedCategory.Qh (C := _))
      (integralScalarExtensionOfUniverses l E L ι X)⟩
  have hu : IsIso (u l E L ι X D hl wE wL) := by
    apply sfIntegralReduction_conservative l L X (u l E L ι X D hl wE wL)
      (sfIntegralScalarExtension_constructible D.p l hl E L ι X
        wE.omega.obj wE.omega.property) wL.omega.property
    intro n
    have hfiniteU : IsIso (finiteU l E L ι X D n) :=
      finiteU_isIso l E L ι X D hl n
    have hcomp : IsIso ((scalarReductionDerivedExtension l L X n).map
        (u l E L ι X D hl wE wL) ≫ (wL.reduction n).hom) := by
      rw [u_reduction l E L ι X D hl wE wL n]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (wL.reduction n).hom
  have hv (K M : sfIntegralConstructibleCategory l E X) :
      IsIso (v l E L ι X a b K.obj M.obj K.property.1 M.property.1) := by
    unfold v
    apply IsIso.comp_isIso'
    · infer_instance
    apply IsIso.comp_isIso'
    · exact homMap_isIso l E L ι X a b K.obj M.obj
    · let eK := completion l E L ι X K.obj K.property.1
      let eM := completion l E L ι X M.obj M.property.1
      have : IsIso eK.inv := eK.isIso_inv
      have : IsIso eM.hom := eM.isIso_hom
      have : IsIso (Prod.mkHom eK.inv.op eM.hom) :=
        (isIso_prod_iff _ _).mpr ⟨inferInstance, inferInstance⟩
      exact (IntegralHom.hom X
        (completedIntegralCommRingSheafUnrestricted l L X)).map_isIso _
  refine ⟨a, b, sE, sL, mE, mL, ?_,
    comparison_identity_E l E X D hl wE a hevalE,
    comparison_identity_E l L X D hl wL b hn,
    ?_⟩
  swap
  · intro F _ _ _ j wF c hc
    obtain ⟨h₃, h₄, h₅⟩ :=
      comparison_composition_transpose l E L ι X D hl wE wL a b hevalE hn F j wF c hc
    refine ⟨?_, ?_, h₃, h₄, h₅, ?_⟩
    · intro K
      exact DirectScalarCoherence.source_unit l E L ι X K.obj K.property.1
    · intro K
      exact DirectScalarCoherence.target_unit l E L ι X K.obj K.property.1
    · intro G _ _ _ k K
      exact DirectScalarCoherence.associativity l E L F G ι j k X K.obj K.property.1
  refine ⟨htri, ?_, hu, hv, ?_, ?_, ?_, hdelta, ?_, hvred, hbred⟩
  · intro K
    exact sfIntegralScalarExtension_constructible D.p l hl E L ι X K.obj K.property
  · intro K
    let huK : IsIso (u l E L ι X D hl wE wL) := hu
    let hvK : IsIso (v l E L ι X a b K.obj wE.omega.obj K.property.1
        wE.omega.property.1) := hv K wE.omega
    unfold beta
    have : IsIso (Prod.mkHom
        (𝟙 (op ((integralScalarExtensionOfUniverses l E L ι X).obj K.obj)))
        (u l E L ι X D hl wE wL)) :=
      (isIso_prod_iff _ _).mpr ⟨inferInstance, hu⟩
    infer_instance
  · intro K M
    exact v_evaluation l E L ι X a b hn K.obj M.obj K.property.1 M.property.1
  · intro K
    unfold beta
    let H := IntegralHom.hom.{u, u} X (completedIntegralCommRingSheafUnrestricted l L X)
    let T := integralScalarExtensionOfUniverses l E L ι X
    have ht : b.tensor.map (Prod.mkHom (𝟙 (T.obj K.obj))
        (v l E L ι X a b K.obj wE.omega.obj K.property.1 wE.omega.property.1 ≫
          H.map (Prod.mkHom (𝟙 _) (u l E L ι X D hl wE wL)))) =
        b.tensor.map (Prod.mkHom (𝟙 _)
          (v l E L ι X a b K.obj wE.omega.obj K.property.1 wE.omega.property.1)) ≫
        b.tensor.map (Prod.mkHom (𝟙 _)
          (H.map (Prod.mkHom (𝟙 _) (u l E L ι X D hl wE wL)))) := by
      rw [← b.tensor.map_comp]
      simp only [prod_comp, Category.id_comp]
    rw [ht, Category.assoc]
    have he := (b.adjunction (T.obj K.obj)).counit.naturality
      (u l E L ι X D hl wE wL)
    change b.tensor.map (Prod.mkHom (𝟙 _)
        (v l E L ι X a b K.obj wE.omega.obj K.property.1 wE.omega.property.1)) ≫
      (b.tensor.map (Prod.mkHom (𝟙 _) (H.map (Prod.mkHom (𝟙 _)
        (u l E L ι X D hl wE wL)))) ≫ _) = _
    simp only [Functor.comp_map, Functor.curry_obj_obj_map, Functor.id_map] at he
    erw [he, ← Category.assoc,
      v_evaluation l E L ι X a b hn K.obj wE.omega.obj K.property.1 wE.omega.property.1]
  · exact u_reduction l E L ι X D hl wE wL

end WeilConjectures
