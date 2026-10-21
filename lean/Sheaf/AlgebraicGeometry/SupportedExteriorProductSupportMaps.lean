/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H3
-/
module
public import Sheaf.AlgebraicGeometry.NormalizedSupportTriangle
import Sheaf.AlgebraicGeometry.SupportedTensorComparisonNaturality
import all Sheaf.AlgebraicGeometry.SupportedExteriorProduct
import all Sheaf.AlgebraicGeometry.SupportedCoefficientDerivedOpenMate
/-! # Supported exterior products and maps of supports -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry.Etale
attribute [local instance] supportedHasSheafify supportedHasWeakSheafify
private noncomputable def coefficientMap (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c]
    (r : supportedEtaleSections A T b.openComplement ⟶
      supportedEtaleSections A T c.openComplement) :
    supportedCoefficients A c ⟶ supportedCoefficients A b :=
  (conjugateEquiv (supportedCoefficientAdjunction A b)
    (supportedCoefficientAdjunction A c)).symm r

@[reassoc] private theorem coefficientMap_quotient (A : Type (u + 1)) [CommRing A]
    {T B C : Scheme.{u}} (b : B ⟶ T) (c : C ⟶ T)
    [IsClosedImmersion b] [IsClosedImmersion c]
    (r : supportedEtaleSections A T b.openComplement ⟶
      supportedEtaleSections A T c.openComplement)
    (hr : r ≫ supportedEtaleSectionsι A T c.openComplement =
      supportedEtaleSectionsι A T b.openComplement) (M : ModuleCat.{u + 1} A) :
    supportedCoefficientQuotient A c M ≫ (coefficientMap A b c r).app M =
      supportedCoefficientQuotient A b M := by
  let ab := supportedCoefficientAdjunction A b
  let ac := supportedCoefficientAdjunction A c
  have h : ac.homEquiv _ _ ((coefficientMap A b c r).app M) =
      ab.unit.app M ≫ r.app ((supportedCoefficients A b).obj M) := by
    symm
    exact unit_conjugateEquiv_symm ab ac r M
  have h₁ := (exists_unique_supportedCoefficientAdjunction A c).choose_spec.1 M _
    (ac.homEquiv _ _ ((coefficientMap A b c r).app M))
  erw [Equiv.symm_apply_apply] at h₁
  rw [h₁, h]
  have h₂ := NatTrans.congr_app hr ((supportedCoefficients A b).obj M)
  dsimp only [NatTrans.comp_app] at h₂
  rw [Category.assoc, h₂]
  have hb := (exists_unique_supportedCoefficientAdjunction A b).choose_spec.1 M _
    (ab.unit.app M)
  have he : (ab.homEquiv M _).symm (ab.unit.app M) = 𝟙 _ := by
    exact ab.homEquiv_symm_unit M
  change supportedCoefficientQuotient A b M ≫ (ab.homEquiv M _).symm
    (ab.unit.app M) = _ at hb
  rw [he, Category.comp_id] at hb
  exact hb.symm
@[reassoc]
private theorem derived_conjugate_counit
    {B C : Type*} [Category B] [Category C] [Abelian B] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    {F F' : B ⥤ C} {R R' : C ⥤ B}
    [F.Additive] [R.Additive] [F'.Additive] [R'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (adj : F ⊣ R) (adj' : F' ⊣ R') (r : R ⟶ R') (X : DerivedCategory C) :
    F'.mapDerivedCategory.map ((Functor.rightDerivedFunctorNatTrans r).app X) ≫
        adj'.mapDerivedCategoryRightDerivedAdjunction.counit.app X =
      (Functor.exactDerivedMap ((conjugateEquiv adj adj').symm r)).app
          (R.rightDerivedFunctor.obj X) ≫
        adj.mapDerivedCategoryRightDerivedAdjunction.counit.app X := by
  let a := (conjugateEquiv adj adj').symm r
  let α : R.rightDerivedFunctor ⋙ F'.mapDerivedCategory ⟶ 𝟭 (DerivedCategory C) :=
    Functor.whiskerRight (Functor.rightDerivedFunctorNatTrans r) F'.mapDerivedCategory ≫
      adj'.mapDerivedCategoryRightDerivedAdjunction.counit
  let β : R.rightDerivedFunctor ⋙ F'.mapDerivedCategory ⟶ 𝟭 (DerivedCategory C) :=
    Functor.whiskerLeft R.rightDerivedFunctor (Functor.exactDerivedMap a) ≫
      adj.mapDerivedCategoryRightDerivedAdjunction.counit
  have h : α = β := by
    apply (R.rightDerivedFunctor ⋙ F'.mapDerivedCategory).rightDerived_ext
      (Functor.whiskerRight R.rightDerivedFunctorUnit F'.mapDerivedCategory ≫
        (Functor.associator _ _ _).hom) (HomotopyCategory.quasiIso C (.up ℤ))
    ext K
    dsimp only [α, β, NatTrans.comp_app, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Functor.associator_hom_app]
    simp only [Category.comp_id]
    change F'.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
      (F'.mapDerivedCategory.map ((Functor.rightDerivedFunctorNatTrans r).app
        (DerivedCategory.Qh.obj K)) ≫ _) =
      F'.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
        ((Functor.exactDerivedMap a).app _ ≫ _)
    rw [← CategoryTheory.Functor.map_comp_assoc]
    erw [Functor.rightDerivedNatTrans_app]
    rw [CategoryTheory.Functor.map_comp, Category.assoc]
    erw [(adj'.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
      (HomotopyCategory.quasiIso C (.up ℤ)) F'.mapDerivedCategoryFactorsh.hom
        R'.rightDerivedFunctorUnit K]
    rw [(Functor.exactDerivedMap a).naturality_assoc]
    erw [(adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
      (HomotopyCategory.quasiIso C (.up ℤ)) F.mapDerivedCategoryFactorsh.hom
        R.rightDerivedFunctorUnit K]
    dsimp only [Functor.whiskerRight_app]
    erw [F'.mapDerivedCategoryFactorsh.hom.naturality_assoc, reassoc_of% exactMap_fac a _]
    dsimp only [Functor.comp_map]
    simp only [← DerivedCategory.Qh.map_comp]
    congr 2
    obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    erw [Adjunction.mapHomotopyCategory_counit_app_quotient,
      Adjunction.mapHomotopyCategory_counit_app_quotient]
    change (HomotopyCategory.quotient C (.up ℤ)).map
        ((F'.mapHomologicalComplex (.up ℤ)).map
          ((NatTrans.mapHomologicalComplex r (.up ℤ)).app P) ≫
            (adj'.mapHomologicalComplex (.up ℤ)).counit.app P) =
      (HomotopyCategory.quotient C (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex a (.up ℤ)).app
          ((R.mapHomologicalComplex (.up ℤ)).obj P) ≫
            (adj.mapHomologicalComplex (.up ℤ)).counit.app P)
    congr 1
    ext n
    simpa only [a, Functor.mapHomologicalComplex_obj_X, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f,
      Adjunction.mapHomologicalComplex_counit_app_f] using
      conjugateEquiv_counit_symm adj adj' r (P.X n)
  exact NatTrans.congr_app h X

@[reassoc]
private theorem exactMap_comp
    {B C D : Type*} [Category B] [Category C] [Category D]
    [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
    {F F' : B ⥤ C} [F.Additive] [F'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (a : F' ⟶ F) (M : DerivedCategory B) :
    (Functor.exactDerivedMap (Functor.whiskerRight a P)).app M ≫
        (Functor.mapDerivedCategoryCompIso F P).hom.app M =
      (Functor.mapDerivedCategoryCompIso F' P).hom.app M ≫
        P.mapDerivedCategory.map ((Functor.exactDerivedMap a).app M) := by
  have h : Functor.exactDerivedMap (Functor.whiskerRight a P) ≫
      (Functor.mapDerivedCategoryCompIso F P).hom =
      (Functor.mapDerivedCategoryCompIso F' P).hom ≫
        Functor.whiskerRight (Functor.exactDerivedMap a) P.mapDerivedCategory := by
    apply Localization.natTrans_ext DerivedCategory.Qh
      (HomotopyCategory.quasiIso B (.up ℤ))
    intro K
    apply (cancel_mono (P.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app K) ≫
      P.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj K))).1
    simp only [NatTrans.comp_app, Functor.whiskerRight_app, Category.assoc]
    erw [Functor.mapDerivedCategoryCompIso_hom_app_factorsh,
      exactMap_fac (Functor.whiskerRight a P) K]
    rw [← P.mapDerivedCategory.map_comp_assoc, exactMap_fac,
      P.mapDerivedCategory.map_comp, Category.assoc]
    erw [P.mapDerivedCategoryFactorsh.hom.naturality]
    erw [reassoc_of% Functor.mapDerivedCategoryCompIso_hom_app_factorsh F' P K]
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    rfl
  exact NatTrans.congr_app h M


@[reassoc]
private theorem derived_evaluation_conjugate
    {B C D : Type*} [Category B] [Category C] [Category D]
    [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory B] [HasDerivedCategory C] [HasDerivedCategory D]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    {F F' : B ⥤ C} {R R' : C ⥤ B}
    [F.Additive] [R.Additive] [F'.Additive] [R'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (adj : F ⊣ R) (adj' : F' ⊣ R')
    (P : C ⥤ D) [P.Additive] [PreservesFiniteLimits P] [PreservesFiniteColimits P]
    (r : R ⟶ R') (K : DerivedCategory C)
    {Y : DerivedCategory D} (z : P.mapDerivedCategory.obj K ⟶ Y) :
    (F' ⋙ P).mapDerivedCategory.map ((Functor.rightDerivedFunctorNatTrans r).app K) ≫
      (Functor.mapDerivedCategoryCompIso F' P).hom.app (R'.rightDerivedFunctor.obj K) ≫
        P.mapDerivedCategory.map (adj'.mapDerivedCategoryRightDerivedAdjunction.counit.app K) ≫
          z =
    (Functor.exactDerivedMap (Functor.whiskerRight
        ((conjugateEquiv adj adj').symm r) P)).app (R.rightDerivedFunctor.obj K) ≫
      (Functor.mapDerivedCategoryCompIso F P).hom.app (R.rightDerivedFunctor.obj K) ≫
        P.mapDerivedCategory.map (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app K) ≫
          z := by
  rw [(Functor.mapDerivedCategoryCompIso F' P).hom.naturality_assoc]
  dsimp only [Functor.comp_map]
  rw [← P.mapDerivedCategory.map_comp_assoc, derived_conjugate_counit adj adj' r K,
    P.mapDerivedCategory.map_comp]
  simp only [Category.assoc, exactMap_comp_assoc]

@[reassoc]
private theorem derived_conjugate_transpose
    {B C : Type*} [Category B] [Category C] [Abelian B] [Abelian C]
    [HasDerivedCategory B] [HasDerivedCategory C]
    [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    {F F' : B ⥤ C} {R R' : C ⥤ B}
    [F.Additive] [R.Additive] [F'.Additive] [R'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    (adj : F ⊣ R) (adj' : F' ⊣ R') (r : R ⟶ R')
    {M : DerivedCategory B} {K : DerivedCategory C}
    (t : F.mapDerivedCategory.obj M ⟶ K) :
    adj'.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
        ((Functor.exactDerivedMap ((conjugateEquiv adj adj').symm r)).app M ≫ t) =
      adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _ t ≫
        (Functor.rightDerivedFunctorNatTrans r).app K := by
  apply (adj'.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _).symm.injective
  rw [Equiv.symm_apply_apply, Adjunction.homEquiv_symm_apply,
    CategoryTheory.Functor.map_comp, Category.assoc, derived_conjugate_counit adj adj' r K,
    (Functor.exactDerivedMap ((conjugateEquiv adj adj').symm r)).naturality_assoc]
  have ht := (adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv M K).symm_apply_apply t
  change F.mapDerivedCategory.map
    (adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv M K t) ≫
      adj.mapDerivedCategoryRightDerivedAdjunction.counit.app K = t at ht
  rw [ht]


private def support_bimap {C : Type*} [Category C] (T : C ⥤ C ⥤ C)
    {U U' V V' : C} (a : U ⟶ U') (b : V ⟶ V') :
    (T.obj U).obj V ⟶ (T.obj U').obj V' :=
  (T.map a).app V ≫ (T.obj U').map b

private theorem support_bimap_comp {C : Type*} [Category C] (T : C ⥤ C ⥤ C)
    {U U' U'' V V' V'' : C} (a : U ⟶ U') (b : V ⟶ V')
    (a' : U' ⟶ U'') (b' : V' ⟶ V'') :
    support_bimap T a b ≫ support_bimap T a' b' = support_bimap T (a ≫ a') (b ≫ b') := by
  simp only [support_bimap, Category.assoc, Functor.map_comp, NatTrans.comp_app]
  rw [(T.map a').naturality_assoc b]


private theorem support_pairing_conjugate
    {B C : Type*} [Category B] [MonoidalCategory B] [Category C]
    {F F' : B ⥤ C} {R R' : C ⥤ B} (adj : F ⊣ R) (adj' : F' ⊣ R')
    (α : F' ⟶ F) (r : R ⟶ R') (T : C ⥤ C ⥤ C)
    (hp : ∀ (Z : B) (P : C) (t : F.obj Z ⟶ P),
      adj'.homEquiv _ _ (α.app Z ≫ t) = adj.homEquiv _ _ t ≫ r.app P)
    {M M' N N' : B} {U V U₀ V₀ U' V' P Q : C}
    (a : M ⟶ M') (e : N ⟶ N')
    (t : F.obj (M ⊗ N) ⟶ (T.obj U).obj V)
    (t₀ : F'.obj (M ⊗ N) ⟶ (T.obj U₀).obj V₀)
    (t' : F'.obj (M' ⊗ N') ⟶ (T.obj U').obj V')
    (c : U₀ ⟶ U) (d : V₀ ⟶ V) (a' : U₀ ⟶ U') (e' : V₀ ⟶ V')
    (v : U ⟶ P) (w : V ⟶ Q) (v' : U' ⟶ P) (w' : V' ⟶ Q)
    (hc : α.app (M ⊗ N) ≫ t = t₀ ≫ support_bimap T c d)
    (hn : F'.map (a ⊗ₘ e) ≫ t' = t₀ ≫ support_bimap T a' e')
    (hv : a' ≫ v' = c ≫ v) (hw : e' ≫ w' = d ≫ w) :
    adj.homEquiv _ _ (t ≫ support_bimap T v w) ≫ r.app ((T.obj P).obj Q) =
      (a ⊗ₘ e) ≫ adj'.homEquiv _ _ (t' ≫ support_bimap T v' w') := by
  rw [← hp, ← adj'.homEquiv_naturality_left]
  congr 1
  rw [← Category.assoc, hc, Category.assoc, support_bimap_comp,
    ← hv, ← hw, ← support_bimap_comp, ← Category.assoc, ← hn, Category.assoc]


private theorem support_scheme_tensor_naturality
    (E : Type (u + 2)) [Category.{u + 1} E] [Abelian E]
    [IsGrothendieckAbelian.{u + 1} E] [HasDerivedCategory.{u + 1} E]
    [MonoidalCategory E] [MonoidalPreadditive E] [SymmetricCategory E] [MonoidalClosed E]
    [Abelian.HasFunctorialFlatResolution E] (P : Scheme.{u})
    (G F₁ F₂ G' F₁' F₂' : E ⥤ Sheaf P.smallEtaleTopology E)
    [G.Additive] [F₁.Additive] [F₂.Additive] [G'.Additive] [F₁'.Additive] [F₂'.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    [PreservesFiniteLimits F₁'] [PreservesFiniteColimits F₁']
    [PreservesFiniteLimits F₂'] [PreservesFiniteColimits F₂']
    [G.IsLeftAdjoint] [G'.IsLeftAdjoint] [F₂.PreservesFlat] [F₂.IsLeftAdjoint]
    (τ : (Functor.postcompose₂.obj G).obj (curriedTensor E) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj (supportedSheafTensorGeneric E P))
    (τ' : (Functor.postcompose₂.obj G').obj (curriedTensor E) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁').obj F₂').obj (supportedSheafTensorGeneric E P))
    (t : supportedSchemeDerivedHom E P G F₁ F₂)
    (t' : supportedSchemeDerivedHom E P G' F₁' F₂')
    (ht : supportedSchemeDerivedCondition E P G F₁ F₂ τ t)
    (ht' : supportedSchemeDerivedCondition E P G' F₁' F₂' τ' t')
    (a₀ : G' ⟶ G) (a₁ : F₁' ⟶ F₁) (a₂ : F₂' ⟶ F₂)
    (ha : ∀ M N, a₀.app (M ⊗ N) ≫ (τ.app M).app N =
      (τ'.app M).app N ≫ (a₁.app M ⊗ₘ a₂.app N))
    (M N : DerivedCategory E) :
    (Functor.exactDerivedMap a₀).app (M ⊗ N) ≫
        supportedSchemeDerivedApply E P G F₁ F₂ t M N =
      supportedSchemeDerivedApply E P G' F₁' F₂' t' M N ≫
        support_bimap (derivedTensor E P)
          ((Functor.exactDerivedMap a₁).app M) ((Functor.exactDerivedMap a₂).app N) := by
  exact supportedDerivedComparison_naturality G F₁ F₂ G' F₁' F₂' τ τ' t t' ht ht'
    a₀ a₁ a₂ ha M N

private theorem support_schemeComparison_natural
    (E : Type (u + 2)) [Category.{u + 1} E] [Abelian E]
    [IsGrothendieckAbelian.{u + 1} E] [HasDerivedCategory.{u + 1} E]
    [MonoidalCategory E] [MonoidalPreadditive E] [SymmetricCategory E] [MonoidalClosed E]
    [Abelian.HasFunctorialFlatResolution E] (T : Scheme.{u})
    (G F₁ F₂ : E ⥤ Sheaf T.smallEtaleTopology E)
    [G.Additive] [F₁.Additive] [F₂.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F₁] [PreservesFiniteColimits F₁]
    [PreservesFiniteLimits F₂] [PreservesFiniteColimits F₂] [G.IsLeftAdjoint]
    (τ : (Functor.postcompose₂.obj G).obj (curriedTensor E) ⟶
      (((Functor.whiskeringLeft₂ _).obj F₁).obj F₂).obj
        (supportedSheafTensorGeneric E T))
    (t : supportedSchemeDerivedHom E T G F₁ F₂)
    (ht : supportedSchemeDerivedCondition E T G F₁ F₂ τ t)
    {M M' N N' : DerivedCategory E} (a : M ⟶ M') (b : N ⟶ N') :
    G.mapDerivedCategory.map (a ⊗ₘ b) ≫ supportedSchemeDerivedApply E T G F₁ F₂ t M' N' =
      supportedSchemeDerivedApply E T G F₁ F₂ t M N ≫
        support_bimap (derivedTensor E T) (F₁.mapDerivedCategory.map a)
          (F₂.mapDerivedCategory.map b) := by
  exact ht.1 M M' N N' a b


section SupportMaps
variable (A : Type (u + 1)) [CommRing A]
    {S X Y B B' D D' : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (b : B ⟶ X) (b' : B' ⟶ X) (d : D ⟶ Y) (d' : D' ⟶ Y)
    [IsClosedImmersion b] [IsClosedImmersion b']
    [IsClosedImmersion d] [IsClosedImmersion d']
    (r₁ : supportedEtaleSections A X b.openComplement ⟶
      supportedEtaleSections A X b'.openComplement)
    (r₂ : supportedEtaleSections A Y d.openComplement ⟶
      supportedEtaleSections A Y d'.openComplement)
    (r₀ : supportedEtaleSections A (pullback f g)
        (supportedProductImmersion f g b d).openComplement ⟶
      supportedEtaleSections A (pullback f g)
        (supportedProductImmersion f g b' d').openComplement)
    (hr₁ : r₁ ≫ supportedEtaleSectionsι A X b'.openComplement =
      supportedEtaleSectionsι A X b.openComplement)
    (hr₂ : r₂ ≫ supportedEtaleSectionsι A Y d'.openComplement =
      supportedEtaleSectionsι A Y d.openComplement)
    (hr₀ : r₀ ≫ supportedEtaleSectionsι A (pullback f g)
        (supportedProductImmersion f g b' d').openComplement =
      supportedEtaleSectionsι A (pullback f g)
        (supportedProductImmersion f g b d).openComplement)

include hr₁ hr₂ hr₀

private theorem ordinary_support_tensor (M N : ModuleCat.{u + 1} A) :
    (coefficientMap A (supportedProductImmersion f g b d)
        (supportedProductImmersion f g b' d') r₀).app (M ⊗ N) ≫
      supportedCoefficientTensor A f g b d M N =
    supportedCoefficientTensor A f g b' d' M N ≫
      ((Functor.whiskerRight (coefficientMap A b b' r₁)
          (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g))).app M ⊗ₘ
        (Functor.whiskerRight (coefficientMap A d d' r₂)
          (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g))).app N) := by
  have := coefficientQuotient_epi A (supportedProductImmersion f g b' d') (M ⊗ N)
  apply (cancel_epi (supportedCoefficientQuotient A
    (supportedProductImmersion f g b' d') (M ⊗ N))).1
  rw [← Category.assoc, coefficientMap_quotient A _ _ r₀ hr₀,
    coefficientTensor_spec,
    reassoc_of% coefficientTensor_spec A f g b' d' M N, tensorHom_comp_tensorHom]
  congr 1
  have h₁ := coefficientMap_quotient A b b' r₁ hr₁ M
  have h₂ := coefficientMap_quotient A d d' r₂ hr₂ N
  symm
  change (_ ≫ (upperStar _ _).map _) ≫ (upperStar _ _).map _ ⊗ₘ
    (_ ≫ (upperStar _ _).map _) ≫ (upperStar _ _).map _ = _ ⊗ₘ _
  rw [Category.assoc, Category.assoc, ← CategoryTheory.Functor.map_comp,
    ← CategoryTheory.Functor.map_comp]
  erw [h₁, h₂]
  rfl

private theorem derived_support_tensor (M N : DerivedCategory (ModuleCat.{u + 1} A)) :
    (Functor.exactDerivedMap (coefficientMap A (supportedProductImmersion f g b d)
        (supportedProductImmersion f g b' d') r₀)).app (M ⊗ N) ≫
      supportedCoefficientTensorDerived A f g b d M N =
    supportedCoefficientTensorDerived A f g b' d' M N ≫
      support_bimap (derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
        ((Functor.exactDerivedMap (Functor.whiskerRight (coefficientMap A b b' r₁)
          (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)))).app M)
        ((Functor.exactDerivedMap (Functor.whiskerRight (coefficientMap A d d' r₂)
          (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)))).app N) := by
  have : (supportedCoefficients A d).PreservesFlat := coefficients_preserveFlat A d
  have : (supportedSecondCoefficients A f g d).PreservesFlat :=
    ⟨fun h ↦ Functor.PreservesFlat.flat_obj (F := upperStar (ModuleCat.{u + 1} A)
      (pullback.snd f g)) (Functor.PreservesFlat.flat_obj h)⟩
  have h := support_scheme_tensor_naturality (ModuleCat.{u + 1} A) (pullback f g)
    (supportedCoefficients A (supportedProductImmersion f g b d))
    (supportedFirstCoefficients A f g b) (supportedSecondCoefficients A f g d)
    (supportedCoefficients A (supportedProductImmersion f g b' d'))
    (supportedFirstCoefficients A f g b') (supportedSecondCoefficients A f g d')
    (supportedCoefficientTensorNatTrans A f g b d)
    (supportedCoefficientTensorNatTrans A f g b' d')
    (exists_unique_supportedCoefficientTensorDerived A f g b d).choose
    (exists_unique_supportedCoefficientTensorDerived A f g b' d').choose
    (exists_unique_supportedCoefficientTensorDerived A f g b d).choose_spec.1
    (exists_unique_supportedCoefficientTensorDerived A f g b' d').choose_spec.1
    (coefficientMap A (supportedProductImmersion f g b d)
      (supportedProductImmersion f g b' d') r₀)
    (Functor.whiskerRight (coefficientMap A b b' r₁)
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)))
    (Functor.whiskerRight (coefficientMap A d d' r₂)
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)))
    (ordinary_support_tensor A f g b b' d d' r₁ r₂ r₀ hr₁ hr₂ hr₀) M N
  exact h

attribute [local irreducible] derivedTensor

/-- The exterior product commutes with normalized inclusions of closed supports.
Source: Stacks Tag 0F1E, naturality of the supported cup product under support maps
(blueprint: lem-pur-supported-exterior-product-support-maps).
Proof: conjugate each support inclusion under the normalized coefficient adjunction.
Its coefficient map preserves the constant quotient, as follows by transposing the
kernel-inclusion normalization. Cancel the epic product coefficient quotient to
obtain the ordinary coefficient tensor square. Naturality of the normalized derived
tensor comparison gives the derived square. The derived conjugate counit identity
identifies its two projected maps with the prescribed maps on supported sections.
Transpose this square under the product coefficient adjunction; naturality in the
two coefficient arguments gives precisely the claimed equality. -/
theorem supportedExteriorProduct_supportMaps
    (K : DerivedCategoryModule A X) (L : DerivedCategoryModule A Y) :
    supportedExteriorProduct A f g b d K L ≫
        (Functor.rightDerivedFunctorNatTrans r₀).app
          (externalProduct (ModuleCat.{u + 1} A) f g K L) =
      ((Functor.rightDerivedFunctorNatTrans r₁).app K ⊗ₘ
        (Functor.rightDerivedFunctorNatTrans r₂).app L) ≫
          supportedExteriorProduct A f g b' d' K L := by
  let M := (supportedSectionsDerived A b).obj K
  let N := (supportedSectionsDerived A d).obj L
  let M' := (supportedSectionsDerived A b').obj K
  let N' := (supportedSectionsDerived A d').obj L
  let a := (Functor.rightDerivedFunctorNatTrans r₁).app K
  let e := (Functor.rightDerivedFunctorNatTrans r₂).app L
  let a₁ := Functor.whiskerRight (coefficientMap A b b' r₁)
    (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g))
  let a₂ := Functor.whiskerRight (coefficientMap A d d' r₂)
    (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g))
  have hv : (supportedFirstCoefficients A f g b').mapDerivedCategory.map a ≫
      supportedFirstEvaluation A f g b' K =
      (Functor.exactDerivedMap a₁).app M ≫ supportedFirstEvaluation A f g b K := by
    exact derived_evaluation_conjugate (supportedCoefficientAdjunction A b)
      (supportedCoefficientAdjunction A b')
      (upperStar (ModuleCat.{u + 1} A) (pullback.fst f g)) r₁ K
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.fst f g)).inv.app K)
  have hw : (supportedSecondCoefficients A f g d').mapDerivedCategory.map e ≫
      supportedSecondEvaluation A f g d' L =
      (Functor.exactDerivedMap a₂).app N ≫ supportedSecondEvaluation A f g d L := by
    exact derived_evaluation_conjugate (supportedCoefficientAdjunction A d)
      (supportedCoefficientAdjunction A d')
      (upperStar (ModuleCat.{u + 1} A) (pullback.snd f g)) r₂ L
      ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A)
        (pullback.snd f g)).inv.app L)
  have hn : (supportedCoefficients A (supportedProductImmersion f g b' d')).mapDerivedCategory.map
        (a ⊗ₘ e) ≫ supportedCoefficientTensorDerived A f g b' d' M' N' =
      supportedCoefficientTensorDerived A f g b' d' M N ≫
        support_bimap (derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
          ((supportedFirstCoefficients A f g b').mapDerivedCategory.map a)
          ((supportedSecondCoefficients A f g d').mapDerivedCategory.map e) := by
    exact support_schemeComparison_natural (ModuleCat.{u + 1} A) (pullback f g)
      (supportedCoefficients A (supportedProductImmersion f g b' d'))
      (supportedFirstCoefficients A f g b') (supportedSecondCoefficients A f g d')
      (supportedCoefficientTensorNatTrans A f g b' d')
      (exists_unique_supportedCoefficientTensorDerived A f g b' d').choose
      (exists_unique_supportedCoefficientTensorDerived A f g b' d').choose_spec.1 a e
  unfold supportedExteriorProduct
  dsimp only [externalProduct]
  refine support_pairing_conjugate
    (supportedCoefficientDerivedAdjunction A (supportedProductImmersion f g b d))
    (supportedCoefficientDerivedAdjunction A (supportedProductImmersion f g b' d'))
    (Functor.exactDerivedMap (coefficientMap A (supportedProductImmersion f g b d)
      (supportedProductImmersion f g b' d') r₀))
    (Functor.rightDerivedFunctorNatTrans r₀)
    (derivedTensor (ModuleCat.{u + 1} A) (pullback f g))
    (fun Z P t ↦ derived_conjugate_transpose
      (supportedCoefficientAdjunction A (supportedProductImmersion f g b d))
      (supportedCoefficientAdjunction A (supportedProductImmersion f g b' d')) r₀ t)
    a e _ (supportedCoefficientTensorDerived A f g b' d' M N) _
    ((Functor.exactDerivedMap a₁).app M) ((Functor.exactDerivedMap a₂).app N)
    ((supportedFirstCoefficients A f g b').mapDerivedCategory.map a)
    ((supportedSecondCoefficients A f g d').mapDerivedCategory.map e)
    _ _ _ _ ?_ ?_ hv hw
  · exact derived_support_tensor A f g b b' d d' r₁ r₂ r₀ hr₁ hr₂ hr₀ M N
  · exact hn
end SupportMaps

end AlgebraicGeometry.Etale
