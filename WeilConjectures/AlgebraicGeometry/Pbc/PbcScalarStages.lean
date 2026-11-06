/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarRationalShift
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarRationalShift
import all WeilConjectures.AlgebraicGeometry.Pbc.PbcScalarComposition
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Normalized finite-field stages and their coherence

Source: blueprint proper base change, order 1307; Milne, Section 19.
Existing declarations extracted from `PbcScalarExtension` to bound compilation cost.
(blueprint: lem-pbc-scalar-stage-coherence)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
open scoped TensorProduct
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [local irreducible] AlgebraicGeometry.Scheme.pbcRationalCoefficientEquiv

namespace CategoryTheory.Functor

variable {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]
  [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
  [HasDerivedCategory C₀] [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory C₃]

end CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {C₀ C₁ C₂ C₃ : Type*} [Category* C₀] [Category* C₁] [Category* C₂] [Category* C₃]

/-- Pentagon for composition isomorphisms conjugated by normalizations. -/
theorem normalized_comp_assoc
    {R₀₁ T₀₁ : C₀ ⥤ C₁} {R₁₂ T₁₂ : C₁ ⥤ C₂} {R₂₃ T₂₃ : C₂ ⥤ C₃} {R₀₂ T₀₂ : C₀ ⥤ C₂}
    {R₁₃ T₁₃ : C₁ ⥤ C₃} {R₀₃ T₀₃ : C₀ ⥤ C₃} {S₀₂ : C₀ ⥤ C₂} {S₁₃ : C₁ ⥤ C₃}
    {S₀₃ S₀₃' : C₀ ⥤ C₃}
    (N₀₁ : R₀₁ ≅ T₀₁) (N₁₂ : R₁₂ ≅ T₁₂) (N₂₃ : R₂₃ ≅ T₂₃) (N₀₂ : R₀₂ ≅ T₀₂)
    (N₁₃ : R₁₃ ≅ T₁₃) (N₀₃ : R₀₃ ≅ T₀₃)
    (c₀₁₂ : R₀₁ ⋙ R₁₂ ≅ S₀₂) (e₀₁₂ : S₀₂ ≅ R₀₂) (c₁₂₃ : R₁₂ ⋙ R₂₃ ≅ S₁₃) (e₁₂₃ : S₁₃ ≅ R₁₃)
    (c₀₂₃ : R₀₂ ⋙ R₂₃ ≅ S₀₃) (e₀₂₃ : S₀₃ ≅ R₀₃) (c₀₁₃ : R₀₁ ⋙ R₁₃ ≅ S₀₃')
    (e₀₁₃ : S₀₃' ≅ R₀₃)
    (h : ∀ K, R₂₃.map ((c₀₁₂ ≪≫ e₀₁₂).hom.app K) ≫ (c₀₂₃ ≪≫ e₀₂₃).hom.app K =
      (c₁₂₃ ≪≫ e₁₂₃).hom.app (R₀₁.obj K) ≫ (c₀₁₃ ≪≫ e₀₁₃).hom.app K) (K : C₀) :
    T₂₃.map ((isoWhiskerRight N₀₁.symm T₁₂ ≪≫ isoWhiskerLeft R₀₁ N₁₂.symm ≪≫ c₀₁₂ ≪≫ e₀₁₂ ≪≫
        N₀₂).hom.app K) ≫
      (isoWhiskerRight N₀₂.symm T₂₃ ≪≫ isoWhiskerLeft R₀₂ N₂₃.symm ≪≫ c₀₂₃ ≪≫ e₀₂₃ ≪≫
        N₀₃).hom.app K =
    (isoWhiskerRight N₁₂.symm T₂₃ ≪≫ isoWhiskerLeft R₁₂ N₂₃.symm ≪≫ c₁₂₃ ≪≫ e₁₂₃ ≪≫
        N₁₃).hom.app (T₀₁.obj K) ≫
      (isoWhiskerRight N₀₁.symm T₁₃ ≪≫ isoWhiskerLeft R₀₁ N₁₃.symm ≪≫ c₀₁₃ ≪≫ e₀₁₃ ≪≫
        N₀₃).hom.app K := by
  have hK := h K
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc] at hK
  have n₁ := N₂₃.inv.naturality (T₁₂.map (N₀₁.inv.app K) ≫ N₁₂.inv.app (R₀₁.obj K) ≫
    c₀₁₂.hom.app K ≫ e₀₁₂.hom.app K)
  have n₂ := N₂₃.inv.naturality (N₁₂.inv.app (T₀₁.obj K))
  have n₃ := N₁₃.hom.naturality (N₀₁.inv.app K)
  have n₄ := (c₁₂₃ ≪≫ e₁₂₃).hom.naturality (N₀₁.inv.app K)
  have n₅ := N₁₂.inv.naturality (N₀₁.inv.app K)
  simp only [Iso.trans_hom, NatTrans.comp_app, comp_map, Functor.map_comp,
    Category.assoc] at n₁ n₂ n₃ n₄ n₅
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    whiskerRight_app, whiskerLeft_app, Iso.symm_hom, Functor.map_comp, Category.assoc]
  rw [← T₂₃.map_comp_assoc (N₀₂.hom.app K), Iso.hom_inv_id_app, T₂₃.map_id, Category.id_comp,
    ← reassoc_of% n₃, Iso.hom_inv_id_app_assoc, ← reassoc_of% n₄, ← reassoc_of% hK,
    reassoc_of% n₁, reassoc_of% n₂, ← R₂₃.map_comp_assoc (T₁₂.map _), n₅, R₂₃.map_comp_assoc]

/-- Left unit law for composition isomorphisms conjugated by normalizations. -/
theorem normalized_comp_heq_leftUnitor {R₀₀ T₀₀ : C₀ ⥤ C₀} {R₀₁ T₀₁ : C₀ ⥤ C₁} {S : C₀ ⥤ C₁}
    (N₀₀ : R₀₀ ≅ T₀₀) (N₀₁ : R₀₁ ≅ T₀₁) (c : R₀₀ ⋙ R₀₁ ≅ S) (e : S ≅ R₀₁)
    (hT : T₀₀ = 𝟭 C₀) (U : R₀₀ ≅ 𝟭 C₀)
    (hN : ∀ K, N₀₀.hom.app K = U.hom.app K ≫ eqToHom (Functor.congr_obj hT K).symm)
    (p : ∀ K, R₀₁.obj K = R₀₁.obj K)
    (hc : ∀ K, (c ≪≫ e).hom.app K = R₀₁.map (U.hom.app K) ≫ eqToHom (p K)) :
    HEq (isoWhiskerRight N₀₀.symm T₀₁ ≪≫ isoWhiskerLeft R₀₀ N₀₁.symm ≪≫ c ≪≫ e ≪≫ N₀₁)
      (leftUnitor T₀₁) := by
  subst hT
  obtain rfl : N₀₀ = U := by
    ext K
    simpa using hN K
  apply heq_of_eq
  ext K
  have hK := hc K
  have n := N₀₁.inv.naturality (N₀₀.inv.app K)
  simp only [Iso.trans_hom, NatTrans.comp_app, eqToHom_refl, Category.comp_id] at hK
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    whiskerRight_app, whiskerLeft_app, Iso.symm_hom, leftUnitor_hom_app]
  rw [reassoc_of% hK, reassoc_of% n, ← R₀₁.map_comp_assoc, Iso.inv_hom_id_app]
  erw [R₀₁.map_id, Category.id_comp, Iso.inv_hom_id_app]

/-- Right unit law for composition isomorphisms conjugated by normalizations. -/
theorem normalized_comp_heq_rightUnitor {R₀₁ T₀₁ : C₀ ⥤ C₁} {R₁₁ T₁₁ : C₁ ⥤ C₁} {S : C₀ ⥤ C₁}
    (N₀₁ : R₀₁ ≅ T₀₁) (N₁₁ : R₁₁ ≅ T₁₁) (c : R₀₁ ⋙ R₁₁ ≅ S) (e : S ≅ R₀₁)
    (hT : T₁₁ = 𝟭 C₁) (U : R₁₁ ≅ 𝟭 C₁)
    (hN : ∀ K, N₁₁.hom.app K = U.hom.app K ≫ eqToHom (Functor.congr_obj hT K).symm)
    (p : ∀ K, R₀₁.obj K = R₀₁.obj K)
    (hc : ∀ K, (c ≪≫ e).hom.app K = U.hom.app (R₀₁.obj K) ≫ eqToHom (p K)) :
    HEq (isoWhiskerRight N₀₁.symm T₁₁ ≪≫ isoWhiskerLeft R₀₁ N₁₁.symm ≪≫ c ≪≫ e ≪≫ N₀₁)
      (rightUnitor T₀₁) := by
  subst hT
  obtain rfl : N₁₁ = U := by
    ext K
    simpa using hN K
  apply heq_of_eq
  ext K
  have hK := hc K
  simp only [Iso.trans_hom, NatTrans.comp_app, eqToHom_refl, Category.comp_id] at hK
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, isoWhiskerLeft_hom,
    whiskerRight_app, whiskerLeft_app, Iso.symm_hom, rightUnitor_hom_app]
  rw [reassoc_of% hK, Iso.inv_hom_id_app_assoc]
  erw [Iso.inv_hom_id_app]

end CategoryTheory.Functor

namespace AlgebraicGeometry.Scheme

section Ambient
variable {X : Scheme.{u}} {R₀ R₁ R₂ R₃ : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}

theorem pbcRestrictComp_hom_app_val {R S B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ) (M : pbcModules X B)
    (U : X.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcRestrictComp φ ψ χ h).hom.app M).val.app U x = x :=
  (pbcRestrictComp_exists φ ψ χ h).exists.choose_spec M U x

theorem pbcRestrictComp_assoc (φ₀₁ : R₀ ⟶ R₁) (φ₁₂ : R₁ ⟶ R₂) (φ₂₃ : R₂ ⟶ R₃)
    (φ₀₂ : R₀ ⟶ R₂) (φ₁₃ : R₁ ⟶ R₃) (φ₀₃ : R₀ ⟶ R₃) (h₀₁₂ : φ₀₁ ≫ φ₁₂ = φ₀₂)
    (h₁₂₃ : φ₁₂ ≫ φ₂₃ = φ₁₃) (h₀₂₃ : φ₀₂ ≫ φ₂₃ = φ₀₃) (h₀₁₃ : φ₀₁ ≫ φ₁₃ = φ₀₃) :
    isoWhiskerLeft (pbcRestrict φ₂₃) (pbcRestrictComp φ₀₁ φ₁₂ φ₀₂ h₀₁₂) ≪≫
        pbcRestrictComp φ₀₂ φ₂₃ φ₀₃ h₀₂₃ =
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (pbcRestrictComp φ₁₂ φ₂₃ φ₁₃ h₁₂₃)
        (pbcRestrict φ₀₁) ≪≫ pbcRestrictComp φ₀₁ φ₁₃ φ₀₃ h₀₁₃ := by
  apply Iso.ext
  ext M U x
  change ((pbcRestrictComp φ₀₂ φ₂₃ φ₀₃ h₀₂₃).hom.app M).val.app U
      (((pbcRestrictComp φ₀₁ φ₁₂ φ₀₂ h₀₁₂).hom.app ((pbcRestrict φ₂₃).obj M)).val.app U x) =
    ((pbcRestrictComp φ₀₁ φ₁₃ φ₀₃ h₀₁₃).hom.app M).val.app U
      (((pbcRestrictComp φ₁₂ φ₂₃ φ₁₃ h₁₂₃).hom.app M).val.app U x)
  erw [pbcRestrictComp_hom_app_val, pbcRestrictComp_hom_app_val, pbcRestrictComp_hom_app_val,
    pbcRestrictComp_hom_app_val]

theorem pbcReductionNormalization_hom_eq {R S B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ : R ⟶ B) (h : φ ≫ ψ = χ) (K : DerivedCategory (pbcModules X R)) :
    (pbcReductionNormalization φ ψ χ h K).hom =
      (Adjunction.leftAdjointCompIso (pbcDerivedScalarAdjunction φ)
        (pbcDerivedScalarAdjunction ψ) (pbcDerivedScalarAdjunction χ)
        (pbcDerivedRestrictComp φ ψ χ h)).hom.app K := by
  dsimp [pbcReductionNormalization, pbcReductionNormalizationHom, pbcReductionTransition]
  simp only [asIso_hom, Adjunction.leftAdjointCompIso_hom_app, Adjunction.homEquiv_counit,
    Functor.map_comp, Category.assoc]

theorem _root_.CategoryTheory.Adjunction.leftAdjointIdIso_eq_symm {C : Type*} [Category* C]
    {F G : C ⥤ C} (adj : F ⊣ G) (e : G ≅ 𝟭 C) :
    Adjunction.leftAdjointIdIso adj e =
      ((conjugateIsoEquiv adj Adjunction.id).symm e).symm := by
  apply Iso.ext
  apply (conjugateEquiv Adjunction.id adj).injective
  rw [Adjunction.conjugateEquiv_leftAdjointIdIso_hom]
  exact ((conjugateEquiv Adjunction.id adj).apply_symm_apply e.inv).symm

variable {R S : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}

/-- The ordinary-unit-normalized identity extension, conjugate to a restriction unit. -/
abbrev pbcDerivedExtendIdIso (ψ : R ⟶ R) (e : pbcRestrict ψ ≅ 𝟭 _) :
    pbcDerivedExtend (ψ) ≅ 𝟭 _ :=
  ((conjugateIsoEquiv (pbcDerivedScalarAdjunction (ψ))
    (Adjunction.id : (𝟭 (DerivedCategory (pbcModules X R))) ⊣ 𝟭 _)).symm
      (Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryIdIso _)).symm

theorem pbcRestrictComp_id_left (ψ : R ⟶ R) (φ : R ⟶ S) (h : ψ ≫ φ = φ) (e : pbcRestrict ψ ≅ 𝟭 _)
    (he : ∀ (M : pbcModules X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
      (e.hom.app M).val.app U x = x) :
    pbcRestrictComp (ψ) φ φ h = isoWhiskerLeft (pbcRestrict φ) e ≪≫
      rightUnitor (pbcRestrict φ) := by
  apply Iso.ext
  ext M U x
  change ((pbcRestrictComp (ψ) φ φ h).hom.app M).val.app U x =
    (e.hom.app ((pbcRestrict φ).obj M)).val.app U x
  erw [pbcRestrictComp_hom_app_val, he]

theorem pbcRestrictComp_id_right (φ : R ⟶ S) (ψ : S ⟶ S) (h : φ ≫ ψ = φ) (e : pbcRestrict ψ ≅ 𝟭 _)
    (he : ∀ (M : pbcModules X S) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
      (e.hom.app M).val.app U x = x) :
    pbcRestrictComp φ (ψ) φ h = isoWhiskerRight e (pbcRestrict φ) ≪≫
      leftUnitor (pbcRestrict φ) := by
  apply Iso.ext
  ext M U x
  change ((pbcRestrictComp φ (ψ) φ h).hom.app M).val.app U x =
    (e.hom.app M).val.app U x
  erw [pbcRestrictComp_hom_app_val, he]

theorem pbcDerivedExtendIdIso_congr (ψ : R ⟶ R) (hψ : ψ = 𝟙 R) (e : pbcRestrict (𝟙 R) ≅ 𝟭 _)
    (he : ∀ (M : pbcModules X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
      (e.hom.app M).val.app U x = x) :
    (∀ (M : pbcModules X R) (U : X.ProEtᵒᵖ) (x : M.val.obj U),
      ((eqToIso (congrArg (fun ψ ↦ pbcRestrict ψ) hψ) ≪≫ e).hom.app M).val.app U x = x) ∧
    eqToIso (congrArg (fun ψ ↦ pbcDerivedExtend ψ) hψ) ≪≫ pbcDerivedExtendIdIso _ e =
      pbcDerivedExtendIdIso ψ (eqToIso (congrArg (fun ψ ↦ pbcRestrict ψ) hψ) ≪≫ e) := by
  subst hψ
  rw [eqToIso_refl, eqToIso_refl, Iso.refl_trans, Iso.refl_trans]
  exact ⟨he, rfl⟩

theorem pbcReductionNormalization_congr {B : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    (φ : R ⟶ S) (ψ : S ⟶ B) (χ χ' : R ⟶ B) (h : φ ≫ ψ = χ) (h' : φ ≫ ψ = χ')
    (hχ : χ = χ') (K : DerivedCategory (pbcModules X R)) :
    (pbcReductionNormalization φ ψ χ' h' K).hom =
      (pbcReductionNormalization φ ψ χ h K).hom ≫
        eqToHom (congrArg (fun c ↦ (pbcDerivedExtend c).obj K) hχ) := by
  subst hχ
  rw [eqToHom_refl, Category.comp_id]

end Ambient

section Fields
variable (l : ℕ) [Fact l.Prime]
variable {E F G H : Type u} [Field E] [Field F] [Field G] [Field H]
variable [Algebra (Padic l) E] [Algebra (Padic l) F] [Algebra (Padic l) G] [Algebra (Padic l) H]
variable [FiniteDimensional (Padic l) E] [FiniteDimensional (Padic l) F]
variable [FiniteDimensional (Padic l) G] [FiniteDimensional (Padic l) H]
variable (T : Scheme.{u})

theorem pbcAmbientScalarComp_hom_app (i : E →ₐ[Padic l] F) (j : F →ₐ[Padic l] G)
    (K : PbcCompletedDerived T (pbcIntegralDatum l E)) :
    (pbcAmbientScalarComp l E F G i j T).hom.app K =
      (pbcReductionNormalization (pbcScalarCoefficientMap l E F i T)
        (pbcScalarCoefficientMap l F G j T) (pbcScalarCoefficientMap l E G (j.comp i) T)
        (pbcScalarCoefficientMap_comp l E F G i j T) K).hom := by
  unfold pbcAmbientScalarComp
  rfl

theorem pbcEmbeddingAmbientUnit_eq :
    pbcEmbeddingAmbientUnit l E T =
      eqToIso (congrArg (fun φ ↦ pbcDerivedExtend φ) (pbcScalarCoefficientMap_id l E T)) ≪≫
        pbcDerivedExtendIdIso _ (pbcScalarRestrictId l E T) := by
  rw [pbcEmbeddingAmbientUnit]


theorem pbcScalarRestrictId_hom_app_val
    (M : pbcModules T (pbcAdicCompletion T (pbcIntegralDatum l E)))
    (U : T.ProEtᵒᵖ) (x : M.val.obj U) :
    ((pbcScalarRestrictId l E T).hom.app M).val.app U x = x := by
  rw [pbcScalarRestrictId]
  exact (pbcScalarRestrictId_exists l E T).exists.choose_spec M U x

variable [IsNoetherian T] [dim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
variable [inv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

theorem pbcRationalScalarComp_hom_app (i : E →ₐ[Padic l] F) (j : F →ₐ[Padic l] G)
    (K : PbcRationalDerivedCategory l E T dim.out inv.out) :
    (pbcRationalScalarComp l E F G i j T dim.out inv.out).hom.app K =
      (pbcRationalization T (pbcIntegralDatum l G) (pbcUniformizer l G)).map
        (ObjectProperty.homMk ((pbcAmbientScalarComp l E F G i j T).hom.app K.obj.obj)) := by
  unfold pbcRationalScalarComp pbcRationalScalarCompComponent
  rfl

theorem pbcRationalScalarUnit_hom_app
    (K : PbcRationalDerivedCategory l E T dim.out inv.out) :
    (pbcRationalScalarUnit l E T dim.out inv.out).hom.app K =
      (pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).map
        (ObjectProperty.homMk ((pbcEmbeddingAmbientUnit l E T).hom.app K.obj.obj)) := by
  unfold pbcRationalScalarUnit pbcRationalScalarUnitComponent
  rfl

theorem pbcRationalScalarExtension_map_rationalization (i : E →ₐ[Padic l] F)
    {K L : PbcRationalDerivedCategory l E T dim.out inv.out} (f : K.obj ⟶ L.obj) :
    (pbcRationalScalarExtension l E F i T dim.out inv.out).map
        ((pbcRationalization T (pbcIntegralDatum l E) (pbcUniformizer l E)).map f : K ⟶ L) =
      (pbcRationalization T (pbcIntegralDatum l F) (pbcUniformizer l F)).map
        ((pbcEmbeddingIntegralTensor l E F i T dim.out inv.out).map f) := by
  have h := pbcScalarLocalization_naturality l E F i T f
  rw [Category.comp_id, Category.id_comp] at h
  exact h.symm

theorem pbcRationalization_map_homMk_eqToHom {a b : E →ₐ[Padic l] F} (hab : a = b)
    (K : PbcRationalDerivedCategory l E T dim.out inv.out) :
    ((pbcRationalization T (pbcIntegralDatum l F) (pbcUniformizer l F)).map
        (ObjectProperty.homMk (eqToHom (congrArg
          (fun a ↦ (pbcEmbeddingAmbientTensor l E F a T).obj K.obj.obj) hab))) :
      (pbcRationalScalarExtension l E F a T dim.out inv.out).obj K ⟶
        (pbcRationalScalarExtension l E F b T dim.out inv.out).obj K) =
      eqToHom (congrArg (fun a ↦ (pbcRationalScalarExtension l E F a T dim.out inv.out).obj K)
        hab) := by
  subst hab
  erw [eqToHom_refl, eqToHom_refl]
  exact (pbcRationalization T (pbcIntegralDatum l F) (pbcUniformizer l F)).map_id _

theorem pbcAmbientScalarComp_id_right_integral (i : E →ₐ[Padic l] F)
    (η : pbcEmbeddingAmbientTensor l F F (AlgHom.id (Padic l) F) T ⟶ 𝟭 _)
    (hη : ∀ X : PbcCompletedDerived T (pbcIntegralDatum l E),
      (pbcAmbientScalarComp l E F F i (AlgHom.id (Padic l) F) T).hom.app X =
        η.app ((pbcEmbeddingAmbientTensor l E F i T).obj X) ≫
          eqToHom (congrArg (fun a ↦ (pbcEmbeddingAmbientTensor l E F a T).obj X)
            (AlgHom.id_comp i).symm))
    (K : PbcRationalDerivedCategory l E T dim.out inv.out) :
    (pbcAmbientScalarComp l E F F i (AlgHom.id (Padic l) F) T).hom.app K.obj.obj =
      η.app ((pbcRationalScalarExtension l E F i T dim.out inv.out).obj K).obj.obj ≫
        eqToHom (congrArg (fun a ↦ (pbcEmbeddingAmbientTensor l E F a T).obj K.obj.obj)
          (AlgHom.id_comp i).symm) :=
  hη K.obj.obj

end Fields

section NestedFields
attribute [local irreducible] pbcRationalScalarHom
variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
variable (T : Scheme.{u}) [IsNoetherian T]
variable [dim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ n)]
variable [inv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- The actual finite subfields, in a common ambient field; no algebraic closure
hypothesis is needed for this finite tower. Source: blueprint order 1307
(blueprint: lem-pbc-scalar-stage-coherence). -/
abbrev pbcCoefficientStage (E : Padic.FiniteCoefficientFields l Ω) :=
  PbcRationalDerivedCategory l E.val T dim.out inv.out

/-- A nested finite subfield inclusion, with its actual algebra homomorphism.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
def pbcSubfieldInclusion {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    E.val →ₐ[Padic l] F.val := IntermediateField.inclusion h

/-- Identity inclusions are the actual algebra identity.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence).
Proof: both maps fix every element of the subfield. -/
theorem pbcSubfieldInclusion_id (E : Padic.FiniteCoefficientFields l Ω) :
    pbcSubfieldInclusion l Ω (le_refl E) = AlgHom.id (Padic l) E.val := by
  rfl

/-- Actual inclusions compose as direct inclusions.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence).
Proof: both maps send each subfield element to its same ambient scalar. -/
theorem pbcSubfieldInclusion_comp {E F G : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (h' : F ≤ G) :
    (pbcSubfieldInclusion l Ω h').comp (pbcSubfieldInclusion l Ω h) =
      pbcSubfieldInclusion l Ω (h.trans h') := by
  rfl

/-- The actual rational tensor before literal identity normalization.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
abbrev pbcStageRaw {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcCoefficientStage l Ω T E ⥤ pbcCoefficientStage l Ω T F :=
  pbcRationalScalarExtension l E.val F.val (pbcSubfieldInclusion l Ω h) T dim.out inv.out

/-- Equal coefficient fields use the literal identity functor.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
def pbcStageTransition {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcCoefficientStage l Ω T E ⥤ pbcCoefficientStage l Ω T F := by
  classical
  exact if e : E = F then e ▸ 𝟭 (pbcCoefficientStage l Ω T E)
    else pbcStageRaw l Ω T h

/-- Normalization uses precisely the ordinary tensor multiplication unit.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
@[irreducible] def pbcStageNormalization {E F : Padic.FiniteCoefficientFields l Ω} (h : E ≤ F) :
    pbcStageRaw l Ω T h ≅ pbcStageTransition l Ω T h := by
  classical
  by_cases e : E = F
  · subst F
    exact eqToIso (congrArg
      (fun i ↦ pbcRationalScalarExtension l E.val E.val i T dim.out inv.out)
      (pbcSubfieldInclusion_id l Ω E)) ≪≫
        pbcRationalScalarUnit l E.val T dim.out inv.out ≪≫
          eqToIso (by unfold pbcStageTransition; rw [dite_eq_left rfl])
  · exact eqToIso (by simp only [pbcStageTransition, dite_eq_right e])

/-- Balancing, conjugated by the specified tensor units, is the chosen associator.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
@[irreducible] def pbcStageAssociator {E F G : Padic.FiniteCoefficientFields l Ω}
    (h : E ≤ F) (h' : F ≤ G) :
    pbcStageTransition l Ω T h ⋙ pbcStageTransition l Ω T h' ≅
      pbcStageTransition l Ω T (h.trans h') :=
  isoWhiskerRight (pbcStageNormalization l Ω T h).symm _ ≪≫
    isoWhiskerLeft _ (pbcStageNormalization l Ω T h').symm ≪≫
    pbcRationalScalarComp l E.val F.val G.val
      (pbcSubfieldInclusion l Ω h) (pbcSubfieldInclusion l Ω h') T dim.out inv.out ≪≫
    eqToIso (congrArg (fun i ↦ pbcRationalScalarExtension l E.val G.val i T dim.out inv.out)
      (pbcSubfieldInclusion_comp l Ω h h')) ≪≫
    pbcStageNormalization l Ω T (h.trans h')

/-- Equal coefficient fields use the identity transition.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
theorem pbcStageTransition_refl (E : Padic.FiniteCoefficientFields l Ω) :
    pbcStageTransition l Ω T (le_refl E) = 𝟭 _ := by
  unfold pbcStageTransition
  rw [dite_eq_left rfl]

/-- The normalization at equal fields is the tensor unit.
Source: blueprint order 1307 (blueprint: lem-pbc-scalar-stage-coherence). -/
theorem pbcStageNormalization_refl (E : Padic.FiniteCoefficientFields l Ω) :
    pbcStageNormalization l Ω T (le_refl E) =
      pbcRationalScalarUnit l E.val T dim.out inv.out ≪≫
        eqToIso (pbcStageTransition_refl l Ω T E).symm := by
  rw [pbcStageNormalization, dite_eq_left rfl]
  exact Iso.refl_trans _

end NestedFields
end AlgebraicGeometry.Scheme
