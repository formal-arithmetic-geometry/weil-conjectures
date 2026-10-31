/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MateCounit
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalOfIso
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReduction
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionMonoidalSheaf
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CounitFac

/-!
# The commutation of the reduction of coefficients with the derived pullback is monoidal

Let `ρ : Λ →+* Λ'` be a surjective morphism of commutative rings with principal kernel and `Ψ`
the derived extension of scalars (`AlgebraicGeometry.Etale.derivedExtendScalars`). For a morphism
of schemes `e : U ⟶ X`, the commutation `Le^* ⋙ Ψ_U ≅ Ψ_X ⋙ Le^*`
(`AlgebraicGeometry.Etale.derivedExtendScalarsPullbackIso`), defined as a mate, is, through the
counits of the left derived functors, the underived commutation of the extension of scalars of
étale sheaves with the pullback (`AlgebraicGeometry.Etale.extendScalarsUpperStarIso`)
(`AlgebraicGeometry.Etale.derivedExtendScalarsPullbackMap_eq`). As the latter is monoidal, so is
the former: it is compatible with the tensor comparisons of `Ψ` and of the derived pullbacks
(`AlgebraicGeometry.Etale.derivedExtendScalarsPullbackMap_app_tensor_comp_δ`) and with the unit
comparisons (`AlgebraicGeometry.Etale.derivedExtendScalarsPullbackMap_app_unit_comp_η`).
-/

@[expose] public section



universe u

open CategoryTheory Limits MonoidalCategory

-- the instances used in the definitions of the derived tensor products, as in
-- `WeilConjectures.SixFunctors.Etale.Derived.ReductionHom`
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

open scoped CategoryTheory.Functor

namespace CategoryTheory


variable {A₁ A₂ B₁ B₂ : Type*} [Category* A₁] [Category* A₂] [Category* B₁] [Category* B₂]
  [Abelian A₁] [Abelian A₂] [Abelian B₁] [Abelian B₂]
  [HasDerivedCategory A₁] [HasDerivedCategory A₂] [HasDerivedCategory B₁] [HasDerivedCategory B₂]
  {R₁ : A₁ ⥤ B₁} {R₂ : A₂ ⥤ B₂} {G : B₁ ⥤ B₂} {H : A₁ ⥤ A₂}
  [R₁.Additive] [PreservesFiniteLimits R₁] [PreservesFiniteColimits R₁]
  [R₂.Additive] [PreservesFiniteLimits R₂] [PreservesFiniteColimits R₂]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  {LG : DerivedCategory B₁ ⥤ DerivedCategory B₂} {LH : DerivedCategory A₁ ⥤ DerivedCategory A₂}

namespace Adjunction

variable [(HomotopyCategory.quotient A₁ (.up ℤ)).IsLocalization
    (HomologicalComplex.homotopyEquivalences A₁ (.up ℤ))]
  [(HomotopyCategory.quotient A₂ (.up ℤ)).IsLocalization
    (HomologicalComplex.homotopyEquivalences A₂ (.up ℤ))]
  [(HomotopyCategory.quotient B₁ (.up ℤ)).IsLocalization
    (HomologicalComplex.homotopyEquivalences B₁ (.up ℤ))]
  [(HomotopyCategory.quotient B₂ (.up ℤ)).IsLocalization
    (HomologicalComplex.homotopyEquivalences B₂ (.up ℤ))]
  {E₁ : B₁ ⥤ A₁} {E₂ : B₂ ⥤ A₂} [E₁.Additive] [E₂.Additive]
  {LE₁ : DerivedCategory B₁ ⥤ DerivedCategory A₁} {LE₂ : DerivedCategory B₂ ⥤ DerivedCategory A₂}

/-- Mates of derived functors (for a natural transformation `T`, not necessarily an
isomorphism): the mate, along derived adjunctions `LE₁ ⊣ D(R₁)` and
`LE₂ ⊣ D(R₂)` whose counits are induced by those of `adj₁ : E₁ ⊣ R₁` and `adj₂ : E₂ ⊣ R₂`, of
an isomorphism `LE₁ ⋙ LH ≅ LG ⋙ LE₂` induced by `β : E₁ ⋙ H ≅ G ⋙ E₂` is the isomorphism
`D(R₁) ⋙ LG ≅ LH ⋙ D(R₂)` induced by the mate `e : R₁ ⋙ G ≅ H ⋙ R₂` of `β.inv`. -/
theorem mateEquiv_leftDerived_eq_of_counit (adj₁ : E₁ ⊣ R₁) (adj₂ : E₂ ⊣ R₂)
    (β : E₁ ⋙ H ≅ G ⋙ E₂) (e : R₁ ⋙ G ≅ H ⋙ R₂) (he : mateEquiv adj₁ adj₂ β.inv = e.hom)
    (βh : E₁.mapHomotopyCategory (.up ℤ) ⋙ H.mapHomotopyCategory (.up ℤ) ≅
      G.mapHomotopyCategory (.up ℤ) ⋙ E₂.mapHomotopyCategory (.up ℤ))
    (hβh : βh.inv = ((Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ E₂)) (.up ℤ)).hom ≫
      NatTrans.mapHomotopyCategory β.inv (.up ℤ)) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (E₁ ⋙ H)) (.up ℤ)).inv)
    (cE₁ : DerivedCategory.Qh ⋙ LE₁ ⟶ E₁.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cE₂ : DerivedCategory.Qh ⋙ LE₂ ⟶ E₂.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (cG : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ιG : LG ≅ G.mapDerivedCategory)
    (hιG : ∀ K, ιG.hom.app (DerivedCategory.Qh.obj K) ≫ G.mapDerivedCategoryFactorsh.hom.app K =
      cG.app K)
    (cH : DerivedCategory.Qh ⋙ LH ⟶ H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (ιH : LH ≅ H.mapDerivedCategory)
    (hιH : ∀ K, ιH.hom.app (DerivedCategory.Qh.obj K) ≫ H.mapDerivedCategoryFactorsh.hom.app K =
      cH.app K)
    (dadj₁ : LE₁ ⊣ R₁.mapDerivedCategory) (dadj₂ : LE₂ ⊣ R₂.mapDerivedCategory)
    (hε₁ : ∀ K, dadj₁.counit.app (DerivedCategory.Qh.obj K) =
      LE₁.map (R₁.mapDerivedCategoryFactorsh.hom.app K) ≫
        cE₁.app ((R₁.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((adj₁.mapHomotopyCategory (.up ℤ)).counit.app K))
    (hε₂ : ∀ K, dadj₂.counit.app (DerivedCategory.Qh.obj K) =
      LE₂.map (R₂.mapDerivedCategoryFactorsh.hom.app K) ≫
        cE₂.app ((R₂.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((adj₂.mapHomotopyCategory (.up ℤ)).counit.app K))
    (T : LG ⋙ LE₂ ⟶ LE₁ ⋙ LH)
    (κ₁ : DerivedCategory.Qh ⋙ LE₁ ⋙ LH ⟶
      E₁.mapHomotopyCategory (.up ℤ) ⋙ H.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hκ₁ : κ₁ = Functor.whiskerRight cE₁ LH ≫
      Functor.whiskerLeft (E₁.mapHomotopyCategory (.up ℤ)) cH)
    (κ₂ : DerivedCategory.Qh ⋙ LG ⋙ LE₂ ⟶
      G.mapHomotopyCategory (.up ℤ) ⋙ E₂.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh)
    (hκ₂ : κ₂ = Functor.whiskerRight cG LE₂ ≫
      Functor.whiskerLeft (G.mapHomotopyCategory (.up ℤ)) cE₂)
    (hT : ∀ K, T.app (DerivedCategory.Qh.obj K) ≫ κ₁.app K =
      κ₂.app K ≫ DerivedCategory.Qh.map (βh.inv.app K))
    (Γ : R₁.mapDerivedCategory ⋙ LG ≅ LH ⋙ R₂.mapDerivedCategory)
    (hΓ : Γ = Functor.isoWhiskerLeft R₁.mapDerivedCategory ιG ≪≫
      Functor.mapDerivedCategorySquareIso e ≪≫
        Functor.isoWhiskerRight ιH.symm R₂.mapDerivedCategory) :
    mateEquiv dadj₁ dadj₂ T = Γ.hom := by
  subst hκ₁ hκ₂
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso A₁ (.up ℤ))
  intro K
  apply (dadj₂.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  have : IsIso (cH.app K) := by
    rw [← hιH]
    infer_instance
  rw [← cancel_mono (cH.app K)]
  have hm := mateEquiv_counit dadj₁ dadj₂ T (DerivedCategory.Qh.obj K)
  have hΓK := Functor.mapDerivedCategorySquareIso_hom_app_Qh_obj_comp_counit cG ιG hιG cH ιH hιH
    e Γ hΓ K
  have hH := mapHomotopyCategory_map_comp_counit_app (.up ℤ) adj₁ adj₂ β e.hom he βh hβh K
  have hκ := cE₂.naturality
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).hom.app K ≫
      (NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).inv.app K)
  have hβ := T.naturality (R₁.mapDerivedCategoryFactorsh.hom.app K)
  have hl := cH.naturality ((adj₁.mapHomotopyCategory (.up ℤ)).counit.app K)
  have hB := hT ((R₁.mapHomotopyCategory (.up ℤ)).obj K)
  rw [hm]
  simp only [Category.assoc]
  erw [← dadj₂.counit_naturality (cH.app K)]
  rw [hε₁]
  erw [hε₂ ((H.mapHomotopyCategory (.up ℤ)).obj K)]
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc] at hB
  dsimp at hκ hβ hl
  simp only [← Functor.map_comp_assoc]
  rw [hΓK]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hβ, cancel_epi]
  simp only [Functor.map_comp, Category.assoc] at hκ
  rw [hl, reassoc_of% hB, reassoc_of% hκ]
  have hH' := congrArg DerivedCategory.Qh.map hH
  simp only [Functor.map_comp, Category.assoc] at hH' ⊢
  rw [hH']

end Adjunction

end CategoryTheory

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

/-- Preserving quasi-isomorphisms between K-flat complexes is invariant under isomorphism of
functors. -/
lemma preservesKFlatQuasiIso_of_iso {F G : C ⥤ D} [F.Additive] [G.Additive] (e : F ≅ G)
    [F.PreservesKFlatQuasiIso] : G.PreservesKFlatQuasiIso where
  quasiIso_map hK hL f _ := by
    have := F.quasiIso_mapHomologicalComplex_map_of_kFlat hK hL f
    exact (quasiIso_iff_of_arrow_mk_iso _ _
      (Arrow.isoOfNatIso (NatIso.mapHomologicalComplex e (.up ℤ)) (Arrow.mk f))).1 this

end CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})

section Monoidal

variable (X : Scheme.{u})

/-- The derived extension of scalars of the unit, `Ψ Λ_X ≅ Λ'_X`: the unit comparison of the
monoidal structure `CategoryTheory.Functor.leftDerivedFunctorMonoidal` of the left derived
functor of the strong monoidal extension of scalars of étale sheaves. -/
noncomputable def derivedExtendScalarsUnitIso :
    (derivedExtendScalars hρ ha X).obj (𝟙_ _) ≅ 𝟙_ _ :=
  haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
  letI := (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorMonoidal
  (Functor.Monoidal.εIso (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctor).symm

lemma derivedExtendScalarsUnitIso_hom :
    haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
    letI := (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorMonoidal
    (derivedExtendScalarsUnitIso hρ ha X).hom =
      Functor.OplaxMonoidal.η (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctor :=
  rfl

lemma leftDerivedFunctor_extendScalars_δ (K M : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    haveI := preservesKFlatQuasiIso_extendScalars hρ ha X
    letI := (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorMonoidal
    Functor.OplaxMonoidal.δ (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctor K M =
      (((Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedTensorComparison.app K).app M) :=
  have := preservesKFlatQuasiIso_extendScalars hρ ha X
  Functor.leftDerivedFunctorMonoidal_δ _ K M

end Monoidal


section Counit

variable (X : Scheme.{u})

/-- The counit of the derived adjunction `Ψ ⊣ Res` on the image of a complex `M` is the levelwise
counit, read through the counit of `Ψ`. -/
lemma derivedExtendScalarsAdjunction_counit_app_Qh
    (M : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) (.up ℤ)) :
    (derivedExtendScalarsAdjunction hρ ha X).counit.app (DerivedCategory.Qh.obj M) =
      (derivedExtendScalars hρ ha X).map
          ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.hom.app M) ≫
        (derivedExtendScalarsCounit hρ ha X).app
          (((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).obj M) ≫
        DerivedCategory.Qh.map (((Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).mapHomotopyCategory
          (.up ℤ)).counit.app M) := by
  have := preservesKFlatQuasiIso_extendScalars hρ ha X
  have h₁ := (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)
    |>.derivedε_fac_app (HomotopyCategory.quasiIso _ (.up ℤ))
      (Sheaf.extendScalars X.smallEtaleTopology ρ).leftDerivedFunctorCounit
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).rightDerivedFunctorUnit M
  have h₃ := NatTrans.congr_app
    (Sheaf.restrictScalars X.smallEtaleTopology ρ).rightDerivedFunctorIsoMapDerivedCategory_hom_fac M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₃
  delta derivedExtendScalarsAdjunction derivedExtendScalars derivedExtendScalarsCounit
  dsimp only
  simp only [Adjunction.derivedAdjunction, Adjunction.ofNatIsoRight_counit, NatTrans.comp_app]
  rw [Functor.whiskerRight_app, Adjunction.derived_counit]
  have hu : (Sheaf.restrictScalars X.smallEtaleTopology ρ).rightDerivedFunctorUnit.app M =
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.inv.app M ≫
        (Sheaf.restrictScalars X.smallEtaleTopology ρ).rightDerivedFunctorIsoMapDerivedCategory.inv.app
          (DerivedCategory.Qh.obj M) := by
    rw [← h₃, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  rw [hu, Functor.map_comp, Category.assoc] at h₁
  rw [← h₁, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

end Counit

section PullbackCounit

variable {U X : Scheme.{u}} (e : U ⟶ X)

/-- The counit `Qh ⋙ Ψ_X ⋙ Le^* ⟶ F_X ⋙ e^* ⋙ Qh` of the composite of the derived extension of
scalars with the derived pullback. -/
noncomputable abbrev derivedExtendScalarsUpperStarCounit :
    DerivedCategory.Qh ⋙ derivedExtendScalars hρ ha X ⋙ L((e)^*[ModuleCat.{u + 1} Λ']) ⟶
      (Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ) ⋙
        ((e)^*[ModuleCat.{u + 1} Λ']).mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh :=
  Functor.whiskerRight (derivedExtendScalarsCounit hρ ha X) L((e)^*[ModuleCat.{u + 1} Λ']) ≫
    Functor.whiskerLeft ((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ))
      ((e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctorCounit

/-- The counit `Qh ⋙ Le^* ⋙ Ψ_U ⟶ e^* ⋙ F_U ⋙ Qh` of the composite of the derived pullback with
the derived extension of scalars. -/
noncomputable abbrev upperStarDerivedExtendScalarsCounit :
    DerivedCategory.Qh ⋙ L((e)^*[ModuleCat.{u + 1} Λ]) ⋙ derivedExtendScalars hρ ha U ⟶
      ((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (.up ℤ) ⋙
        (Sheaf.extendScalars U.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh :=
  Functor.whiskerRight ((e)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctorCounit
      (derivedExtendScalars hρ ha U) ≫
    Functor.whiskerLeft (((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (.up ℤ))
      (derivedExtendScalarsCounit hρ ha U)

/-- `Ψ_X ⋙ Le^*` is a left derived functor of `F_X ⋙ e^*`: on a K-flat complex, both counits
are isomorphisms. -/
instance isLeftDerivedFunctor_derivedExtendScalarsUpperStarCounit :
    (derivedExtendScalars hρ ha X ⋙ L((e)^*[ModuleCat.{u + 1} Λ'])).IsLeftDerivedFunctor
      (derivedExtendScalarsUpperStarCounit hρ ha e) (HomotopyCategory.quasiIso _ (.up ℤ)) := by
  refine LocalizerMorphism.isLeftDerivedFunctor_of_isLeftDerivabilityStructure
    (HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat _ ?_
  rintro ⟨K, hK⟩
  have := preservesKFlatQuasiIso_extendScalars hρ ha X
  have h₁ : IsIso ((derivedExtendScalarsCounit hρ ha X).app
      ((HomotopyCategory.quasiIso _ (.up ℤ)).localizerMorphismKFlat.functor.obj ⟨K, hK⟩)) :=
    (Sheaf.extendScalars X.smallEtaleTopology ρ).isIso_leftDerivedFunctorCounit_app_of_kFlat' K hK
  have h₂ : IsIso (((e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctorCounit.app
      (((Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ)).obj K)) :=
    inferInstance
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _) h₂


variable (ρ) in
/-- The isomorphism `F_X ⋙ e^* ≅ e^* ⋙ F_U` on homotopy categories. -/
noncomputable def extendScalarsUpperStarHomotopyIso :
    (Sheaf.extendScalars X.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ) ⋙
        ((e)^*[ModuleCat.{u + 1} Λ']).mapHomotopyCategory (.up ℤ) ≅
      ((e)^*[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (.up ℤ) ⋙
        (Sheaf.extendScalars U.smallEtaleTopology ρ).mapHomotopyCategory (.up ℤ) :=
  Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ) ≪≫
    { hom := NatTrans.mapHomotopyCategory (extendScalarsUpperStarIso ρ e).hom (.up ℤ)
      inv := NatTrans.mapHomotopyCategory (extendScalarsUpperStarIso ρ e).inv (.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id, NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id, NatTrans.mapHomotopyCategory_id] } ≪≫
    (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (.up ℤ)).symm

/-- The comparison `Le^* ⋙ Ψ_U ⟶ Ψ_X ⋙ Le^*` of left derived functors induced by the
underived commutation `F_X ⋙ e^* ≅ e^* ⋙ F_U`, through the counits. -/
noncomputable def derivedExtendScalarsPullbackOfCounit :
    L((e)^*[ModuleCat.{u + 1} Λ]) ⋙ derivedExtendScalars hρ ha U ⟶
      derivedExtendScalars hρ ha X ⋙ L((e)^*[ModuleCat.{u + 1} Λ']) :=
  Functor.leftDerivedNatTrans _ _ (upperStarDerivedExtendScalarsCounit hρ ha e)
    (derivedExtendScalarsUpperStarCounit hρ ha e) (HomotopyCategory.quasiIso _ (.up ℤ))
    (Functor.whiskerRight (extendScalarsUpperStarHomotopyIso ρ e).inv DerivedCategory.Qh)

/-- The comparison `Le^* ⋙ Ψ_U ⟶ Ψ_X ⋙ Le^*` is induced, through the counits, by the
underived commutation. -/
@[reassoc]
lemma derivedExtendScalarsPullbackOfCounit_app_Qh
    (K : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ)) :
    (derivedExtendScalarsPullbackOfCounit hρ ha e).app (DerivedCategory.Qh.obj K) ≫
        (derivedExtendScalarsUpperStarCounit hρ ha e).app K =
      (upperStarDerivedExtendScalarsCounit hρ ha e).app K ≫
        DerivedCategory.Qh.map ((extendScalarsUpperStarHomotopyIso ρ e).inv.app K) :=
  Functor.leftDerivedNatTrans_app _ _ _ _ (HomotopyCategory.quasiIso _ (.up ℤ)) _ K

/-- **The commutation of `Ψ` with the derived pullbacks through the counits**: the mate
`derivedExtendScalarsPullbackMap` of `Res ⋙ Le^* ≅ Le^* ⋙ Res` is the comparison of left
derived functors induced by the underived commutation `F_X ⋙ e^* ≅ e^* ⋙ F_U`. -/
theorem derivedExtendScalarsPullbackMap_eq :
    derivedExtendScalarsPullbackMap hρ ha e = derivedExtendScalarsPullbackOfCounit hρ ha e := by
  have h := Adjunction.mateEquiv_leftDerived_eq_of_counit
    (Sheaf.extendScalarsAdjunction X.smallEtaleTopology ρ)
    (Sheaf.extendScalarsAdjunction U.smallEtaleTopology ρ)
    (extendScalarsUpperStarIso ρ e) (upperStarRestrictScalarsIso ρ e)
    (mateEquiv_extendScalarsUpperStarIso_inv ρ e) (extendScalarsUpperStarHomotopyIso ρ e)
    (by simp [extendScalarsUpperStarHomotopyIso])
    (derivedExtendScalarsCounit hρ ha X) (derivedExtendScalarsCounit hρ ha U)
    ((e)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctorCounit
    (leftDerivedUpperStarIsoMapDerivedCategory _ e)
    ((e)^*[ModuleCat.{u + 1} Λ]).leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac
    ((e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctorCounit
    (leftDerivedUpperStarIsoMapDerivedCategory _ e)
    ((e)^*[ModuleCat.{u + 1} Λ']).leftDerivedFunctorIsoMapDerivedCategory_hom_app_fac
    (derivedExtendScalarsAdjunction hρ ha X) (derivedExtendScalarsAdjunction hρ ha U)
    (derivedExtendScalarsAdjunction_counit_app_Qh hρ ha X)
    (derivedExtendScalarsAdjunction_counit_app_Qh hρ ha U)
    (derivedExtendScalarsPullbackOfCounit hρ ha e) _ rfl _ rfl
    (derivedExtendScalarsPullbackOfCounit_app_Qh hρ ha e)
    (leftDerivedUpperStarRestrictScalarsIso ρ e) rfl
  rw [derivedExtendScalarsPullbackMap, ← h, Equiv.symm_apply_apply]

end PullbackCounit

end AlgebraicGeometry.Etale
