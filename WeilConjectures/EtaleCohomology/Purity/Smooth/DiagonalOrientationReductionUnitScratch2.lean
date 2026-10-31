module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionUnitScratch

universe u

open CategoryTheory Limits

namespace CategoryTheory.Functor

variable {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] [Abelian C₁] [Abelian C₂]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂] (F : C₂ ⥤ C₁) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

lemma g1 {A : C₁} {B : C₂} (g : A ⟶ F.obj B) :
    ((DerivedCategory.singleFunctorIsoCompQ C₁ 0).app A ≪≫
        (DerivedCategory.quotientCompQhIso C₁).symm.app _).inv ≫
      (DerivedCategory.singleFunctor C₁ 0).map g ≫ (F.mapDerivedCategorySingleFunctor 0).inv.app B ≫
      F.mapDerivedCategory.map (((DerivedCategory.singleFunctorIsoCompQ C₂ 0).app B ≪≫
        (DerivedCategory.quotientCompQhIso C₂).symm.app _).hom) ≫
      F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((HomologicalComplex.single _ (.up ℤ) 0).obj B)) =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
      ((HomologicalComplex.single _ (.up ℤ) 0).map g ≫
        (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).inv.app B)) := by
  have h₁ (K : CochainComplex C₁ ℤ) : (DerivedCategory.quotientCompQhIso C₁).hom.app K = 𝟙 _ := rfl
  have h₂ (K : CochainComplex C₁ ℤ) : (DerivedCategory.quotientCompQhIso C₁).inv.app K = 𝟙 _ := rfl
  have h₃ (K : CochainComplex C₂ ℤ) : (DerivedCategory.quotientCompQhIso C₂).hom.app K = 𝟙 _ := rfl
  have h₄ (K : CochainComplex C₂ ℤ) : (DerivedCategory.quotientCompQhIso C₂).inv.app K = 𝟙 _ := rfl
  have h₅ (K : CochainComplex C₂ ℤ) : (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app K = 𝟙 _ := rfl
  rw [mapDerivedCategoryFactorsh_hom_app]
  simp only [DerivedCategory.singleFunctorIsoCompQ, Iso.trans_inv, Iso.trans_hom, Iso.symm_inv,
    Iso.symm_hom, Iso.app_inv, Iso.app_hom, Iso.refl_inv, Iso.refl_hom,
    NatTrans.id_app, h₁, h₂, h₃, h₄, h₅, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp, CategoryTheory.Functor.map_id,
    Category.comp_id]
  erw [mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app]
  rw [Functor.map_comp, Functor.map_comp]
  rfl

end CategoryTheory.Functor

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace AlgebraicGeometry.Etale

open MonoidalCategory Functor.LaxMonoidal

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') (X : Scheme.{u})

set_option profiler true in
lemma hεq :
    ε (HomotopyCategory.quotient (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ)) =
      𝟙 _ := rfl

set_option profiler true in
lemma c1 (g : 𝟙_ _ ⟶
      (Sheaf.restrictScalars X.smallEtaleTopology ρ).obj
        (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')))) :
    (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X).inv ≫
        (DerivedCategory.singleFunctor _ 0).map g ≫
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app
          _ ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
          (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ') X).hom ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (ε DerivedCategory.Qh) ≫
        (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.hom.app (𝟙_ _) =
      ε DerivedCategory.Qh ≫ DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((HomologicalComplex.single _ (.up ℤ) 0).map g ≫
          (HomologicalComplex.singleMapHomologicalComplex
            (Sheaf.restrictScalars X.smallEtaleTopology ρ) (.up ℤ) 0).inv.app (𝟙_ _))) := by
  have e1 : (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X).inv = ε DerivedCategory.Qh ≫
      DerivedCategory.Qh.map (Functor.Monoidal.εIso (HomotopyCategory.quotient
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ))).hom ≫
      (singleFunctorObjIsoQh (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))).inv := by
    simp [singleFunctorObjUnitIso]
  have e2 : (singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ') X).hom ≫ ε DerivedCategory.Qh =
      (singleFunctorObjIsoQh (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')))).hom ≫
      DerivedCategory.Qh.map (Functor.Monoidal.εIso (HomotopyCategory.quotient
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) (.up ℤ))).inv := by
    simp [singleFunctorObjUnitIso]
  have hε'' : (Functor.Monoidal.εIso (HomotopyCategory.quotient
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ))).hom = 𝟙 _ := rfl
  have hη'' : (Functor.Monoidal.εIso (HomotopyCategory.quotient
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) (.up ℤ))).inv = 𝟙 _ := rfl
  have hn := (Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategoryFactorsh.hom.naturality
    (Functor.Monoidal.εIso (HomotopyCategory.quotient
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) (.up ℤ))).inv
  simp only [Functor.comp_map] at hn
  rw [e1, ← Functor.map_comp_assoc (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ) _ (ε _), e2,
    Functor.map_comp_assoc, hn]
  simp only [Category.assoc]
  erw [reassoc_of% (g1' ρ X g)]
  trace_state
  sorry

end AlgebraicGeometry.Etale
