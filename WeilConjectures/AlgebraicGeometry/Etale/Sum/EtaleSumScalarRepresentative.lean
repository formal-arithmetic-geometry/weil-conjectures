/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumCoefficientComputation
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-! # Derived normalization of the sheetwise scalar comparison

Source: Stacks Project, Tags 06YY, 03S5 and 0GL6
(blueprint: lem-sp-etale-sum-scalar-representative).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
private theorem cachedEtaleGroth (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) :=
  inferInstance
private theorem cachedEtaleSheafify (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasSheafify X.smallEtaleTopology (ModuleCat.{u + 1} A) :=
  inferInstance
private theorem cachedEtaleMonoidalPreadditive (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : MonoidalPreadditive (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleCoproducts (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasCountableCoproducts (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleColimits (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasColimitsOfShape ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleFlatResolution (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : Abelian.HasFunctorialFlatResolution (Sheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleInjectiveResolution (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : Abelian.HasKInjectiveResolutions (Sheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleExactColimits (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : HasExactColimitsOfShape ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A)) := inferInstance
private theorem cachedEtaleTensor4 (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))),
    GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄ := inferInstance
private theorem cachedEtaleTensor12 (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))),
    GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃ := inferInstance
private theorem cachedEtaleTensor23 (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (X₁ X₂ X₃ : GradedObject ℤ (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} A))),
    GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃ := inferInstance
private theorem cachedEtaleTensorColimits (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (V : (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
    PreservesColimitsOfShape ℤ ((CategoryTheory.MonoidalCategory.curriedTensor (Sheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} A))).obj V) :=
  inferInstance
private theorem cachedEtaleTensorFlipColimits (A : Type (u + 1)) [CommRing A]
    (X : AlgebraicGeometry.Scheme.{u}) : ∀ (V : (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))),
    PreservesColimitsOfShape ℤ ((CategoryTheory.MonoidalCategory.curriedTensor (Sheaf
      X.smallEtaleTopology (ModuleCat.{u + 1} A))).flip.obj V) :=
  inferInstance

private def adjointComparison
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    (Q : C ⥤ A) (Q' : D ⥤ B) {F : C ⥤ D} {R : D ⥤ C}
    {L : A ⥤ B} {U : B ⥤ A} (adj : F ⊣ R) (ad : L ⊣ U)
    (r : R ⋙ Q ≅ Q' ⋙ U) (P : C) : L.obj (Q.obj P) ⟶ Q'.obj (F.obj P) :=
  (ad.homEquiv _ _).symm (Q.map (adj.unit.app P) ≫ r.hom.app (F.obj P))

private theorem adjointComparison_unit
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    (Q : C ⥤ A) (Q' : D ⥤ B) {F : C ⥤ D} {R : D ⥤ C}
    {L : A ⥤ B} {U : B ⥤ A} (adj : F ⊣ R) (ad : L ⊣ U)
    (r : R ⋙ Q ≅ Q' ⋙ U) (P : C) :
    ad.unit.app (Q.obj P) ≫ U.map (adjointComparison Q Q' adj ad r P) =
      Q.map (adj.unit.app P) ≫ r.hom.app (F.obj P) :=
  (ad.homEquiv _ _).apply_symm_apply _

private def compositeRightFactor
    {C D E A B T : Type*} [Category C] [Category D] [Category E]
    [Category A] [Category B] [Category T]
    {Q : C ⥤ A} {Q' : D ⥤ B} {Q'' : E ⥤ T}
    {R : D ⥤ C} {S : E ⥤ D} {U : B ⥤ A} {V : T ⥤ B}
    (r : R ⋙ Q ≅ Q' ⋙ U) (s : S ⋙ Q' ≅ Q'' ⋙ V) :
    (S ⋙ R) ⋙ Q ≅ Q'' ⋙ V ⋙ U :=
  Functor.associator S R Q ≪≫ Functor.isoWhiskerLeft S r ≪≫
    (Functor.associator S Q' U).symm ≪≫ Functor.isoWhiskerRight s U ≪≫
      Functor.associator Q'' V U

private theorem compositeRightFactor_hom
    {C D E A B T : Type*} [Category C] [Category D] [Category E]
    [Category A] [Category B] [Category T]
    {Q : C ⥤ A} {Q' : D ⥤ B} {Q'' : E ⥤ T}
    {R : D ⥤ C} {S : E ⥤ D} {U : B ⥤ A} {V : T ⥤ B}
    (r : R ⋙ Q ≅ Q' ⋙ U) (s : S ⋙ Q' ≅ Q'' ⋙ V) (Z : E) :
    (compositeRightFactor r s).hom.app Z = r.hom.app (S.obj Z) ≫ U.map (s.hom.app Z) := by
  simp only [compositeRightFactor, Iso.trans_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Iso.symm_hom, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp, Category.comp_id]

private theorem adjointComparison_comp
    {C D E A B T : Type*} [Category C] [Category D] [Category E]
    [Category A] [Category B] [Category T]
    (Q : C ⥤ A) (Q' : D ⥤ B) (Q'' : E ⥤ T)
    {F : C ⥤ D} {R : D ⥤ C} {G : D ⥤ E} {S : E ⥤ D}
    {L : A ⥤ B} {U : B ⥤ A} {M : B ⥤ T} {V : T ⥤ B}
    (adj : F ⊣ R) (adj' : G ⊣ S) (ad : L ⊣ U) (ad' : M ⊣ V)
    (r : R ⋙ Q ≅ Q' ⋙ U) (s : S ⋙ Q' ≅ Q'' ⋙ V)
    (t : (S ⋙ R) ⋙ Q ≅ Q'' ⋙ V ⋙ U)
    (ht : ∀ Z, t.hom.app Z = r.hom.app (S.obj Z) ≫ U.map (s.hom.app Z)) (P : C) :
    M.map (adjointComparison Q Q' adj ad r P) ≫
        adjointComparison Q' Q'' adj' ad' s (F.obj P) =
      adjointComparison Q Q'' (adj.comp adj') (ad.comp ad') t P := by
  apply ((ad.comp ad').homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit]
  rw [adjointComparison_unit]
  simp only [Adjunction.comp_unit_app, Functor.comp_map,
    Functor.map_comp, Category.assoc]
  rw [← U.map_comp_assoc]
  erw [← ad'.unit.naturality]
  simp only [Functor.id_map, U.map_comp, Category.assoc]
  rw [← Category.assoc, adjointComparison_unit]
  simp only [Category.assoc]
  rw [← U.map_comp, adjointComparison_unit, U.map_comp]
  erw [← r.hom.naturality_assoc]
  simp only [Functor.comp_map, Functor.comp_obj, ht]

private theorem adjointComparison_conjugate
    {C D A B : Type*} [Category C] [Category D] [Category A] [Category B]
    (Q : C ⥤ A) (Q' : D ⥤ B)
    {F G : C ⥤ D} {R S : D ⥤ C} {L M : A ⥤ B} {U V : B ⥤ A}
    (adj : F ⊣ R) (adj' : G ⊣ S) (ad : L ⊣ U) (ad' : M ⊣ V)
    (r : R ⋙ Q ≅ Q' ⋙ U) (s : S ⋙ Q ≅ Q' ⋙ V)
    (α : F ⟶ G) (β : S ⟶ R) (a : L ⟶ M) (b : V ⟶ U)
    (hα : ∀ P, adj.unit.app P ≫ R.map (α.app P) =
      adj'.unit.app P ≫ β.app (G.obj P))
    (ha : ∀ P, ad.unit.app P ≫ U.map (a.app P) =
      ad'.unit.app P ≫ b.app (M.obj P))
    (hr : ∀ Z, Q.map (β.app Z) ≫ r.hom.app Z =
      s.hom.app Z ≫ b.app (Q'.obj Z)) (P : C) :
    adjointComparison Q Q' adj ad r P ≫ Q'.map (α.app P) =
      a.app (Q.obj P) ≫ adjointComparison Q Q' adj' ad' s P := by
  apply (ad.homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  rw [← Category.assoc, adjointComparison_unit]
  rw [← Category.assoc, ha]
  simp only [Category.assoc]
  rw [← b.naturality]
  conv_rhs => rw [← Category.assoc, adjointComparison_unit]
  simp only [Category.assoc]
  erw [← r.hom.naturality]
  simp only [Functor.comp_map]
  rw [← Q.map_comp_assoc, hα, Q.map_comp, Category.assoc, hr]

private theorem complexUnit
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    {F : C ⥤ D} {R : D ⥤ C} [F.Additive] [R.Additive] (adj : F ⊣ R)
    (P : CochainComplex C ℤ) :
    (adj.mapHomologicalComplex (.up ℤ)).unit.app P =
      (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
        (NatTrans.mapHomologicalComplex adj.unit (.up ℤ)).app P ≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ R)) (.up ℤ)).inv.app P := by
  ext n
  simp only [Adjunction.mapHomologicalComplex_unit_app_f, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexIdIso_inv_app_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplexCompIso_inv_app_f, Iso.refl_inv, NatTrans.id_app,
    Functor.id_obj, Functor.comp_obj]
  change adj.unit.app (P.X n) = 𝟙 _ ≫ adj.unit.app (P.X n) ≫ 𝟙 _
  rw [Category.id_comp, Category.comp_id]

private theorem complexConjugateUnit
    {C D E T : Type*} [Category C] [Category D] [Category E] [Category T]
    [Preadditive C] [Preadditive D] [Preadditive E] [Preadditive T]
    {F : C ⥤ D} {R : D ⥤ C} {G : D ⥤ T} {S : T ⥤ D}
    {H : C ⥤ E} {U : E ⥤ C} {I : E ⥤ T} {V : T ⥤ E}
    [F.Additive] [R.Additive] [G.Additive] [S.Additive]
    [H.Additive] [U.Additive] [I.Additive] [V.Additive]
    (a : F ⊣ R) (b : G ⊣ S) (c : H ⊣ U) (d : I ⊣ V)
    (α : F ⋙ G ⟶ H ⋙ I) (β : V ⋙ U ⟶ S ⋙ R)
    (h : ∀ M, (a.comp b).unit.app M ≫ (S ⋙ R).map (α.app M) =
      (c.comp d).unit.app M ≫ β.app ((H ⋙ I).obj M)) (P : CochainComplex C ℤ) :
    ((a.mapHomologicalComplex (.up ℤ)).comp
        (b.mapHomologicalComplex (.up ℤ))).unit.app P ≫
      (S.mapHomologicalComplex (.up ℤ) ⋙ R.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex α (.up ℤ)).app P) =
    ((c.mapHomologicalComplex (.up ℤ)).comp
        (d.mapHomologicalComplex (.up ℤ))).unit.app P ≫
      (NatTrans.mapHomologicalComplex β (.up ℤ)).app
        ((H.mapHomologicalComplex (.up ℤ) ⋙ I.mapHomologicalComplex (.up ℤ)).obj P) := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact h (P.X n)

private theorem exactFactorh
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P : CochainComplex C ℤ) :
    F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj P) =
      F.mapDerivedCategoryFactors.hom.app P := by
  rw [Functor.mapDerivedCategoryFactorsh_hom_app]
  change F.mapDerivedCategory.map (𝟙 (DerivedCategory.Q.obj P)) ≫
    F.mapDerivedCategoryFactors.hom.app P ≫
      𝟙 (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
        DerivedCategory.Qh.map
          (𝟙 ((HomotopyCategory.quotient D (.up ℤ)).obj
            ((F.mapHomologicalComplex (.up ℤ)).obj P))) = _
  have hi : DerivedCategory.Qh.map
      (𝟙 ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj P))) =
      𝟙 (DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj P)) :=
    DerivedCategory.Qh.map_id _
  rw [hi, CategoryTheory.Functor.map_id]
  change 𝟙 _ ≫ F.mapDerivedCategoryFactors.hom.app P ≫ 𝟙 _ ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]

private theorem inverseSquare
    {C : Type*} [Category C] {A B D E : C}
    (p : A ≅ B) (q : D ≅ E) (f : A ⟶ D) (g : B ⟶ E)
    (h : f ≫ q.hom = p.hom ≫ g) : g ≫ q.inv = p.inv ≫ f := by
  apply (cancel_epi p.hom).1
  apply (cancel_mono q.hom).1
  simpa only [Category.assoc, Iso.inv_hom_id, Iso.hom_inv_id_assoc,
    Category.comp_id] using h.symm

private theorem exactSquareInverseFactors
    {C D E T : Type*} [Category C] [Category D] [Category E] [Category T]
    [Abelian C] [Abelian D] [Abelian E] [Abelian T]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory T]
    {F : C ⥤ D} {G : D ⥤ T} {H : C ⥤ E} {I : E ⥤ T}
    [F.Additive] [G.Additive] [H.Additive] [I.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    (e : F ⋙ G ≅ H ⋙ I) (P : CochainComplex C ℤ) :
    DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) ≫
        (compositeRightFactor I.mapDerivedCategoryFactors.symm
          H.mapDerivedCategoryFactors.symm).hom.app P =
      (compositeRightFactor G.mapDerivedCategoryFactors.symm
          F.mapDerivedCategoryFactors.symm).hom.app P ≫
        (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) := by
  have hs : (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P) ≫
      I.mapDerivedCategory.map (H.mapDerivedCategoryFactors.hom.app P) ≫
      I.mapDerivedCategoryFactors.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj P) =
    G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app P) ≫
      G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P) := by
    simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom,
      Iso.symm_hom, NatTrans.comp_app, Category.assoc]
    rw [Functor.mapDerivedCategoryCompIso_hom_app_factors,
      Functor.mapDerivedCategoryNatIso_fac]
    rw [← Functor.mapDerivedCategoryCompIso_hom_app_factors F G P]
    erw [Category.assoc, Iso.inv_hom_id_app_assoc]
    exact Category.assoc _ _ _
  rw [compositeRightFactor_hom, compositeRightFactor_hom]
  exact inverseSquare
    (G.mapDerivedCategory.mapIso (F.mapDerivedCategoryFactors.app P) ≪≫
      G.mapDerivedCategoryFactors.app ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (I.mapDerivedCategory.mapIso (H.mapDerivedCategoryFactors.app P) ≪≫
      I.mapDerivedCategoryFactors.app ((H.mapHomologicalComplex (.up ℤ)).obj P))
    ((Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Q.obj P))
    (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex e.hom (.up ℤ)).app P))
    (by simpa only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
      Category.assoc] using hs)

private theorem sumComparison
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).obj X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {F : C ⥤ D} {R : D ⥤ C} [F.Additive] [R.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (a : F ⊣ R) (P : CochainComplex C ℤ) :
    adjointComparison DerivedCategory.Q DerivedCategory.Q
      (a.mapHomologicalComplex (.up ℤ)) a.mapDerivedCategoryAdjunction
      R.mapDerivedCategoryFactors.symm P = F.mapDerivedCategoryFactors.hom.app P := by
  have h := a.mapDerivedCategoryAdjunction_unit_app_fac
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  rw [Adjunction.mapHomotopyCategory_unit_app_quotient] at h
  change a.mapDerivedCategoryAdjunction.unit.app (DerivedCategory.Q.obj P) ≫
    R.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj P)) ≫
    R.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj
      ((F.mapHomologicalComplex (.up ℤ)).obj P)) =
    DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app P) at h
  rw [exactFactorh, exactFactorh] at h
  apply (a.mapDerivedCategoryAdjunction.homEquiv _ _).injective
  dsimp only [adjointComparison]
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  rw [← h]
  dsimp only [Functor.comp_obj]
  simp only [Category.assoc, Iso.symm_hom, Iso.hom_inv_id_app]
  erw [Category.comp_id]

private theorem exactSumScalarComparison
    {C D E T : Type*} [Category C] [Category D] [Category E] [Category T]
    [Abelian C] [Abelian D] [Abelian E] [Abelian T]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory T]
    [Abelian.HasKInjectiveResolutions D] [Abelian.HasKInjectiveResolutions T]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).obj X)]
    [∀ (X : C), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C]
    [MonoidalCategory E] [MonoidalPreadditive E] [HasCountableCoproducts E]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ E), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ E), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ E), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ E] [HasExactColimitsOfShape ℤ E]
    [∀ (X : E), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor E).obj X)]
    [∀ (X : E), PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor E).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution E]
    {SA : C ⥤ D} {UA : D ⥤ C} {SB : E ⥤ T} {UB : T ⥤ E}
    {TX : C ⥤ E} {RX : E ⥤ C} {TY : D ⥤ T} {RY : T ⥤ D}
    [SA.Additive] [UA.Additive] [SB.Additive] [UB.Additive]
    [TX.Additive] [RX.Additive] [TY.Additive] [RY.Additive]
    [PreservesFiniteLimits SA] [PreservesFiniteColimits SA]
    [PreservesFiniteLimits SB] [PreservesFiniteColimits SB]
    [PreservesFiniteLimits UA] [PreservesFiniteColimits UA]
    [PreservesFiniteLimits UB] [PreservesFiniteColimits UB]
    [PreservesFiniteLimits RX] [PreservesFiniteColimits RX]
    [PreservesFiniteLimits RY] [PreservesFiniteColimits RY]
    (a : SA ⊣ UA) (b : SB ⊣ UB) (x : TX ⊣ RX) (y : TY ⊣ RY)
    {LX : DerivedCategory C ⥤ DerivedCategory E} {LY : DerivedCategory D ⥤ DerivedCategory T}
    (xd : LX ⊣ RX.mapDerivedCategory) (yd : LY ⊣ RY.mapDerivedCategory)
    (β : RY ⋙ UA ≅ UB ⋙ RX) (P : CochainComplex C ℤ) :
    let α := (a.comp y).leftAdjointUniq ((x.comp b).ofNatIsoRight β.symm)
    let σ := ((conjugateIsoEquiv (a.mapDerivedCategoryAdjunction.comp yd)
      (xd.comp b.mapDerivedCategoryAdjunction)).symm
        (Functor.mapDerivedCategorySquareIso β)).symm
    LY.map (SA.mapDerivedCategoryFactors.hom.app P) ≫
        (yd.homEquiv _ _).symm
          (DerivedCategory.Q.map
            ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app
                ((SA.mapHomologicalComplex (.up ℤ)).obj P) ≫
              (NatTrans.mapHomologicalComplex y.unit (.up ℤ)).app
                ((SA.mapHomologicalComplex (.up ℤ)).obj P) ≫
              (Functor.mapHomologicalComplexCompIso (Iso.refl (TY ⋙ RY)) (.up ℤ)).inv.app
                ((SA.mapHomologicalComplex (.up ℤ)).obj P)) ≫
            RY.mapDerivedCategoryFactors.inv.app
              ((TY.mapHomologicalComplex (.up ℤ)).obj
                ((SA.mapHomologicalComplex (.up ℤ)).obj P))) ≫
        DerivedCategory.Q.map
          (X := (TY.mapHomologicalComplex (.up ℤ)).obj
            ((SA.mapHomologicalComplex (.up ℤ)).obj P))
          (Y := (SB.mapHomologicalComplex (.up ℤ)).obj
            ((TX.mapHomologicalComplex (.up ℤ)).obj P))
          ((NatTrans.mapHomologicalComplex α.hom (.up ℤ)).app P) =
      σ.hom.app (DerivedCategory.Q.obj P) ≫
        SB.mapDerivedCategory.map
          ((xd.homEquiv _ _).symm
            (DerivedCategory.Q.map
              ((Functor.mapHomologicalComplexIdIso _ (.up ℤ)).inv.app P ≫
                (NatTrans.mapHomologicalComplex x.unit (.up ℤ)).app P ≫
                (Functor.mapHomologicalComplexCompIso (Iso.refl (TX ⋙ RX)) (.up ℤ)).inv.app
                  P) ≫
              RX.mapDerivedCategoryFactors.inv.app
                ((TX.mapHomologicalComplex (.up ℤ)).obj P))) ≫
        SB.mapDerivedCategoryFactors.hom.app ((TX.mapHomologicalComplex (.up ℤ)).obj P) := by
  dsimp only
  let α := (a.comp y).leftAdjointUniq ((x.comp b).ofNatIsoRight β.symm)
  let ad := a.mapDerivedCategoryAdjunction
  let bd := b.mapDerivedCategoryAdjunction
  let rA := UA.mapDerivedCategoryFactors.symm
  let rB := UB.mapDerivedCategoryFactors.symm
  let rX := RX.mapDerivedCategoryFactors.symm
  let rY := RY.mapDerivedCategoryFactors.symm
  let r := compositeRightFactor rA rY
  let s := compositeRightFactor rX rB
  let βd := Functor.mapDerivedCategorySquareIso β
  let σ := ((conjugateIsoEquiv (ad.comp yd) (xd.comp bd)).symm βd).symm
  have hα : ∀ M, (a.comp y).unit.app M ≫ (RY ⋙ UA).map (α.hom.app M) =
      (x.comp b).unit.app M ≫ β.inv.app ((TX ⋙ SB).obj M) := by
    intro M
    exact Adjunction.unit_leftAdjointUniq_hom_app (a.comp y)
      ((x.comp b).ofNatIsoRight β.symm) M
  have hαc := complexConjugateUnit a y x b α.hom β.inv hα
  have hσ : ∀ K, (ad.comp yd).unit.app K ≫
      (RY.mapDerivedCategory ⋙ UA.mapDerivedCategory).map (σ.hom.app K) =
      (xd.comp bd).unit.app K ≫ βd.inv.app ((LX ⋙ SB.mapDerivedCategory).obj K) := by
    intro K
    exact (unit_conjugateEquiv_symm (xd.comp bd) (ad.comp yd) βd.inv K).symm
  have hs := exactSquareInverseFactors β
  have hr : ∀ K, DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex β.inv (.up ℤ)).app K) ≫ r.hom.app K =
      s.hom.app K ≫ βd.inv.app (DerivedCategory.Q.obj K) := by
    intro K
    let βc := NatIso.mapHomologicalComplex β (.up ℤ)
    exact (inverseSquare (DerivedCategory.Q.mapIso (βc.app K))
      (βd.app (DerivedCategory.Q.obj K)) (r.hom.app K) (s.hom.app K)
      (by simpa only [r, s, rA, rB, rX, rY, βd, βc, Functor.comp_obj,
        Iso.app_hom, Functor.mapIso_hom, NatIso.mapHomologicalComplex] using (hs K).symm)).symm
  have hc := adjointComparison_conjugate DerivedCategory.Q DerivedCategory.Q
    ((a.mapHomologicalComplex (.up ℤ)).comp (y.mapHomologicalComplex (.up ℤ)))
    ((x.mapHomologicalComplex (.up ℤ)).comp (b.mapHomologicalComplex (.up ℤ)))
    (ad.comp yd) (xd.comp bd) r s
    (NatTrans.mapHomologicalComplex α.hom (.up ℤ))
    (NatTrans.mapHomologicalComplex β.inv (.up ℤ)) σ.hom βd.inv hαc hσ hr P
  rw [← adjointComparison_comp DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    (a.mapHomologicalComplex (.up ℤ)) (y.mapHomologicalComplex (.up ℤ)) ad yd rA rY r
    (compositeRightFactor_hom rA rY) P] at hc
  rw [← adjointComparison_comp DerivedCategory.Q DerivedCategory.Q DerivedCategory.Q
    (x.mapHomologicalComplex (.up ℤ)) (b.mapHomologicalComplex (.up ℤ)) xd bd rX rB s
    (compositeRightFactor_hom rX rB) P] at hc
  dsimp only [ad, bd, rA, rB] at hc
  rw [sumComparison, sumComparison] at hc
  simpa only [rX, rY, Category.assoc, adjointComparison, complexUnit, Iso.symm_hom,
    α, σ, βd, ad, bd, Functor.comp_obj] using hc

namespace AlgebraicGeometry.Etale
attribute [local instance 2000] cachedEtaleGroth cachedEtaleSheafify
  cachedEtaleMonoidalPreadditive cachedEtaleCoproducts
  cachedEtaleColimits cachedEtaleFlatResolution
  cachedEtaleInjectiveResolution cachedEtaleExactColimits
  cachedEtaleTensor4 cachedEtaleTensor12 cachedEtaleTensor23
  cachedEtaleTensorColimits cachedEtaleTensorFlipColimits

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor upperStar lowerStar openImmersionLowerShriek
  etaleLowerShriek ProEtale.etaleSheafExtendScalars

end AlgebraicGeometry.Etale
