/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Counit
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Trivializations of left derived functors

Let `F : C ⥤ C` be an exact endofunctor of an abelian category with functorial flat
resolutions, and `e : F ≅ 𝟭 C` a trivialization of `F`. Then the total left derived functor
of `F` is trivialized as well, `L(F) ≅ L(𝟭) ≅ D(𝟭) ≅ 𝟭`
(`CategoryTheory.Functor.leftDerivedFunctorIsoId`). We show that this construction is
compatible with composition and with commutative squares of exact functors; both statements
are checked on the image of the homotopy category, through the counits of the derived
functors.

## Main definitions

- `CategoryTheory.Functor.leftDerivedFunctorIsoId`: the trivialization `L(F) ≅ 𝟭` induced by a
  trivialization `F ≅ 𝟭`.

## Main statements

- `CategoryTheory.Functor.leftDerivedFunctorIsoId_hom_app_Qh_obj`: the trivialization on the
  image of a complex.
- `CategoryTheory.Functor.leftDerivedFunctorIsoId_comp`: compatibility with composition.
- `CategoryTheory.Functor.leftDerivedFunctorIsoId_square`: compatibility with a commutative
  square.
-/

@[expose] public section

universe wC wD vC vD uC uD

open CategoryTheory Limits

namespace CategoryTheory.Functor

open MonoidalCategory DerivedCategory

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D] [Abelian C] [Abelian D]

/-- The composite `e.hom ≫ (𝟭 ≅ 𝟭)` on the image of a complex in the homotopy category. -/
lemma mapHomotopyCategory_isoId_quotient_obj {F : C ⥤ D} {G : C ⥤ D} [F.Additive] [G.Additive]
    (e : F ⟶ G) (K : CochainComplex C ℤ) :
    (NatTrans.mapHomotopyCategory e (.up ℤ)).app ((HomotopyCategory.quotient C _).obj K) =
      (HomotopyCategory.quotient D _).map ((NatTrans.mapHomologicalComplex e (.up ℤ)).app K) :=
  rfl

/-- The homotopy category statement behind `leftDerivedFunctorIsoId_comp`. -/
lemma mapHomotopyCategory_isoId_comp {F G H : C ⥤ C} [F.Additive] [G.Additive] [H.Additive]
    (eF : F ≅ 𝟭 C) (eG : G ≅ 𝟭 C) (c : H ≅ F ⋙ G)
    (P : HomotopyCategory C (.up ℤ)) :
    (NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app P ≫
        ((NatTrans.mapHomotopyCategory eG.hom (.up ℤ)).app
            ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
          (mapHomotopyCategoryIdIso C (.up ℤ)).hom.app
            ((F.mapHomotopyCategory (.up ℤ)).obj P)) ≫
        (NatTrans.mapHomotopyCategory eF.hom (.up ℤ)).app P ≫
          (mapHomotopyCategoryIdIso C (.up ℤ)).hom.app P =
      (NatTrans.mapHomotopyCategory (c ≪≫ isoWhiskerRight eF G ≪≫ G.leftUnitor ≪≫ eG).hom
          (.up ℤ)).app P ≫
        (mapHomotopyCategoryIdIso C (.up ℤ)).hom.app P := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  erw [mapHomotopyCategoryIdIso_hom_app, mapHomotopyCategoryIdIso_hom_app]
  rw [mapHomotopyCategory_isoId_quotient_obj, mapHomotopyCategory_isoId_quotient_obj,
    mapHomotopyCategory_isoId_quotient_obj]
  erw [mapHomotopyCategory_isoId_quotient_obj]
  simp only [← Functor.map_comp]
  congr 1
  ext n : 1
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    mapHomologicalComplexIdIso_hom_app_f, Iso.trans_hom, NatTrans.comp_app,
    isoWhiskerRight_hom, whiskerRight_app, leftUnitor_hom_app,
    Category.id_comp, id_obj, comp_obj]
  erw [Category.comp_id, Category.comp_id]
  rw [eG.hom.naturality]
  erw [Category.comp_id]
  rfl

/-- The homotopy category statement behind `leftDerivedFunctorIsoId_square`. -/
lemma mapHomotopyCategory_isoId_square {F : C ⥤ C} {G : C ⥤ D} {F' : D ⥤ D} [F.Additive]
    [G.Additive] [F'.Additive] (eF : F ≅ 𝟭 C) (eF' : F' ≅ 𝟭 D) (c : F ⋙ G ≅ G ⋙ F')
    (hc : c.hom ≫ whiskerLeft G eF'.hom = whiskerRight eF.hom G ≫ G.leftUnitor.hom ≫
      G.rightUnitor.inv) (P : HomotopyCategory C (.up ℤ)) :
    (NatTrans.mapHomotopyCategory c.hom (.up ℤ)).app P ≫
        (NatTrans.mapHomotopyCategory eF'.hom (.up ℤ)).app
            ((G.mapHomotopyCategory (.up ℤ)).obj P) ≫
          (mapHomotopyCategoryIdIso D (.up ℤ)).hom.app ((G.mapHomotopyCategory (.up ℤ)).obj P) =
      (G.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory eF.hom (.up ℤ)).app P ≫
          (mapHomotopyCategoryIdIso C (.up ℤ)).hom.app P) := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective P
  erw [mapHomotopyCategoryIdIso_hom_app, mapHomotopyCategoryIdIso_hom_app]
  rw [mapHomotopyCategory_isoId_quotient_obj, mapHomotopyCategory_isoId_quotient_obj]
  erw [mapHomotopyCategory_isoId_quotient_obj]
  rw [← (HomotopyCategory.quotient C (.up ℤ)).map_comp, Functor.mapHomotopyCategory_map]
  simp only [← Functor.map_comp]
  congr 1
  ext n : 1
  have := NatTrans.congr_app hc (K.X n)
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, leftUnitor_hom_app,
    rightUnitor_inv_app, Category.comp_id] at this
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    mapHomologicalComplexIdIso_hom_app_f, Functor.mapHomologicalComplex_map_f]
  erw [Category.comp_id, Category.comp_id]
  erw [Category.comp_id] at this
  exact this

variable [HasDerivedCategory.{wC} C] [HasDerivedCategory.{wD} D]

variable [MonoidalCategory C] [MonoidalPreadditive C]
  [HasCountableCoproducts C]
  [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
  [∀ (X : C), PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution C]

section NatIso

variable {F G H : C ⥤ D} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- The isomorphism of left derived functors induced by a composite of isomorphisms of exact
functors is the composite of the induced isomorphisms. -/
lemma leftDerivedFunctorNatIso_trans (e : F ≅ G) (e' : G ≅ H) :
    F.leftDerivedFunctorNatIso (e ≪≫ e') =
      F.leftDerivedFunctorNatIso e ≪≫ G.leftDerivedFunctorNatIso e' := by
  ext : 1
  refine Localization.natTrans_ext Qh (HomotopyCategory.quasiIso _ (.up ℤ)) fun P ↦ ?_
  rw [← cancel_mono (H.leftDerivedFunctorCounit.app P)]
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc]
  rw [leftDerivedFunctorNatIso_hom_app_comp_counit, leftDerivedFunctorNatIso_hom_app_comp_counit,
    leftDerivedFunctorNatIso_hom_app_comp_counit_assoc, Category.assoc, ← Functor.map_comp,
    ← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp]

/-- The isomorphism of left derived functors induced by the identity is the identity. -/
@[simp]
lemma leftDerivedFunctorNatIso_refl :
    F.leftDerivedFunctorNatIso (Iso.refl F) = Iso.refl _ := by
  ext : 1
  refine Localization.natTrans_ext Qh (HomotopyCategory.quasiIso _ (.up ℤ)) fun P ↦ ?_
  rw [← cancel_mono (F.leftDerivedFunctorCounit.app P),
    leftDerivedFunctorNatIso_hom_app_comp_counit]
  simp

/-- The isomorphism of left derived functors induced by the inverse of an isomorphism is the
inverse of the induced isomorphism. -/
lemma leftDerivedFunctorNatIso_symm (e : F ≅ G) :
    G.leftDerivedFunctorNatIso e.symm = (F.leftDerivedFunctorNatIso e).symm := by
  ext : 1
  rw [Iso.symm_hom, ← Iso.hom_comp_eq_id, ← Iso.trans_hom, ← leftDerivedFunctorNatIso_trans,
    Iso.self_symm_id, leftDerivedFunctorNatIso_refl, Iso.refl_hom]

end NatIso

section IsoId

variable (F : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The trivialization `L(F) ≅ L(𝟭) ≅ D(𝟭) ≅ 𝟭` of the total left derived functor of an exact
endofunctor `F` induced by a trivialization `e : F ≅ 𝟭`. -/
noncomputable def leftDerivedFunctorIsoId (e : F ≅ 𝟭 C) : F.leftDerivedFunctor ≅ 𝟭 _ :=
  F.leftDerivedFunctorNatIso e ≪≫ (𝟭 C).leftDerivedFunctorIsoMapDerivedCategory ≪≫
    mapDerivedCategoryIdIso C

/-- On the image `Qh P` of a complex, the trivialization `L(F) ≅ 𝟭` induced by `e : F ≅ 𝟭` is
`e`, through the counit of the derived functor. -/
lemma leftDerivedFunctorIsoId_hom_app_Qh_obj (e : F ≅ 𝟭 C)
    (P : HomotopyCategory C (.up ℤ)) :
    (F.leftDerivedFunctorIsoId e).hom.app (Qh.obj P) =
      F.leftDerivedFunctorCounit.app P ≫
        Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P ≫
          (mapHomotopyCategoryIdIso C (.up ℤ)).hom.app P) := by
  have hfac := NatTrans.congr_app F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac P
  have hnat := mapDerivedCategoryNatIso_fach e P
  have hid := NatTrans.congr_app (congrArg Iso.hom (mapDerivedCategoryIdIso_factorsh C)) P
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerLeft_hom,
    whiskerLeft_app, rightUnitor_hom_app, isoWhiskerRight_hom,
    whiskerRight_app, leftUnitor_hom_app] at hfac hid
  simp only [leftDerivedFunctorIsoId, leftDerivedFunctorNatIso, Iso.trans_hom,
    Iso.symm_hom, NatTrans.comp_app, Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← hfac, Category.assoc, Functor.map_comp]
  congr 1
  have hid' : (mapDerivedCategoryIdIso C).hom.app (Qh.obj P) =
      (𝟭 C).mapDerivedCategoryFactorsh.hom.app P ≫
        Qh.map ((mapHomotopyCategoryIdIso C (.up ℤ)).hom.app P) := by
    erw [Category.comp_id, Category.comp_id] at hid
    exact hid
  rw [hid', reassoc_of% hnat]

end IsoId

/-- The naturality of the counit of a left derived functor, with the composite functors
unfolded. -/
@[reassoc]
lemma leftDerivedFunctorCounit_naturality' (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F]
    {P Q : HomotopyCategory C (.up ℤ)} (f : P ⟶ Q) :
    F.leftDerivedFunctor.map (Qh.map f) ≫ F.leftDerivedFunctorCounit.app Q =
      F.leftDerivedFunctorCounit.app P ≫ Qh.map ((F.mapHomotopyCategory (.up ℤ)).map f) :=
  F.leftDerivedFunctorCounit.naturality f

section Comp

variable {F G H : C ⥤ C} [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]

/-- **Compatibility of the derived trivializations with composition**: for exact
endofunctors with trivializations `eF : F ≅ 𝟭`, `eG : G ≅ 𝟭` and `c : H ≅ F ⋙ G`, the
composite `L(H) ≅ L(F ⋙ G) ≅ L(F) ⋙ L(G) ≅ 𝟭` of the derived trivializations is the derived
trivialization of the composite `H ≅ F ⋙ G ≅ 𝟭`. -/
lemma leftDerivedFunctorIsoId_comp (eF : F ≅ 𝟭 C) (eG : G ≅ 𝟭 C) (c : H ≅ F ⋙ G) :
    H.leftDerivedFunctorNatIso c ≪≫ F.leftDerivedFunctorCompIso G ≪≫
        isoWhiskerRight (F.leftDerivedFunctorIsoId eF) G.leftDerivedFunctor ≪≫
        G.leftDerivedFunctor.leftUnitor ≪≫ G.leftDerivedFunctorIsoId eG =
      H.leftDerivedFunctorIsoId (c ≪≫ isoWhiskerRight eF G ≪≫ G.leftUnitor ≪≫ eG) := by
  ext : 1
  refine Localization.natTrans_ext Qh (HomotopyCategory.quasiIso _ (.up ℤ)) fun P ↦ ?_
  simp only [Iso.trans_hom, NatTrans.comp_app, isoWhiskerRight_hom, whiskerRight_app,
    leftUnitor_hom_app]
  erw [Category.id_comp]
  rw [leftDerivedFunctorIsoId_hom_app_Qh_obj F eF P, Functor.map_comp, Category.assoc]
  have hn := (G.leftDerivedFunctorIsoId eG).hom.naturality (Qh.map
    ((NatTrans.mapHomotopyCategory eF.hom (.up ℤ)).app P ≫
      (mapHomotopyCategoryIdIso C (.up ℤ)).hom.app P))
  rw [id_map] at hn
  erw [hn]
  rw [leftDerivedFunctorIsoId_hom_app_Qh_obj G eG, leftDerivedFunctorIsoId_hom_app_Qh_obj H,
    Category.assoc, leftDerivedFunctorCompIso_hom_app_comp_counit_assoc,
    leftDerivedFunctorNatIso_hom_app_comp_counit_assoc]
  congr 1
  rw [← Functor.map_comp, ← Functor.map_comp, mapHomotopyCategory_isoId_comp]

end Comp

section Square

variable [MonoidalCategory D] [MonoidalPreadditive D]
  [HasCountableCoproducts D]
  [HasColimitsOfShape ℤ D] [HasExactColimitsOfShape ℤ D]
  [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ D), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ D), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).obj X)]
  [∀ (X : D), PreservesColimitsOfShape ℤ ((curriedTensor D).flip.obj X)]
  [Abelian.HasFunctorialFlatResolution D]

variable {F : C ⥤ C} {G : C ⥤ D} {F' : D ⥤ D}
  [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']

/-- **Compatibility of the derived trivializations with commutative squares**: for exact
functors `F : C ⥤ C`, `G : C ⥤ D`, `F' : D ⥤ D`, trivializations `eF : F ≅ 𝟭`, `eF' : F' ≅ 𝟭`
and an isomorphism `c : F ⋙ G ≅ G ⋙ F'` compatible with them, the induced isomorphism
`L(F) ⋙ L(G) ≅ L(F ⋙ G) ≅ L(G ⋙ F') ≅ L(G) ⋙ L(F')` is compatible with the derived
trivializations. -/
lemma leftDerivedFunctorIsoId_square (eF : F ≅ 𝟭 C) (eF' : F' ≅ 𝟭 D) (c : F ⋙ G ≅ G ⋙ F')
    (hc : c.hom ≫ whiskerLeft G eF'.hom = whiskerRight eF.hom G ≫ G.leftUnitor.hom ≫
      G.rightUnitor.inv) :
    (F.leftDerivedFunctorCompIso G).inv ≫ ((F ⋙ G).leftDerivedFunctorNatIso c).hom ≫
        (G.leftDerivedFunctorCompIso F').hom ≫
        whiskerLeft G.leftDerivedFunctor (F'.leftDerivedFunctorIsoId eF').hom =
      whiskerRight (F.leftDerivedFunctorIsoId eF).hom G.leftDerivedFunctor ≫
        G.leftDerivedFunctor.leftUnitor.hom ≫ G.leftDerivedFunctor.rightUnitor.inv := by
  refine Localization.natTrans_ext Qh (HomotopyCategory.quasiIso _ (.up ℤ)) fun P ↦ ?_
  rw [← cancel_mono (G.leftDerivedFunctorCounit.app P)]
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, leftUnitor_hom_app,
    rightUnitor_inv_app, Category.assoc]
  erw [Category.id_comp, Category.id_comp]
  have hn := (F'.leftDerivedFunctorIsoId eF').hom.naturality (G.leftDerivedFunctorCounit.app P)
  rw [id_map] at hn
  erw [← hn]
  erw [leftDerivedFunctorIsoId_hom_app_Qh_obj F' eF' ((G.mapHomotopyCategory (.up ℤ)).obj P)]
  rw [leftDerivedFunctorIsoId_hom_app_Qh_obj F eF P, G.leftDerivedFunctor.map_comp,
    Category.assoc]
  erw [leftDerivedFunctorCounit_naturality']
  rw [leftDerivedFunctorCompIso_hom_app_comp_counit_assoc,
    leftDerivedFunctorNatIso_hom_app_comp_counit_assoc,
    ← leftDerivedFunctorCompIso_hom_app_comp_counit, Category.assoc, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  simp only [← Functor.map_comp, mapHomotopyCategory_isoId_square eF eF' c hc]

end Square

end CategoryTheory.Functor
