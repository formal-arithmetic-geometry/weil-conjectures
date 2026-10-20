/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NO
-/
module

public import Sheaf.AlgebraicGeometry.GeometricPointDerivedConstants
public import Sheaf.AlgebraicGeometry.EtaleConstantProjectionMap
public import Sheaf.AlgebraicGeometry.PullbackConstantModule
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
import WeilConjectures.CategoryTheory.RightDerivedSingleZeroUnit
import WeilConjectures.CategoryTheory.DerivedExactCompositionComparison
import WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf

/-!
# Derived sections over a geometric point, with adjunction normalization

Source: Stacks Project, sites-cohomology.tex, Tag 07A6, and etale-cohomology.tex,
Tags 04JQ and 0F0F (blueprint: lem-kun-geometric-point-derived-sections-adjunction).

The integer-module encoding and the actual stalk are those of the dependency
`GeometricPointDerivedConstants`. All derived inverse images and constants below are
termwise exact functors. The image and constant-section adjunctions are constructed
directly from the exact left adjoints and right-derived units. Equality with the
transported canonical left-derived adjunctions follows from their unit factorizations.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

private theorem uniq_transport
    {C D : Type*} [Category* C] [Category* D]
    {L₀ L₁ : C ⥤ D} {R₀ R₁ : D ⥤ C}
    (a : L₀ ⊣ R₀) (b : L₁ ⊣ R₁) (e : L₀ ≅ L₁) :
    ((a.ofNatIsoLeft e).rightAdjointUniq b).hom =
      conjugateEquiv a b e.inv := by
  ext X
  simp [Adjunction.rightAdjointUniq, conjugateEquiv_apply_app,
    Adjunction.ofNatIsoLeft_counit]

private theorem conjugate_right_transport
    {C D : Type*} [Category* C] [Category* D]
    {L₀ L₁ : C ⥤ D} {R₀ R₀' R₁ : D ⥤ C}
    (a : L₀ ⊣ R₀) (b : L₁ ⊣ R₁) (t : R₀ ≅ R₀') (e : L₁ ⟶ L₀) :
    conjugateEquiv (a.ofNatIsoRight t) b e =
      t.inv ≫ conjugateEquiv a b e := by
  ext X
  simp only [conjugateEquiv_apply_app, Adjunction.ofNatIsoRight_counit,
    NatTrans.comp_app, Functor.whiskerRight_app, CategoryTheory.Functor.map_comp]
  rw [← R₁.map_comp_assoc, ← e.naturality, R₁.map_comp_assoc]
  have hn := b.unit.naturality (t.inv.app X)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  rw [← reassoc_of% hn]

private theorem conjugate_target_transport
    {C D : Type*} [Category* C] [Category* D]
    {L₀ L₁ : C ⥤ D} {R₀ R₁ R₁' : D ⥤ C}
    (a : L₀ ⊣ R₀) (b : L₁ ⊣ R₁) (t : R₁ ≅ R₁') (e : L₁ ⟶ L₀) :
    conjugateEquiv a (b.ofNatIsoRight t) e = conjugateEquiv a b e ≫ t.hom := by
  ext X
  simp only [conjugateEquiv_apply_app, Adjunction.ofNatIsoRight_unit,
    NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  rw [← t.hom.naturality_assoc, ← t.hom.naturality]

private theorem right_transport_uniq
    {C D : Type*} [Category* C] [Category* D]
    {L : C ⥤ D} {R R' : D ⥤ C} (a : L ⊣ R) (b : L ⊣ R') :
    a.ofNatIsoRight (a.rightAdjointUniq b) = b := by
  apply Adjunction.ext
  ext X
  simp [Adjunction.ofNatIsoRight_unit]

private theorem left_uniq_conjugate
    {C D : Type*} [Category* C] [Category* D]
    {L L' : C ⥤ D} {R R' : D ⥤ C}
    (a : L ⊣ R) (b : L' ⊣ R') (t : R ≅ R') :
    conjugateEquiv a b ((a.ofNatIsoRight t).leftAdjointUniq b).inv = t.hom := by
  apply (cancel_epi t.inv).1
  rw [← conjugate_right_transport]
  simp [Adjunction.leftAdjointUniq]

private theorem comp_right_transport
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L₀ : C ⥤ D} {R₀ R₀' : D ⥤ C} {L₁ : D ⥤ E} {R₁ : E ⥤ D}
    (a : L₀ ⊣ R₀) (b : L₁ ⊣ R₁) (t : R₀ ≅ R₀') :
    (a.ofNatIsoRight t).comp b = (a.comp b).ofNatIsoRight (Functor.isoWhiskerLeft R₁ t) := by
  apply Adjunction.ext
  ext X
  simp only [Adjunction.comp_unit_app, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.isoWhiskerLeft_hom,
    Category.assoc]
  exact congrArg (a.unit.app X ≫ ·) (t.hom.naturality (b.unit.app (L₀.obj X))).symm

private theorem ordinary_comparison
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    {L : C ⥤ D} {R R' T : D ⥤ C} {U : D ⥤ E} {F : E ⥤ D}
    {L' : C ⥤ E} {H T' : E ⥤ C}
    (a : L ⊣ R) (b : L ⊣ R') (aT : L ⊣ T)
    (c : L' ⊣ H) (cT : L' ⊣ T') (f : U ⊣ F) (q : F ⋙ T ≅ T') :
    Functor.whiskerLeft F (a.rightAdjointUniq b).hom ≫
      conjugateEquiv (b.comp f) c
        (((aT.comp f).ofNatIsoRight q).leftAdjointUniq cT).inv =
    (Functor.isoWhiskerLeft F (a.rightAdjointUniq aT)).hom ≫
      q.hom ≫ (c.rightAdjointUniq cT).inv := by
  let r := a.rightAdjointUniq b
  let t := a.rightAdjointUniq aT
  let v := c.rightAdjointUniq cT
  let γ := ((aT.comp f).ofNatIsoRight q).leftAdjointUniq cT
  have hb : b.comp f = (a.comp f).ofNatIsoRight (Functor.isoWhiskerLeft F r) := by
    rw [← comp_right_transport, right_transport_uniq]
  have ht : aT.comp f = (a.comp f).ofNatIsoRight (Functor.isoWhiskerLeft F t) := by
    rw [← comp_right_transport, right_transport_uniq]
  have hc : cT = c.ofNatIsoRight v := (right_transport_uniq c cT).symm
  have he := left_uniq_conjugate (aT.comp f) cT q
  change conjugateEquiv (aT.comp f) cT γ.inv = q.hom at he
  rw [ht, hc, conjugate_right_transport, conjugate_target_transport] at he
  have he' : conjugateEquiv (a.comp f) c γ.inv =
      (Functor.isoWhiskerLeft F t).hom ≫ q.hom ≫ v.inv := by
    rw [← he]
    ext X
    simp [Category.assoc]
  change Functor.whiskerLeft F r.hom ≫ conjugateEquiv (b.comp f) c γ.inv = _
  rw [hb, conjugate_right_transport, he']
  ext X
  simp [r, t, v]

private theorem exactDerivedAdjunction_eq
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (adj : L ⊣ R) (a : L.mapDerivedCategory ⊣ R.rightDerivedFunctor)
    (ha : ∀ K : HomotopyCategory C (.up ℤ),
      a.unit.app (DerivedCategory.Qh.obj K) ≫
        R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app K) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app K) ≫
        R.rightDerivedFunctorUnit.app ((L.mapHomotopyCategory (.up ℤ)).obj K)) :
    a = adj.mapDerivedCategoryRightDerivedAdjunction := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Qh (HomotopyCategory.quasiIso C (.up ℤ))
  intro K
  apply (cancel_mono
    (R.rightDerivedFunctor.map (L.mapDerivedCategoryFactorsh.hom.app K))).1
  exact (ha K).trans
    ((adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso C (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
      R.rightDerivedFunctorUnit K).symm

private theorem transported_unit_fac
    {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) (Q : C ⥤ E) (Q' : D ⥤ F)
    {L₀ L₁ : E ⥤ F} {R' : F ⥤ E} (a : L₀ ⊣ R') (e : L₀ ≅ L₁)
    (α₀ : Q ⋙ L₀ ⟶ L ⋙ Q') (α₁ : Q ⋙ L₁ ⟶ L ⋙ Q')
    (β : R ⋙ Q ⟶ Q' ⋙ R') (K : C)
    (ha : a.unit.app (Q.obj K) ≫ R'.map (α₀.app K) =
      Q.map (adj.unit.app K) ≫ β.app (L.obj K))
    (he : e.hom.app (Q.obj K) ≫ α₁.app K = α₀.app K) :
    (a.ofNatIsoLeft e).unit.app (Q.obj K) ≫ R'.map (α₁.app K) =
      Q.map (adj.unit.app K) ≫ β.app (L.obj K) := by
  simp only [Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app, Functor.whiskerRight_app]
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, he]
  exact ha

private theorem canonicalDerivedAdjunction_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalPreadditive C] [HasCountableCoproducts C]
    [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ C, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ X₁ X₂ X₃ : GradedObject ℤ C, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ X₁ X₂ X₃ : GradedObject ℤ C, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ X : C, PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).obj X)]
    [∀ X : C, PreservesColimitsOfShape ℤ ((MonoidalCategory.curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C] [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions D]
    {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R) :
    adj.derivedAdjunction.ofNatIsoLeft L.leftDerivedFunctorIsoMapDerivedCategory =
      adj.mapDerivedCategoryRightDerivedAdjunction := by
  apply exactDerivedAdjunction_eq
  intro K
  apply transported_unit_fac (adj.mapHomotopyCategory (.up ℤ))
  · exact Adjunction.derivedη_fac_app _ (HomotopyCategory.quasiIso _ (.up ℤ)) _ _ K
  · exact NatTrans.congr_app L.leftDerivedFunctorIsoMapDerivedCategory_hom_fac K

private theorem factorh_inv_quotient
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (S : C ⥤ D) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (K : CochainComplex C ℤ) :
    S.mapDerivedCategoryFactorsh.inv.app ((HomotopyCategory.quotient C (.up ℤ)).obj K) =
      S.mapDerivedCategoryFactors.inv.app K := by
  apply (cancel_mono (S.mapDerivedCategoryFactorsh.hom.app
    ((HomotopyCategory.quotient C (.up ℤ)).obj K))).1
  rw [Iso.inv_hom_id_app, Functor.mapDerivedCategoryFactorsh_hom_app]
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Functor.mapHomotopyCategoryFactors,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv]
  repeat erw [CategoryTheory.Functor.map_id]
  simp
  rfl

private theorem exact_comparison_unit
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) (S : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [S.Additive] [H.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : F ⋙ S ≅ H) (K : HomotopyCategory C (.up ℤ)) :
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit F S).app K ≫
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F S).inv.app
        (DerivedCategory.Qh.obj K) ≫
      (Functor.rightDerivedFunctorNatIso e).hom.app (DerivedCategory.Qh.obj K) =
    DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app K) ≫
      H.rightDerivedFunctorUnit.app K := by
  simp [Functor.rightDerivedFunctorCompMapDerivedCategoryIso,
    Functor.rightDerivedFunctorNatIso, Functor.rightDerivedFunctorNatTrans,
    Functor.rightDerivedUnique]

private theorem single_chain_comparison
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    (F : C ⥤ D) (S : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [S.Additive] [H.Additive] (e : F ⋙ S ⟶ H) (M : C) :
    (S.mapCochainComplexSingleFunctor 0).inv.app (F.obj M) ≫
      (S.mapHomologicalComplex (.up ℤ)).map
        ((F.mapCochainComplexSingleFunctor 0).inv.app M) ≫
      (NatTrans.mapHomologicalComplex e (.up ℤ)).app
        ((CochainComplex.singleFunctor C 0).obj M) =
    (CochainComplex.singleFunctor E 0).map (e.app M) ≫
      (H.mapCochainComplexSingleFunctor 0).inv.app M := by
  apply HomologicalComplex.from_single_hom_ext
  dsimp only [Functor.mapCochainComplexSingleFunctor, HomologicalComplex.comp_f,
    CategoryTheory.Functor.mapHomologicalComplex_map_f]
  simp only [Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
  simp only [Functor.comp_obj, CategoryTheory.Functor.map_comp, Category.assoc,
    Iso.map_inv_hom_id_assoc]
  simp only [HomologicalComplex.singleObjXSelf, HomologicalComplex.singleObjXIsoOfEq,
    CochainComplex.singleFunctor, CochainComplex.singleFunctors, HomologicalComplex.single]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem exact_comparison_single
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [EnoughInjectives C]
    (F : C ⥤ D) (S : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [S.Additive] [H.Additive]
    [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (e : F ⋙ S ≅ H) (M : C) :
    S.mapDerivedCategory.map (F.rightDerivedSingleUnit M) ≫
      ((Functor.rightDerivedFunctorCompMapDerivedCategoryIso F S).inv ≫
        (Functor.rightDerivedFunctorNatIso e).hom).app
          ((DerivedCategory.singleFunctor C 0).obj M) =
      (S.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) ≫
        (DerivedCategory.singleFunctor E 0).map (e.hom.app M) ≫ H.rightDerivedSingleUnit M := by
  let I := (CochainComplex.singleFunctor C 0).obj M
  let K := (HomotopyCategory.quotient C (.up ℤ)).obj I
  let β := (Functor.rightDerivedFunctorCompMapDerivedCategoryIso F S).inv ≫
    (Functor.rightDerivedFunctorNatIso e).hom
  have hu := exact_comparison_unit F S H e K
  have hi : (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ S)) (.up ℤ)).inv.app K =
      𝟙 _ := by
    have hi := Iso.inv_hom_id_app
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (F ⋙ S)) (.up ℤ)) K
    erw [Functor.mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at hi
    exact hi
  dsimp only [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app] at hu
  simp only [Category.id_comp, Category.comp_id, Category.assoc] at hu
  erw [hi, CategoryTheory.Functor.map_id, Category.id_comp] at hu
  change S.mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.quotient D (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj I)) ≫
      S.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app K) ≫
      β.app (DerivedCategory.Qh.obj K) = _ at hu
  rw [factorh_inv_quotient] at hu
  apply (cancel_epi ((S.mapDerivedCategorySingleFunctor 0).inv.app (F.obj M))).1
  simp only [← Category.assoc, Iso.inv_hom_id_app, Category.id_comp]
  have hs : (S.mapDerivedCategorySingleFunctor 0).inv.app (F.obj M) =
      DerivedCategory.Q.map ((S.mapCochainComplexSingleFunctor 0).inv.app (F.obj M)) ≫
        S.mapDerivedCategoryFactors.inv.app
          ((CochainComplex.singleFunctor D 0).obj (F.obj M)) := by
    apply (cancel_mono (S.mapDerivedCategoryFactors.hom.app
      ((CochainComplex.singleFunctor D 0).obj (F.obj M)))).1
    simpa only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id,
      CochainComplex.singleFunctor, CochainComplex.singleFunctors, Functor.comp_obj] using
      S.mapDerivedCategorySingleFunctor_inv_app_mapDerivedCategoryFactors_hom_app (F.obj M)
  rw [hs]
  dsimp only [Functor.rightDerivedSingleUnit, NatTrans.comp_app]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := S.mapDerivedCategoryFactors.inv.naturality
    ((F.mapCochainComplexSingleFunctor 0).inv.app M)
  dsimp only [Functor.comp_map] at hn
  erw [← reassoc_of% hn]
  dsimp only [β, NatTrans.comp_app] at hu
  try simp only [Category.assoc] at hu
  erw [hu]
  change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ ≫
      DerivedCategory.Q.map _ ≫ H.rightDerivedFunctorUnit.app K = _
  rw [← DerivedCategory.Q.map_comp_assoc, ← DerivedCategory.Q.map_comp_assoc]
  have hc := single_chain_comparison F S H e.hom M
  erw [Category.assoc, hc, DerivedCategory.Q.map_comp, Category.assoc]
  rfl

namespace CategoryTheory.Functor

/-- The canonical zeroth-cohomology comparison for a right-derived functor on a sheaf
in degree zero. Source: Stacks Tag 05TD
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricSectionsSingleH0Iso
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions C] [EnoughInjectives C]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] (M : C) :
    (DerivedCategory.homologyFunctor D 0).obj
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M)) ≅ F.obj M :=
  F.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫ F.rightDerivedZeroIsoSelf.app M

/-- The same comparison after an exact functor. Factoring the construction here avoids
rechecking the derived-functor comparison at large concrete sheaf categories.
Source: Stacks Tag 05TD
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricSectionsExactSingleH0Iso
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [EnoughInjectives C]
    (F : C ⥤ D) (S : D ⥤ E) [F.Additive] [S.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits S] [PreservesFiniteColimits S] (M : C) :
    (DerivedCategory.homologyFunctor E 0).obj
        ((F.rightDerivedFunctor ⋙ S.mapDerivedCategory).obj
          ((DerivedCategory.singleFunctor C 0).obj M)) ≅ S.obj (F.obj M) :=
  (S.mapDerivedCategoryHomologyFunctorIso 0).symm.app _ ≪≫
    S.mapIso (F.geometricSectionsSingleH0Iso M)

end CategoryTheory.Functor

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem comparison_zero
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [EnoughInjectives C]
    (F : C ⥤ D) (S : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [S.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits H]
    (β : F.rightDerivedFunctor ⋙ S.mapDerivedCategory ⟶ H.rightDerivedFunctor)
    (e : F ⋙ S ⟶ H) (M : C)
    (he : S.mapDerivedCategory.map (F.rightDerivedSingleUnit M) ≫
        β.app ((DerivedCategory.singleFunctor C 0).obj M) =
      (S.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) ≫
        (DerivedCategory.singleFunctor E 0).map (e.app M) ≫ H.rightDerivedSingleUnit M) :
    S.map (F.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫
        F.rightDerivedZeroIsoSelf.app M).inv ≫
      (S.mapDerivedCategoryHomologyFunctorIso 0).hom.app
        (F.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor C 0).obj M)) ≫
      (DerivedCategory.homologyFunctor E 0).map
        (β.app ((DerivedCategory.singleFunctor C 0).obj M)) ≫
      (H.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫
        H.rightDerivedZeroIsoSelf.app M).hom = e.app M := by
  let HD := DerivedCategory.homologyFunctor D 0
  let HE := DerivedCategory.homologyFunctor E 0
  let cD := DerivedCategory.singleFunctorCompHomologyFunctorIso D 0
  let cE := DerivedCategory.singleFunctorCompHomologyFunctorIso E 0
  let f₀ := F.homologyRightDerivedFunctorObjSingleFunctorIso M 0 ≪≫
    F.rightDerivedZeroIsoSelf.app M
  have huF : f₀.inv = cD.inv.app (F.obj M) ≫ HD.map (F.rightDerivedSingleUnit M) := by
    apply (cancel_mono f₀.hom).1
    simp only [Iso.inv_hom_id, Category.assoc]
    rw [F.rightDerivedSingleUnit_zero M, Iso.inv_hom_id_app]
    rfl
  rw [huF, CategoryTheory.Functor.map_comp, Category.assoc]
  have hn := (S.mapDerivedCategoryHomologyFunctorIso 0).hom.naturality
    (F.rightDerivedSingleUnit M)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  erw [← HE.map_comp_assoc, he]
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  have hs := S.mapDerivedCategoryHomologyFunctorIso_hom_app_singleFunctor 0 (F.obj M)
  have hs' : S.map (cD.inv.app (F.obj M)) ≫
      (S.mapDerivedCategoryHomologyFunctorIso 0).hom.app
        ((DerivedCategory.singleFunctor D 0).obj (F.obj M)) ≫
      HE.map ((S.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M)) =
      cE.inv.app (S.obj (F.obj M)) := by
    apply (cancel_mono (cE.hom.app (S.obj (F.obj M)))).1
    rw [Category.assoc, Category.assoc, hs]
    simp [cD, cE, ← S.map_comp]
  erw [reassoc_of% hs']
  erw [reassoc_of% (cE.inv.naturality (e.app M)).symm]
  rw [H.rightDerivedSingleUnit_zero M, Iso.inv_hom_id_app]
  simp

private theorem comparison_zero_factored
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C] [EnoughInjectives C]
    (F : C ⥤ D) (S : D ⥤ E) (H : C ⥤ E)
    [F.Additive] [S.Additive] [H.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    [PreservesFiniteLimits H]
    (β : F.rightDerivedFunctor ⋙ S.mapDerivedCategory ⟶ H.rightDerivedFunctor)
    (e : F ⋙ S ⟶ H) (M : C)
    (he : S.mapDerivedCategory.map (F.rightDerivedSingleUnit M) ≫
        β.app ((DerivedCategory.singleFunctor C 0).obj M) =
      (S.mapDerivedCategorySingleFunctor 0).hom.app (F.obj M) ≫
        (DerivedCategory.singleFunctor E 0).map (e.app M) ≫ H.rightDerivedSingleUnit M) :
    (Functor.geometricSectionsExactSingleH0Iso F S M).inv ≫
      (DerivedCategory.homologyFunctor E 0).map
        (β.app ((DerivedCategory.singleFunctor C 0).obj M)) ≫
      (H.geometricSectionsSingleH0Iso M).hom = e.app M := by
  simpa only [Functor.geometricSectionsExactSingleH0Iso,
    Functor.geometricSectionsSingleH0Iso, Iso.trans_inv, Iso.trans_hom,
    Functor.mapIso_inv, Iso.app_inv, Iso.symm_inv, Category.assoc] using
    comparison_zero F S H β e M he


namespace AlgebraicGeometry.Etale

/-- Register the additivity supplied by the normalized geometric-point equivalence.
Source: Stacks Tag 04JQ
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable instance geometricPointSectionsStalkAdditive
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] : (geometricPointStalk Ω).Additive :=
  (Classical.choice (nonempty_geometricPointDerivedConstantsData Ω)).stalkAdditive

/-- The normalized constant/stalk adjunction, whose unit is the canonical constant germ.
Its counit is uniquely determined by that normalization, so this choice selects no
arbitrary map. Source: Stacks Tag 04JQ
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsStalkAdjunction
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    geometricPointConstants Ω ⊣ geometricPointStalk Ω :=
  (Classical.choice (nonempty_geometricPointDerivedConstantsData Ω)).adjunction

/-- The canonical constant-section adjunction with termwise derived constants on the left.
Source: Stacks Tag 07A6
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsConstantAdjunction (Z : Scheme.{u}) :
    (constantSheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).mapDerivedCategory ⊣
      rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Z :=
  (constantSheafΓAdj Z.smallEtaleTopology
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).mapDerivedCategoryRightDerivedAdjunction

/-- The canonical derived inverse/direct-image adjunction, with the exact termwise inverse
image on the left. Source: Stacks Tag 07A6
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsImageAdjunction
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω)) :
    (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).mapDerivedCategory ⊣
      (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor :=
  (upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).mapDerivedCategoryRightDerivedAdjunction

/-- The canonical pullback-of-constants comparison, descended termwise.
Source: Stacks Tags 07A6 and 0F0F, and `lem-kun-pullback-constant`
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsConstantsIso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω)) :
    (geometricPointConstants Ω).mapDerivedCategory ⋙
        (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).mapDerivedCategory ≅
      (constantSheaf Z.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (geometricPointConstants Ω)
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h)

private theorem constantAdjunction_eq (Z : Scheme.{u}) :
    geometricPointSectionsConstantAdjunction Z =
      (constantSheafΓAdj Z.smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).mapDerivedCategoryRightDerivedAdjunction := by
  rfl

private theorem imageAdjunction_eq (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω)) :
    geometricPointSectionsImageAdjunction Ω h =
      (upperStarLowerStarAdjunction
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).mapDerivedCategoryRightDerivedAdjunction := by
  rfl

private theorem stalkAdjunction_eq (Ω : Type u) [Field Ω] [IsAlgClosed Ω] :
    (geometricPointSectionsStalkAdjunction Ω).mapDerivedCategoryAdjunction =
      ((geometricPointSectionsStalkAdjunction Ω).mapDerivedCategoryRightDerivedAdjunction
        |>.ofNatIsoRight (geometricPointStalk Ω).rightDerivedFunctorIsoMapDerivedCategory) := by
  unfold Adjunction.mapDerivedCategoryAdjunction
  rw [canonicalDerivedAdjunction_eq]

/-- The specified natural isomorphism of right adjoints. It is constructed by composing
constant/stalk with inverse/direct image, transporting the left adjoint through the
canonical constants comparison, and applying uniqueness of right adjoints.
Source: Stacks Tag 07A6 and the pushforward-composition proof following it
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointDerivedSectionsIso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω)) :
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor ⋙
        (geometricPointStalk Ω).mapDerivedCategory ≅
      rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Z :=
  (((geometricPointSectionsStalkAdjunction Ω).mapDerivedCategoryAdjunction.comp
      (geometricPointSectionsImageAdjunction Ω h)).ofNatIsoLeft
        (geometricPointSectionsConstantsIso Ω h)).rightAdjointUniq
    (geometricPointSectionsConstantAdjunction Z)

private noncomputable def ordinarySectionsIso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω)) :
    lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h ⋙ geometricPointStalk Ω ≅
      Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) :=
  conjugateIsoEquiv
    ((geometricPointSectionsStalkAdjunction Ω).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h))
    (constantSheafΓAdj Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).symm

private theorem derivedSections_eq (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω)) :
    (geometricPointDerivedSectionsIso Ω h).hom =
      (Functor.isoWhiskerLeft
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor
        (geometricPointStalk Ω).rightDerivedFunctorIsoMapDerivedCategory).inv ≫
      (Functor.rightDerivedFunctorCompIso'
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h)
        (geometricPointStalk Ω) (ordinarySectionsIso Ω h)).hom := by
  let a := upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h
  let := a.preservesKInjectiveComplexes
  rw [geometricPointDerivedSectionsIso, uniq_transport, stalkAdjunction_eq,
    imageAdjunction_eq, constantAdjunction_eq, comp_right_transport,
    conjugate_right_transport]
  congr 1
  symm
  exact Adjunction.rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv a
    (geometricPointSectionsStalkAdjunction Ω)
    (constantSheafΓAdj Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (ordinarySectionsIso Ω h)
    (Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).symm
    (by rfl)

private theorem derivedSections_direct (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω)) :
    (geometricPointDerivedSectionsIso Ω h).hom =
      (Functor.rightDerivedFunctorCompMapDerivedCategoryIso
        (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h)
        (geometricPointStalk Ω)).inv ≫
      (Functor.rightDerivedFunctorNatIso (ordinarySectionsIso Ω h)).hom := by
  rw [derivedSections_eq,
    Functor.rightDerivedFunctorCompMapDerivedCategoryIso_eq_viaRightDerived]
  simp only [Functor.rightDerivedFunctorCompMapDerivedCategoryIsoViaRightDerived,
    Functor.rightDerivedFunctorCompIso', Iso.trans_inv, Iso.trans_hom, Iso.symm_hom,
    Category.assoc]
  rfl

/-- The actual global-section-to-germ map at the identity geometric point. The lift
only reindexes the same pointed-neighbourhood colimit, as in the dependency's stalk.
Source: Stacks Tags 040R and 04JQ
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsGerm
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (G : Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    (Sheaf.Γ (Spec (.of Ω)).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj G ⟶ (geometricPointStalk Ω).obj G :=
  (Sheaf.ΓNatIsoSheafSections (Spec (.of Ω)).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Spec (.of Ω)))).hom.app G ≫
    ((Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{u + 1}).toPresheafFiber
      (Scheme.Etale.mk (𝟙 (Spec (.of Ω))))
      (ULift.up (Over.homMk (𝟙 (Spec (.of Ω))) (Category.comp_id _))) G.obj

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem germ_eq_uniq (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (G : Sheaf (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    geometricPointSectionsGerm Ω G =
      ((constantSheafΓAdj (Spec (.of Ω)).smallEtaleTopology
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).rightAdjointUniq
          (geometricPointSectionsStalkAdjunction Ω)).hom.app G := by
  let Φ := (Scheme.pointSmallEtale (𝟙 (Spec (.of Ω)))).ulift.{u + 1}
  let T := Scheme.Etale.mk (𝟙 (Spec (.of Ω)))
  let t : Φ.fiber.obj T := ULift.up (Over.homMk (𝟙 _) (Category.comp_id _))
  let A := ModuleCat.{u + 1} (ULift.{u + 1} ℤ)
  let J := (Spec (.of Ω)).smallEtaleTopology
  let a := constantSheafΓAdj J A
  let b := geometricPointSectionsStalkAdjunction Ω
  have hu : b.unit = (geometricPointConstantGerm Ω).hom :=
    (Classical.choice (nonempty_geometricPointDerivedConstantsData Ω)).unit_eq
  rw [Adjunction.rightAdjointUniq, conjugateIsoEquiv_apply_hom]
  simp only [conjugateEquiv_apply_app, Iso.refl_hom, NatTrans.id_app]
  change geometricPointSectionsGerm Ω G = b.unit.app _ ≫ _
  rw [hu]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  dsimp only [geometricPointConstantGerm, Iso.symm_hom,
    GrothendieckTopology.Point.constantSheafCompSheafFiberIso,
    NatIso.ofComponents_inv_app, GrothendieckTopology.Point.sheafFiberConstantSheafIso,
    Iso.trans_inv, Iso.symm_inv, asIso_hom]
  change geometricPointSectionsGerm Ω G =
    (Φ.presheafFiberConstIso ((Sheaf.Γ J A).obj G)).inv ≫
      Φ.presheafFiber.map (toSheafify J ((Functor.const _).obj ((Sheaf.Γ J A).obj G))) ≫
      Φ.presheafFiber.map (a.counit.app G).hom
  have hp : (Φ.presheafFiberConstIso ((Sheaf.Γ J A).obj G)).inv =
      Φ.toPresheafFiber T t ((Functor.const _).obj ((Sheaf.Γ J A).obj G)) := by
    apply (cancel_mono (Φ.presheafFiberConstIso ((Sheaf.Γ J A).obj G)).hom).1
    rw [Iso.inv_hom_id, Φ.toPresheafFiber_presheafFiberConstIso_hom]
  rw [hp, Φ.toPresheafFiber_naturality_assoc, Φ.toPresheafFiber_naturality]
  let bT := constantSheafAdj J A
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale (Spec (.of Ω)))
  let q := (a.rightAdjointUniq bT).hom.app G
  have hc := congrArg (fun f ↦ f.hom.app (op T))
    (Adjunction.rightAdjointUniq_hom_app_counit a bT G)
  change geometricPointSectionsGerm Ω G =
    (toSheafify J ((Functor.const _).obj ((Sheaf.Γ J A).obj G))).app (op T) ≫
      (a.counit.app G).hom.app (op T) ≫ Φ.toPresheafFiber T t G.obj
  rw [← hc]
  have hn := congr_app (toSheafify_naturality J ((Functor.const _).map q)) (op T)
  simp only [NatTrans.comp_app, Functor.const_map_app] at hn
  have ht : (toSheafify J ((Functor.const _).obj (G.obj.obj (op T)))).app (op T) ≫
      (bT.counit.app G).hom.app (op T) = 𝟙 _ := by
    have h := bT.right_triangle_components G
    simpa [bT, constantSheafAdj, Adjunction.comp_unit_app,
      constantPresheafAdj] using h
  change q ≫ Φ.toPresheafFiber T t G.obj = _
  change q ≫ Φ.toPresheafFiber T t G.obj =
    (toSheafify J ((Functor.const _).obj ((Sheaf.Γ J A).obj G))).app (op T) ≫
      (sheafifyMap J ((Functor.const _).map q)).app (op T) ≫
      (bT.counit.app G).hom.app (op T) ≫ Φ.toPresheafFiber T t G.obj
  erw [← reassoc_of% hn, reassoc_of% ht]

private theorem ordinarySections_germ
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}}
    (h : Z ⟶ Spec (.of Ω))
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    geometricPointSectionsGerm Ω ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).obj G) ≫
      (ordinarySectionsIso Ω h).hom.app G =
    (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).hom.app G := by
  rw [germ_eq_uniq]
  have he := ordinary_comparison
    (constantSheafΓAdj (Spec (.of Ω)).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (geometricPointSectionsStalkAdjunction Ω)
    (constantSheafAdj (Spec (.of Ω)).smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) terminalIsTerminal)
    (constantSheafΓAdj Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)))
    (constantSheafAdj Z.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) terminalIsTerminal)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h)
    (lowerStarCompSheafSectionsTerminalIso (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h)
  exact congr_app he G

/-- The augmentation identification `H⁰(S_D Rh_* G[0]) ≅ S(h_* G)`.
It uses exactness of the stalk and the canonical zeroth-right-derived comparison.
Source: Stacks Tags 05TD and 04JQ
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsImageH0Iso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω))
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) 0).obj
        (((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor ⋙
          (geometricPointStalk Ω).mapDerivedCategory).obj
            ((DerivedCategory.singleFunctor _ 0).obj G)) ≅
      (geometricPointStalk Ω).obj ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).obj G) :=
  Functor.geometricSectionsExactSingleH0Iso
    (lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h) (geometricPointStalk Ω) G

/-- The canonical augmentation identification `H⁰(RΓ_Z G[0]) ≅ Γ_Z G`.
Source: Stacks Tag 05TD
(blueprint: lem-kun-geometric-point-derived-sections-adjunction). -/
noncomputable def geometricPointSectionsGlobalH0Iso (Z : Scheme.{u})
    (G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) 0).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) Z).obj
          ((DerivedCategory.singleFunctor _ 0).obj G)) ≅
      (Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).obj G :=
  Functor.geometricSectionsSingleH0Iso
    (Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))) G

/-- The natural right-adjoint comparison has the specified counit identity and is inverse
to the global-section-to-germ map in degree zero. Source: Stacks Tag 07A6, the subsequent
pushforward-composition proof, and Tags 04JQ, 0F0F and 05TD
(blueprint: lem-kun-geometric-point-derived-sections-adjunction).

Proof:
1. Compose the normalized constant/stalk adjunction of
   `lem-kun-geometric-point-derived-constants` with the canonical derived image adjunction
   of `def-kun-projection-formula-map`. Its counit is the image counit after inverse image
   of the stalk-equivalence counit.
2. Transport its left adjoint through `lem-kun-pullback-constant`. The transported counit
   is this composite preceded by inverse to the constants comparison.
3. Compare with `def-kun-constant-projection-morphism` by `det-sp-unique-right-adjoint`.
   Its counit equation, precomposed with the constants comparison, is the first clause.
4. The ordinary constant-section and normalized constant/stalk Hom bijections identify
   Hom(A, Γ_s H) with Hom(A, SH). The composite sends a map v to ρ_H after v:
   the constant-section adjunction extends a section by restriction, and the normalized
   point unit sends a constant to its germ. This is the definition of ρ_H from
   `def-weil-pbc-geometric-stalks` and `def-weil-pbc-global-sections-functor`.
   Taking A to be the integer module shows ρ_H bijective, hence invertible.
   Its naturality follows from the germ-map naturality. Finally
   `def-weil-pbc-direct-image` identifies sections of h_*G with sections of G on Z.
5. Compare the transported left-derived adjunctions with the exact-left/right-derived
   adjunctions by their defining unit factorizations. The source library's
   `rightDerivedFunctorCompIso'_hom_eq_conjugateEquiv` identifies β with the derived
   ordinary conjugate of the pullback-of-constants comparison.
6. At the ordinary level, identify the germ with uniqueness of right adjoints using the
   fixed constant-germ unit, naturality of sheafification and the constant/evaluation
   triangle identity. Composition and transport of conjugates show that germ followed
   by the ordinary comparison is `lowerStarCompGlobalSectionsIso`.
7. The defining unit of the exact-right derived composition comparison gives its
   compatibility with `rightDerivedSingleUnit` on G[0]. Apply zeroth homology and
   `rightDerivedSingleUnit_zero` to h_* and Γ. Naturality of the exact stalk/homology
   comparison and its value on single complexes cancel the augmentation identifications.
   This identifies the transported H⁰ map with the ordinary comparison from Step 6,
   and precomposition with the germ gives the second clause.
-/
theorem geometricPoint_derivedSections_adjunction
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] {Z : Scheme.{u}} (h : Z ⟶ Spec (.of Ω)) :
    (∀ E : DerivedCategory (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))),
      (geometricPointSectionsConstantsIso Ω h).hom.app
          (((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor ⋙
            (geometricPointStalk Ω).mapDerivedCategory).obj E) ≫
        (constantSheaf Z.smallEtaleTopology
          (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).mapDerivedCategory.map
            ((geometricPointDerivedSectionsIso Ω h).hom.app E) ≫
        (geometricPointSectionsConstantAdjunction Z).counit.app E =
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).mapDerivedCategory.map
          ((geometricPointSectionsStalkAdjunction Ω).mapDerivedCategoryAdjunction.counit.app
            ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).rightDerivedFunctor.obj E)) ≫
        (geometricPointSectionsImageAdjunction Ω h).counit.app E) ∧
    (∀ G : Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)),
      geometricPointSectionsGerm Ω ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).obj G) ≫
        (geometricPointSectionsImageH0Iso Ω h G).inv ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) 0).map
          ((geometricPointDerivedSectionsIso Ω h).hom.app
            ((DerivedCategory.singleFunctor _ 0).obj G)) ≫
        (geometricPointSectionsGlobalH0Iso Z G).hom =
      (lowerStarCompGlobalSectionsIso (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h).hom.app G) := by
  constructor
  · intro E
    have hc := Adjunction.rightAdjointUniq_hom_app_counit
      (((geometricPointSectionsStalkAdjunction Ω).mapDerivedCategoryAdjunction.comp
        (geometricPointSectionsImageAdjunction Ω h)).ofNatIsoLeft
          (geometricPointSectionsConstantsIso Ω h))
      (geometricPointSectionsConstantAdjunction Z) E
    dsimp only [geometricPointDerivedSectionsIso] at ⊢
    rw [hc]
    simp [Adjunction.ofNatIsoLeft_counit, Adjunction.comp_counit]
  · intro G
    let F := lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) h
    let S := geometricPointStalk Ω
    let H := Sheaf.Γ Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1} ℤ))
    have hu := exact_comparison_single F S H (ordinarySectionsIso Ω h) G
    have hd := congr_app (derivedSections_direct Ω h)
      ((DerivedCategory.singleFunctor _ 0).obj G)
    have hu' := (congrArg (S.mapDerivedCategory.map (F.rightDerivedSingleUnit G) ≫ ·) hd).trans hu
    have hz := comparison_zero_factored F S H (geometricPointDerivedSectionsIso Ω h).hom
      (ordinarySectionsIso Ω h).hom G hu'
    exact (congrArg (geometricPointSectionsGerm Ω (F.obj G) ≫ ·) hz).trans
      (ordinarySections_germ Ω h G)

end AlgebraicGeometry.Etale
