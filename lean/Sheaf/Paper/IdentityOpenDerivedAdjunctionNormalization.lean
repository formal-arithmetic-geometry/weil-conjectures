/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q49
-/
module

public import Sheaf.Paper.IdentityOpenDerivedRestriction
public import Sheaf.Paper.CondensedModuleDerivedPushpull
public import Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
import Mathlib.CategoryTheory.Localization.Predicate
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction

/-!
# Resolution and adjunction normalization over an identity open

Source: Stacks Project, sites-cohomology.tex, Tags 0D6G and 08FI; derived.tex,
Tags 08BJ, 015F, 070Y and 09T5
(blueprint: lem-sfb-identity-open-derived-adjunction-normalization).

The restriction maps are the existing canonical mates. Pullback is derived termwise;
the adjunction is the specified total derived adjunction transported through the canonical
exact-pullback identification. The localized comparison unit uses the existing UnitQ.
-/

@[expose] public noncomputable section

set_option autoImplicit false

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj
open CategoryTheory.MonoidalCategory

private theorem equivalenceKInjective
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    (E : C ≌ D) [E.functor.Additive] [E.inverse.Additive]
    (I : CochainComplex C ℤ) :
    I.IsKInjective ↔ CochainComplex.IsKInjective
      ((E.functor.mapHomologicalComplex (.up ℤ)).obj I) := by
  constructor
  · intro hI
    infer_instance
  · intro hI
    have : CochainComplex.IsKInjective ((E.inverse.mapHomologicalComplex (.up ℤ)).obj
      ((E.functor.mapHomologicalComplex (.up ℤ)).obj I)) := inferInstance
    let e : (E.inverse.mapHomologicalComplex (.up ℤ)).obj
        ((E.functor.mapHomologicalComplex (.up ℤ)).obj I) ≅ I :=
      (E.mapHomologicalComplex (.up ℤ)).unitIso.symm.app I
    exact CochainComplex.isKInjective_of_iso e

set_option backward.defeqAttrib.useBackward true in
private theorem exactAdjunctionTransport
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [MonoidalCategory C] [MonoidalPreadditive C]
    [HasCountableCoproducts C]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    [HasColimitsOfShape ℤ C] [HasExactColimitsOfShape ℤ C]
    [∀ X : C, PreservesColimitsOfShape ℤ ((curriedTensor C).obj X)]
    [∀ X : C, PreservesColimitsOfShape ℤ ((curriedTensor C).flip.obj X)]
    [Abelian.HasFunctorialFlatResolution C]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive] [F.PreservesKFlatQuasiIso]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G) :
    adj.mapDerivedCategoryRightDerivedAdjunction =
      adj.derivedAdjunction.ofNatIsoLeft F.leftDerivedFunctorIsoMapDerivedCategory := by
  refine (adj.mapHomotopyCategory (.up ℤ)).derived_eq_ofNatIsoLeft
    (HomotopyCategory.quasiIso C (.up ℤ)) (HomotopyCategory.quasiIso D (.up ℤ)) _ _ _
    F.leftDerivedFunctorIsoMapDerivedCategory.symm ?_
  ext K
  simp only [Iso.symm_hom, NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [← F.leftDerivedFunctorIsoMapDerivedCategory_hom_fac]
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.inv_hom_id_app_assoc]

-- The localization unit calculation, also used in CompletedTowerPullback.
private theorem exactLeftUnit
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ C) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (adj : F ⊣ G)
    (d : F.mapDerivedCategory ⊣ G.rightDerivedFunctor)
    (hd : adj.mapDerivedCategoryRightDerivedAdjunction = d) (P : CochainComplex C ℤ) :
    d.unit.app (DerivedCategory.Q.obj P) ≫
        G.rightDerivedFunctor.map (F.mapDerivedCategoryFactors.hom.app P) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        G.rightDerivedFunctorUnitQ ((F.mapHomologicalComplex (.up ℤ)).obj P) := by
  subst d
  have hh := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ))
    F.mapDerivedCategoryFactorsh.hom G.rightDerivedFunctorUnit
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  change adj.mapDerivedCategoryRightDerivedAdjunction.unit.app _ ≫ _ = _ at hh
  rw [F.mapDerivedCategoryFactorsh_hom_app,
    Adjunction.mapHomotopyCategory_unit_app_quotient] at hh
  simp only [DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv, Functor.mapHomotopyCategoryFactors] at hh
  erw [F.mapDerivedCategory.map_id, (DerivedCategory.Qh (C := D)).map_id,
    Category.id_comp, Category.comp_id, Category.comp_id] at hh
  dsimp only [Functor.rightDerivedFunctorUnitQ, DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Quotient.lift.isLift_hom,
    Quotient.lift.isLift_inv]
  erw [G.rightDerivedFunctor.map_id, Category.comp_id, Category.id_comp]
  exact hh

private theorem derivedComparisonInv
    {C D E : Type*} [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    (L : C ⥤ D) (V : D ⥤ E) (W : C ⥤ E)
    [L.Additive] [V.Additive] [W.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    [PreservesFiniteLimits W] [PreservesFiniteColimits W]
    (a : L ⋙ V ≅ W) (P : CochainComplex C ℤ) :
    W.mapDerivedCategoryFactors.hom.app P ≫
        DerivedCategory.Q.map ((a.inv.mapHomologicalComplex (.up ℤ)).app P) ≫
        V.mapDerivedCategoryFactors.inv.app ((L.mapHomologicalComplex (.up ℤ)).obj P) ≫
        V.mapDerivedCategory.map (L.mapDerivedCategoryFactors.inv.app P) =
      ((Functor.mapDerivedCategoryCompIso L V).symm ≪≫
        Functor.mapDerivedCategoryNatIso a).inv.app (DerivedCategory.Q.obj P) := by
  have ha := Functor.mapDerivedCategoryNatIso_fac a.symm P
  have hc := Functor.mapDerivedCategoryCompIso_fac L V P
  simp only [Iso.symm_hom] at ha
  simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]
  apply (cancel_mono (V.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app P) ≫
    V.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P))).1
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  erw [V.mapDerivedCategory.map_id, Category.id_comp, Iso.inv_hom_id_app, Category.comp_id]
  have hc' : (Functor.mapDerivedCategoryCompIso L V).hom.app
      (DerivedCategory.Q.obj P) ≫
      V.mapDerivedCategory.map (L.mapDerivedCategoryFactors.hom.app P) ≫
      V.mapDerivedCategoryFactors.hom.app ((L.mapHomologicalComplex (.up ℤ)).obj P) =
      (L ⋙ V).mapDerivedCategoryFactors.hom.app P := by
    simp only [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
      Iso.refl_hom, NatTrans.mapHomologicalComplex_id, NatTrans.id_app] at hc
    erw [DerivedCategory.Q.map_id, Category.comp_id] at hc
    exact hc
  erw [hc']
  exact ha.symm


-- This calculation uses only the localization factors, not the internal sheaf model.
private theorem localizedUnitComparison
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ C) (I : D ⥤ E) (J : C ⥤ E)
    [F.Additive] [G.Additive] [I.Additive] [J.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (adj : F ⊣ G) (d : F.mapDerivedCategory ⊣ G.rightDerivedFunctor)
    (a : F ⋙ I ≅ J) (c : G ⋙ J ⟶ I)
    (r : G.rightDerivedFunctor ⋙ J.mapDerivedCategory ⟶ I.mapDerivedCategory)
    (hη : ∀ P : CochainComplex C ℤ,
      d.unit.app (DerivedCategory.Q.obj P) ≫
          G.rightDerivedFunctor.map (F.mapDerivedCategoryFactors.hom.app P) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
          G.rightDerivedFunctorUnitQ ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (hγ : ∀ P : CochainComplex D ℤ,
      J.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
          J.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ P) ≫
          r.app (DerivedCategory.Q.obj P) ≫ I.mapDerivedCategoryFactors.hom.app P =
        DerivedCategory.Q.map ((c.mapHomologicalComplex (.up ℤ)).app P))
    (hc : ∀ (M : C) (N : D) (t : F.obj M ⟶ N),
      J.map (adj.homEquiv M N t) ≫ c.app N = a.inv.app M ≫ I.map t)
    (P : CochainComplex C ℤ) :
    J.mapDerivedCategory.map (d.unit.app (DerivedCategory.Q.obj P)) ≫
        r.app (F.mapDerivedCategory.obj (DerivedCategory.Q.obj P)) =
      ((Functor.mapDerivedCategoryCompIso F I).symm ≪≫
        Functor.mapDerivedCategoryNatIso a).inv.app (DerivedCategory.Q.obj P) := by
  have hγb (P : CochainComplex D ℤ) :
      J.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ P) ≫
          r.app (DerivedCategory.Q.obj P) =
        J.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
          DerivedCategory.Q.map ((c.mapHomologicalComplex (.up ℤ)).app P) ≫
            I.mapDerivedCategoryFactors.inv.app P := by
    have hh := congrArg (fun f ↦ J.mapDerivedCategoryFactors.hom.app
      ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫ f ≫
        I.mapDerivedCategoryFactors.inv.app P) (hγ P)
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app] at hh
    erw [Category.comp_id] at hh
    exact hh
  have hη' : d.unit.app (DerivedCategory.Q.obj P) =
      (DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        G.rightDerivedFunctorUnitQ ((F.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      G.rightDerivedFunctor.map (F.mapDerivedCategoryFactors.inv.app P) :=
    (Iso.eq_comp_inv (G.rightDerivedFunctor.mapIso
      (F.mapDerivedCategoryFactors.app P))).2 (hη P)
  rw [hη']
  simp only [Functor.map_comp, Category.assoc]
  erw [r.naturality (F.mapDerivedCategoryFactors.inv.app P)]
  erw [reassoc_of% hγb ((F.mapHomologicalComplex (.up ℤ)).obj P)]
  erw [J.mapDerivedCategoryFactors.hom.naturality_assoc
    ((adj.mapHomologicalComplex (.up ℤ)).unit.app P)]
  simp only [Functor.comp_map, Functor.id_obj]
  erw [← DerivedCategory.Q.map_comp_assoc]
  have hcP : (J.mapHomologicalComplex (.up ℤ)).map
        ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      (c.mapHomologicalComplex (.up ℤ)).app ((F.mapHomologicalComplex (.up ℤ)).obj P) =
        (a.inv.mapHomologicalComplex (.up ℤ)).app P := by
    apply HomologicalComplex.hom_ext
    intro n
    change J.map (adj.unit.app (P.X n)) ≫ c.app (F.obj (P.X n)) = a.inv.app (P.X n)
    have hh := hc (P.X n) (F.obj (P.X n)) (𝟙 _)
    rw [Adjunction.homEquiv_unit] at hh
    erw [G.map_id, Category.comp_id, I.map_id, Category.comp_id] at hh
    exact hh
  erw [hcP]
  exact derivedComparisonInv F I J a P


private theorem localizedAdjunctionComparison
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions D]
    (F : C ⥤ D) (G : D ⥤ C) (I : D ⥤ E) (J : C ⥤ E)
    [F.Additive] [G.Additive] [I.Additive] [J.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits I] [PreservesFiniteColimits I]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    (adj : F ⊣ G) (d : F.mapDerivedCategory ⊣ G.rightDerivedFunctor)
    (a : F ⋙ I ≅ J) (c : G ⋙ J ⟶ I)
    (r : G.rightDerivedFunctor ⋙ J.mapDerivedCategory ⟶ I.mapDerivedCategory)
    (hη : ∀ P : CochainComplex C ℤ,
      d.unit.app (DerivedCategory.Q.obj P) ≫
          G.rightDerivedFunctor.map (F.mapDerivedCategoryFactors.hom.app P) =
        DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
          G.rightDerivedFunctorUnitQ ((F.mapHomologicalComplex (.up ℤ)).obj P))
    (hγ : ∀ P : CochainComplex D ℤ,
      J.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
          J.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ P) ≫
          r.app (DerivedCategory.Q.obj P) ≫ I.mapDerivedCategoryFactors.hom.app P =
        DerivedCategory.Q.map ((c.mapHomologicalComplex (.up ℤ)).app P))
    (hc : ∀ (M : C) (N : D) (t : F.obj M ⟶ N),
      J.map (adj.homEquiv M N t) ≫ c.app N = a.inv.app M ≫ I.map t)
    : (∀ A, J.mapDerivedCategory.map (d.unit.app A) ≫
        r.app (F.mapDerivedCategory.obj A) =
      ((Functor.mapDerivedCategoryCompIso F I).symm ≪≫
        Functor.mapDerivedCategoryNatIso a).inv.app A) ∧
      (∀ K, I.mapDerivedCategory.map (d.counit.app K) =
        ((Functor.mapDerivedCategoryCompIso F I).symm ≪≫
          Functor.mapDerivedCategoryNatIso a).hom.app (G.rightDerivedFunctor.obj K) ≫
            r.app K) := by
  let aD := (Functor.mapDerivedCategoryCompIso F I).symm ≪≫
    Functor.mapDerivedCategoryNatIso a
  have hu : ∀ A, J.mapDerivedCategory.map (d.unit.app A) ≫
      r.app (F.mapDerivedCategory.obj A) = aD.inv.app A := by
    let t : J.mapDerivedCategory ⟶ F.mapDerivedCategory ⋙ I.mapDerivedCategory :=
      Functor.whiskerRight d.unit J.mapDerivedCategory ≫
        Functor.whiskerLeft F.mapDerivedCategory r
    have ht : t = aD.inv := Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C (.up ℤ))
        (localizedUnitComparison F G I J adj d a c r hη hγ hc)
    intro A
    exact congrArg (fun x ↦ x.app A) ht
  refine ⟨hu, ?_⟩
  intro K
  apply (cancel_epi (aD.inv.app (G.rightDerivedFunctor.obj K))).1
  rw [Iso.inv_hom_id_app_assoc, ← hu]
  simp only [Category.assoc]
  erw [← r.naturality (d.counit.app K)]
  simp only [Functor.comp_map, ← Category.assoc, ← Functor.map_comp]
  rw [d.right_triangle_components]
  erw [J.mapDerivedCategory.map_id, Category.id_comp]
  rfl

private theorem normalizedRestriction
    {C D E : Type*} [Category* C] [Category* D] [Category* E]
    [Abelian C] [Abelian D] [Abelian E]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
    [Abelian.HasKInjectiveResolutions C]
    (G : C ⥤ D) (J : D ⥤ E) (V : C ⥤ E)
    [G.Additive] [J.Additive] [V.Additive]
    [PreservesFiniteLimits J] [PreservesFiniteColimits J]
    [PreservesFiniteLimits V] [PreservesFiniteColimits V]
    (c : G ⋙ J ⟶ V) (r : G.rightDerivedFunctor ⋙ J.mapDerivedCategory ⟶ V.mapDerivedCategory)
    [IsIso c] [IsIso r]
    (δ : G.mapHomologicalComplex (.up ℤ) ⋙ J.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ G.rightDerivedFunctor ⋙ J.mapDerivedCategory)
    (hδ : ∀ P : CochainComplex C ℤ, δ.app P =
      J.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
        J.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ P))
    (hnorm : ∀ (I : CochainComplex C ℤ) [I.IsKInjective],
      r.app (DerivedCategory.Q.obj I) ≫ V.mapDerivedCategoryFactors.hom.app I =
        J.mapDerivedCategory.map (G.rightDerivedFunctorObjQIso I).hom ≫
          J.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
            DerivedCategory.Q.map ((c.mapHomologicalComplex (.up ℤ)).app I)) :
    (∀ (P I : CochainComplex C ℤ) (s : P ⟶ I) [QuasiIso s] [I.IsKInjective],
      r.app (DerivedCategory.Q.obj P) ≫ V.mapDerivedCategoryFactors.hom.app P =
        J.mapDerivedCategory.map (G.rightDerivedFunctor.map (DerivedCategory.Q.map s) ≫
          (G.rightDerivedFunctorObjQIso I).hom) ≫
          J.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
            DerivedCategory.Q.map ((c.mapHomologicalComplex (.up ℤ)).app I) ≫
              inv (DerivedCategory.Q.map ((V.mapHomologicalComplex (.up ℤ)).map s))) ∧
    (∀ P : CochainComplex C ℤ,
      J.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
        J.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ P) ≫
          r.app (DerivedCategory.Q.obj P) ≫ V.mapDerivedCategoryFactors.hom.app P =
            DerivedCategory.Q.map ((c.mapHomologicalComplex (.up ℤ)).app P)) ∧
    (G.rightDerivedFunctor ⋙ J.mapDerivedCategory).IsRightDerivedFunctor δ
      (HomologicalComplex.quasiIso C (.up ℤ)) := by
  have hformula (P I : CochainComplex
      C ℤ) (s : P ⟶ I) [QuasiIso s] [I.IsKInjective] :
      r.app (DerivedCategory.Q.obj P) ≫
          V.mapDerivedCategoryFactors.hom.app P =
        J.mapDerivedCategory.map
            (G.rightDerivedFunctor.map (DerivedCategory.Q.map s) ≫
              (G.rightDerivedFunctorObjQIso I).hom) ≫
          J.mapDerivedCategoryFactors.hom.app
            ((G.mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex c
              (.up ℤ)).app I) ≫
          inv (DerivedCategory.Q.map ((V.mapHomologicalComplex
            (.up ℤ)).map s)) := by
    apply (cancel_mono (DerivedCategory.Q.map
      ((V.mapHomologicalComplex (.up ℤ)).map s))).1
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id, Functor.map_comp]
    erw [← V.mapDerivedCategoryFactors.hom.naturality s]
    erw [← Category.assoc, ← r.naturality
      (DerivedCategory.Q.map s), Category.assoc, hnorm I]
    rfl
  let τ := δ ≫
    Functor.whiskerLeft DerivedCategory.Q r ≫
      V.mapDerivedCategoryFactors.hom
  let σ := Functor.whiskerRight
    (c.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
  have hγI (I : CochainComplex
      C ℤ) [I.IsKInjective] : τ.app I = σ.app I := by
    change δ.app I ≫ r.app (DerivedCategory.Q.obj I) ≫
      V.mapDerivedCategoryFactors.hom.app I = σ.app I
    rw [hδ I]
    simp only [Category.assoc]
    rw [hnorm I, G.rightDerivedFunctorUnitQ_eq I]
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id]
    rw [J.mapDerivedCategory.map_id]
    simp only [Category.id_comp, Iso.inv_hom_id_app_assoc]
    rfl
  have hγ (P : CochainComplex
      C ℤ) : τ.app P = σ.app P := by
    obtain ⟨I, hI, s, _, hs⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective P
    have : IsIso ((V.mapHomologicalComplex (.up ℤ) ⋙
        DerivedCategory.Q).map s) := by dsimp; infer_instance
    apply (cancel_mono ((V.mapHomologicalComplex (.up ℤ) ⋙
      DerivedCategory.Q).map s)).1
    rw [← τ.naturality s, ← σ.naturality s, hγI I]
    rfl
  have htotal : Functor.IsRightDerivedFunctor
      (G.rightDerivedFunctor ⋙ J.mapDerivedCategory)
      (δ)
        (HomologicalComplex.quasiIso
          C (.up ℤ)) := by
    have : IsIso σ := by
      change IsIso (Functor.whiskerRight
        (NatIso.mapHomologicalComplex
          (asIso c) (.up ℤ)).hom
          DerivedCategory.Q)
      infer_instance
    have : IsIso τ := by
      have heq : τ = σ := by ext P; exact hγ P
      rw [heq]
      infer_instance
    have : IsIso (δ) :=
      IsIso.of_isIso_comp_right _
        (Functor.whiskerLeft DerivedCategory.Q r ≫
          V.mapDerivedCategoryFactors.hom)
    exact Functor.isRightDerivedFunctor_of_inverts _ _
      (asIso (δ)).symm
  have hγ' (P : CochainComplex C ℤ) :
      J.mapDerivedCategoryFactors.inv.app ((G.mapHomologicalComplex (.up ℤ)).obj P) ≫
        J.mapDerivedCategory.map (G.rightDerivedFunctorUnitQ P) ≫
          r.app (DerivedCategory.Q.obj P) ≫ V.mapDerivedCategoryFactors.hom.app P =
            DerivedCategory.Q.map ((c.mapHomologicalComplex (.up ℤ)).app P) := by
    have hh := hγ P
    dsimp only [τ, σ, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app] at hh
    rw [hδ P] at hh
    simpa only [Category.assoc] using hh
  exact ⟨hformula, hγ', htotal⟩

namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

variable (Λ : Sheaf (coherentTopology Profinite.{u}) AddCommGrpCat.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The inverse composition comparison `i^* h^* ≅ j^*`, transported along `hi = j`.
Source: the composition convention in the node and Stacks 09T5
(blueprint: lem-sfb-identity-open-derived-adjunction-normalization). -/
def identityOpenPullbackComparison {U D Z : Scheme.{u}}
    (j : U ⟶ Z) (i : U ⟶ D) (h : D ⟶ Z) (w : i ≫ h = j) :
    upperStar Λ h ⋙ upperStar Λ i ≅ upperStar Λ j :=
  (upperStarComp Λ i h).symm ≪≫ upperStarCongr Λ w

/-- The termwise derived comparison `a_h` with its canonical localization identifications.
Source: Stacks 015F and the composition convention
(blueprint: lem-sfb-identity-open-derived-adjunction-normalization). -/
def identityOpenDerivedPullbackComparison {U D Z : Scheme.{u}}
    (j : U ⟶ Z) (i : U ⟶ D) (h : D ⟶ Z) (w : i ≫ h = j) :
    (upperStar Λ h).mapDerivedCategory ⋙ (upperStar Λ i).mapDerivedCategory ≅
      (upperStar Λ j).mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso (upperStar Λ h) (upperStar Λ i)).symm ≪≫
    Functor.mapDerivedCategoryNatIso (identityOpenPullbackComparison Λ j i h w)

/-- The specified derived adjunction, expressed with the exact termwise pullback.
This transports the published adjunction, including its actual unit and counit.
Source: Stacks 09T5 and sk-def-sfb-module-derived-pushpull
(blueprint: lem-sfb-identity-open-derived-adjunction-normalization). -/
def identityOpenTermwiseDerivedAdjunction {D Z : Scheme.{u}} (h : D ⟶ Z) :
    (upperStar Λ h).mapDerivedCategory ⊣ (lowerStar Λ h).rightDerivedFunctor :=
  (upperStarLowerStarAdjunction Λ h).mapDerivedCategoryRightDerivedAdjunction

/-- The comparison unit on complexes, obtained from the published right-derived unit.
Source: Stacks 070Y, localization of the comparison unit
(blueprint: lem-sfb-identity-open-derived-adjunction-normalization). -/
def identityOpenRightDerivedUnit {D Z : Scheme.{u}} (h : D ⟶ Z) :
    (lowerStar Λ h).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (lowerStar Λ h).rightDerivedFunctor where
  app P := (lowerStar Λ h).rightDerivedFunctorUnitQ P
  naturality _ _ s := (lowerStar Λ h).rightDerivedFunctorUnitQ_naturality s

/-- The localized comparison unit for `j^* Rh_*`, with the exact-functor factorization.
Source: Stacks 015F and 070Y
(blueprint: lem-sfb-identity-open-derived-adjunction-normalization). -/
def identityOpenLocalizedDerivedUnit {U D Z : Scheme.{u}}
    (j : U ⟶ Z) (h : D ⟶ Z) :
    (lowerStar Λ h).mapHomologicalComplex (.up ℤ) ⋙
        (upperStar Λ j).mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ (lowerStar Λ h).rightDerivedFunctor ⋙
        (upperStar Λ j).mapDerivedCategory where
  app P := (upperStar Λ j).mapDerivedCategoryFactors.inv.app
      (((lowerStar Λ h).mapHomologicalComplex (.up ℤ)).obj P) ≫
    (upperStar Λ j).mapDerivedCategory.map ((lowerStar Λ h).rightDerivedFunctorUnitQ P)
  naturality P P' s := by
    dsimp only [Functor.comp_map]
    rw [Category.assoc, ← Functor.map_comp,
      ← (lowerStar Λ h).rightDerivedFunctorUnitQ_naturality s, Functor.map_comp]
    have hh := (upperStar Λ j).mapDerivedCategoryFactors.inv.naturality
      (((lowerStar Λ h).mapHomologicalComplex (.up ℤ)).map s)
    simpa only [Functor.comp_map, Category.assoc] using
      congrArg (fun f ↦ f ≫ (upperStar Λ j).mapDerivedCategory.map
        ((lowerStar Λ h).rightDerivedFunctorUnitQ P')) hh

private theorem identityOpenLocalizedDerivedUnit_app {U D Z : Scheme.{u}}
    (j : U ⟶ Z) (h : D ⟶ Z)
    (P : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1})
      (condensedRingObj Λ D)) ℤ) :
    (identityOpenLocalizedDerivedUnit Λ j h).app P =
      (upperStar Λ j).mapDerivedCategoryFactors.inv.app
          (((lowerStar Λ h).mapHomologicalComplex (.up ℤ)).obj P) ≫
        (upperStar Λ j).mapDerivedCategory.map
          ((lowerStar Λ h).rightDerivedFunctorUnitQ P) := by
  rfl

attribute [local irreducible] identityOpenRestriction identityOpenDerivedRestriction
  upperStar lowerStar upperStarLowerStarAdjunction derivedUpperStarLowerStarAdjunction
  leftDerivedUpperStarIsoMapDerivedCategory identityOpenTermwiseDerivedAdjunction
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors
  Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnitQ
  identityOpenLocalizedDerivedUnit identityOpenRightDerivedUnit
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory instCategoryDerivedCategory
  CategoryTheory.Adjunction.mapDerivedCategoryRightDerivedAdjunction
  Functor.mapDerivedCategoryCompIso Functor.mapDerivedCategoryNatIso
  identityOpenPullbackComparison identityOpenDerivedPullbackComparison
  upperStarComp upperStarCongr
  InternalAbelianSheafModule.sectionModuleEquivalence

set_option linter.unusedVariables false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in

/-- Resolution, comparison-unit and actual derived-adjunction normalization at an identity
open locus. Source: Stacks 0D6G, 08FI, 08BJ, 015F, 070Y and 09T5
(blueprint: lem-sfb-identity-open-derived-adjunction-normalization).

Proof (the six steps recorded in the node):
1. The internal/sectionwise equivalence and its inverse are additive. Each preserves
K-injective complexes as a right adjoint of its exact inverse. The unit isomorphism
of the equivalence on complexes gives reflection.
2. Exact extension by zero is left adjoint to open restriction, so restriction preserves
K-injective complexes. All exact pullbacks descend termwise with their canonical factors.
3. Since U is quasi-compact over k and D is separated over k, i is quasi-compact.
Apply identity_open_derived_restriction. Naturality of its r at Q(s), followed by its
normalization at I, gives the resolution formula after cancellation of Q(i^*s).
4. On a K-injective I the comparison unit is the inverse of rightDerivedFunctorObjQIso I.
Its composite with r is therefore Q(c_I). Both sides are natural on complexes. For arbitrary
P choose a K-injective resolution s:P→I and cancel the invertible Q(i^*s).
5. Step 4 identifies the localized comparison unit, followed by r and the exact-pullback
factor, with the termwise isomorphism Q(c). Thus this unit is invertible. Localization
makes every such pair a total right derived pair.
6. Transport uniqueness of derived adjunctions identifies the specified termwise adjunction
with the existing exact-left derived adjunction. Its unit formula on complexes, step 4,
and hc applied degreewise to identity maps give the unit equation. The canonical composition
and natural-isomorphism factorization formulas identify its right side with a_h inverse.
Localization extends the unit equation to all derived objects. Naturality of r and the
right triangle identity then give the counit equation.
-/
theorem identity_open_derived_adjunction_normalization
    (ℓ : ℕ) [Fact ℓ.Prime] (hΛ : IsLocalizingAdmissibleCoefficient ℓ Λ)
    (k : Type u) [Field k] (p : ℕ) [CharP k p] (hp : 0 < p) (hpℓ : p ≠ ℓ)
    {U D Z : Scheme.{u}} [U.Over (Spec (.of k))] [D.Over (Spec (.of k))]
    [Z.Over (Spec (.of k))]
    [IsSeparated (U ↘ Spec (.of k))] [LocallyOfFiniteType (U ↘ Spec (.of k))]
    [QuasiCompact (U ↘ Spec (.of k))]
    [IsSeparated (D ↘ Spec (.of k))] [LocallyOfFiniteType (D ↘ Spec (.of k))]
    [QuasiCompact (D ↘ Spec (.of k))]
    [IsSeparated (Z ↘ Spec (.of k))] [LocallyOfFiniteType (Z ↘ Spec (.of k))]
    [QuasiCompact (Z ↘ Spec (.of k))]
    (j : U ⟶ Z) (i : U ⟶ D) (h : D ⟶ Z)
    [j.IsOver (Spec (.of k))] [i.IsOver (Spec (.of k))] [h.IsOver (Spec (.of k))]
    [IsOpenImmersion j] [QuasiCompact j] [IsOpenImmersion i]
    (w : i ≫ h = j) (hw : h ⁻¹' Set.range j = Set.range i)
    (hc : ∀ (M : Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ Z))
      (N : Mod (Sheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ D)) (t : (upperStar Λ h).obj M ⟶ N),
      (upperStar Λ j).map ((upperStarLowerStarAdjunction Λ h).homEquiv M N t) ≫
          (identityOpenRestriction Λ j i h w).app N =
        (identityOpenPullbackComparison Λ j i h w).inv.app M ≫
          (upperStar Λ i).map t) :
    (∀ (T : Scheme.{u})
      (I : CochainComplex (Mod (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ T)) ℤ),
      I.IsKInjective ↔
        CochainComplex.IsKInjective
          (((InternalModuleOperations.equivalence Λ T).functor.mapHomologicalComplex
            (.up ℤ)).obj I)) ∧
    (∀ (I : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ D)) ℤ) [I.IsKInjective],
      CochainComplex.IsKInjective
        (((upperStar Λ i).mapHomologicalComplex (.up ℤ)).obj I)) ∧
    (∀ (P I : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ D)) ℤ) (s : P ⟶ I) [QuasiIso s] [I.IsKInjective],
      (identityOpenDerivedRestriction Λ j i h w).app (DerivedCategory.Q.obj P) ≫
          (upperStar Λ i).mapDerivedCategoryFactors.hom.app P =
        (upperStar Λ j).mapDerivedCategory.map
            ((lowerStar Λ h).rightDerivedFunctor.map (DerivedCategory.Q.map s) ≫
              ((lowerStar Λ h).rightDerivedFunctorObjQIso I).hom) ≫
          (upperStar Λ j).mapDerivedCategoryFactors.hom.app
            (((lowerStar Λ h).mapHomologicalComplex (.up ℤ)).obj I) ≫
          DerivedCategory.Q.map
            ((NatTrans.mapHomologicalComplex (identityOpenRestriction Λ j i h w)
              (.up ℤ)).app I) ≫
          inv (DerivedCategory.Q.map (((upperStar Λ i).mapHomologicalComplex
            (.up ℤ)).map s))) ∧
    (∀ P : CochainComplex
        (Mod (Sheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ D)) ℤ,
      (upperStar Λ j).mapDerivedCategoryFactors.inv.app
          (((lowerStar Λ h).mapHomologicalComplex (.up ℤ)).obj P) ≫
          (upperStar Λ j).mapDerivedCategory.map
            ((lowerStar Λ h).rightDerivedFunctorUnitQ P) ≫
          (identityOpenDerivedRestriction Λ j i h w).app (DerivedCategory.Q.obj P) ≫
          (upperStar Λ i).mapDerivedCategoryFactors.hom.app P =
        DerivedCategory.Q.map
          ((NatTrans.mapHomologicalComplex (identityOpenRestriction Λ j i h w)
            (.up ℤ)).app P)) ∧
    Functor.IsRightDerivedFunctor
      ((lowerStar Λ h).rightDerivedFunctor ⋙ (upperStar Λ j).mapDerivedCategory)
      (identityOpenLocalizedDerivedUnit Λ j h)
        (HomologicalComplex.quasiIso
          (Mod (Sheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1})
            (condensedRingObj Λ D)) (.up ℤ)) ∧
    (∀ A : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology Z) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ Z)),
      (upperStar Λ j).mapDerivedCategory.map
          ((identityOpenTermwiseDerivedAdjunction Λ h).unit.app A) ≫
          (identityOpenDerivedRestriction Λ j i h w).app
            ((upperStar Λ h).mapDerivedCategory.obj A) =
        (identityOpenDerivedPullbackComparison Λ j i h w).inv.app A) ∧
    (∀ K : DerivedCategory
        (Mod (Sheaf (Scheme.ProEt.topology D) AddCommGrpCat.{u + 1})
          (condensedRingObj Λ D)),
      (upperStar Λ i).mapDerivedCategory.map
          ((identityOpenTermwiseDerivedAdjunction Λ h).counit.app K) =
        (identityOpenDerivedPullbackComparison Λ j i h w).hom.app
            ((lowerStar Λ h).rightDerivedFunctor.obj K) ≫
          (identityOpenDerivedRestriction Λ j i h w).app K) := by
  clear hp hpℓ
  let : Abelian.HasKInjectiveResolutions
      (Mod (Sheaf (Scheme.ProEt.topology D) Ab.{u + 1}) (condensedRingObj Λ D)) :=
    Abelian.hasKInjectiveResolutions_of_isGrothendieckAbelian
  have hE := (InternalModuleOperations.internal_module_operations_transport Λ).1
  have hK (T : Scheme.{u}) (I : CochainComplex
      (Mod (Sheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1})
        (condensedRingObj Λ T)) ℤ) :
      I.IsKInjective ↔ CochainComplex.IsKInjective
        (((InternalModuleOperations.equivalence Λ T).functor.mapHomologicalComplex
          (.up ℤ)).obj I) := by
    let E := InternalModuleOperations.equivalence Λ T
    have : E.functor.Additive := (hE T).1
    have : E.inverse.Additive := (hE T).2.1
    exact equivalenceKInjective E I
  have hKi : (upperStar Λ i).PreservesKInjectiveComplexes :=
    (openImmersionLowerShriekUpperStarAdjunction Λ i).preservesKInjectiveComplexes
  have : QuasiCompact (i ≫ (D ↘ Spec (.of k))) := by
    rw [comp_over]
    infer_instance
  have : QuasiCompact i := QuasiCompact.of_comp i (D ↘ Spec (.of k))
  have hr := identity_open_derived_restriction Λ ℓ hΛ j i h w hw
  rcases hr with ⟨hriso, hciso, hsectionIso, hsection, hnorm⟩
  have hd : (upperStarLowerStarAdjunction Λ h).mapDerivedCategoryRightDerivedAdjunction =
      identityOpenTermwiseDerivedAdjunction Λ h := by
    unfold identityOpenTermwiseDerivedAdjunction
    rfl
  have : IsIso (identityOpenDerivedRestriction Λ j i h w) := hriso
  have : IsIso (identityOpenRestriction Λ j i h w) := hciso
  have hn := by
    set_option backward.isDefEq.respectTransparency true in
    exact normalizedRestriction (lowerStar Λ h) (upperStar Λ j) (upperStar Λ i)
      (identityOpenRestriction Λ j i h w) (identityOpenDerivedRestriction Λ j i h w)
      (identityOpenLocalizedDerivedUnit Λ j h)
      (identityOpenLocalizedDerivedUnit_app Λ j h) hnorm
  rcases hn with ⟨hformula, hγ', htotal⟩
  have hu := localizedAdjunctionComparison (upperStar Λ h) (lowerStar Λ h)
    (upperStar Λ i) (upperStar Λ j) (upperStarLowerStarAdjunction Λ h)
    (identityOpenTermwiseDerivedAdjunction Λ h)
    (identityOpenPullbackComparison Λ j i h w) (identityOpenRestriction Λ j i h w)
    (identityOpenDerivedRestriction Λ j i h w)
    (exactLeftUnit (upperStar Λ h) (lowerStar Λ h) (upperStarLowerStarAdjunction Λ h)
      (identityOpenTermwiseDerivedAdjunction Λ h) hd) hγ' hc
  rcases hu with ⟨hu, hv⟩
  have hpair :
      (∀ A, (upperStar Λ j).mapDerivedCategory.map
          ((identityOpenTermwiseDerivedAdjunction Λ h).unit.app A) ≫
          (identityOpenDerivedRestriction Λ j i h w).app
            ((upperStar Λ h).mapDerivedCategory.obj A) =
        (identityOpenDerivedPullbackComparison Λ j i h w).inv.app A) ∧
      (∀ K, (upperStar Λ i).mapDerivedCategory.map
          ((identityOpenTermwiseDerivedAdjunction Λ h).counit.app K) =
        (identityOpenDerivedPullbackComparison Λ j i h w).hom.app
            ((lowerStar Λ h).rightDerivedFunctor.obj K) ≫
          (identityOpenDerivedRestriction Λ j i h w).app K) := by
    unfold identityOpenDerivedPullbackComparison
    exact ⟨hu, hv⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hK
  · intro I hI
    infer_instance
  · exact hformula
  · exact hγ'
  · exact htotal
  · intro A
    exact hpair.1 A
  · intro K
    exact hpair.2 K

end AlgebraicGeometry.ProEtale.CondensedRing
