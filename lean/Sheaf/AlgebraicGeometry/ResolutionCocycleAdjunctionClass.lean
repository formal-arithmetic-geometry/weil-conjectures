module

public import Sheaf.AlgebraicGeometry.RawRestrictedResolutionCocycle
import Sheaf.AlgebraicGeometry.ResolutionSectionCocycleSheafification
import Sheaf.AlgebraicGeometry.ResolutionShiftedUnitHomology
import all Sheaf.CategoryTheory.OrdinaryComplexAdjunct
import all Sheaf.CategoryTheory.DerivedAdjunctionSingleZero
import all Mathlib.Logic.Small.Defs

/-! # The class of a resolution section cocycle

Source: Stacks Project, Tags 072W, 0DVC and 09T5.
(blueprint: lem-weil-pbc-resolution-cocycle-adjunction-class).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
set_option backward.defeqAttrib.useBackward true
attribute [local instance] RawRestrictedComparison.etaleComposition
  RawRestrictedComparison.etaleIdentities RawRestrictedComparison.etalePullbacks
  RawRestrictedComparison.etaleBaseChange RawRestrictedComparison.sheafifyInstance
  RawRestrictedComparison.weakSheafifyInstance

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_adjunct_chain
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)
    (A : C) (J : CochainComplex.Plus D)
    (c : (CochainComplex.singleFunctor D 0).obj (L.obj A) ⟶ J.obj) :
    adj.derivedPlus.homEquiv _ _
        ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫
          DerivedCategory.Plus.ι.preimage
            (X := (DerivedCategory.Plus.singleFunctor D 0).obj (L.obj A))
            (Y := DerivedCategory.Plus.Q.obj J) (DerivedCategory.Q.map c)) =
      (DerivedCategory.Plus.singleFunctor C 0).map (adj.unit.app A) ≫
        (R.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 (L.obj A)).inv ≫
        DerivedCategory.Plus.Qh.map
          (R.mapHomotopyCategoryPlus.map
            ((HomotopyCategory.Plus.quotient D).map
              (ObjectProperty.homMk c :
                (⟨(CochainComplex.singleFunctor D 0).obj (L.obj A),
                  0, inferInstance⟩ : CochainComplex.Plus D) ⟶ J))) ≫
        R.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient D).obj J) := by
  rw [adj.derivedPlus.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [CategoryTheory.Adjunction.unit_single]
  let S : CochainComplex.Plus D :=
    ⟨(CochainComplex.singleFunctor D 0).obj (L.obj A), 0, inferInstance⟩
  let g : S ⟶ J := ObjectProperty.homMk c
  have hn := R.rightDerivedFunctorPlusUnit.naturality
    ((HomotopyCategory.Plus.quotient D).map g)
  dsimp only [Functor.comp_map] at hn
  have he : (DerivedCategory.Plus.ι.preimageIso
      (X := (DerivedCategory.Plus.singleFunctor D 0).obj (L.obj A))
      (Y := DerivedCategory.Plus.Qh.obj
        ((HomotopyCategory.Plus.singleFunctor D 0).obj (L.obj A)))
      ((DerivedCategory.singleFunctorIsoCompQ D 0).app (L.obj A) ≪≫
        (DerivedCategory.quotientCompQhIso D).symm.app _)).inv = 𝟙 _ := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [Functor.preimageIso_inv, Functor.map_preimage, Iso.trans_inv]
    change 𝟙 _ ≫ 𝟙 _ = 𝟙 _
    exact Category.id_comp _
  simp only [Functor.rightDerivedPlusSingleUnit, he, Category.assoc]
  have hqc : DerivedCategory.Plus.ι.preimage
      (X := (DerivedCategory.Plus.singleFunctor D 0).obj (L.obj A))
      (Y := DerivedCategory.Plus.Q.obj J) (DerivedCategory.Q.map c) =
      DerivedCategory.Plus.Qh.map ((HomotopyCategory.Plus.quotient D).map g) := by
    apply DerivedCategory.Plus.ι.map_injective
    rw [Functor.map_preimage]
    rfl
  rw [hqc]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  erw [← hn]

private theorem localized_termwise_adjunct
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)
    (A : C) (J : CochainComplex.Plus D)
    (c : (CochainComplex.singleFunctor D 0).obj (L.obj A) ⟶ J.obj) :
    let S₀ : CochainComplex.Plus C :=
      ⟨(CochainComplex.singleFunctor C 0).obj A, 0, inferInstance⟩
    let d : (CochainComplex.singleFunctor C 0).obj A ⟶
        (R.mapHomologicalComplex (.up ℤ)).obj J.obj :=
      ordinaryComplexAdjunct L R adj A J.obj c
    adj.derivedPlus.homEquiv _ _
        ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫
          DerivedCategory.Plus.ι.preimage
            (X := (DerivedCategory.Plus.singleFunctor D 0).obj (L.obj A))
            (Y := DerivedCategory.Plus.Q.obj J) (DerivedCategory.Q.map c)) =
      DerivedCategory.Plus.Q.map
        (ObjectProperty.homMk d : S₀ ⟶ R.mapCochainComplexPlus.obj J) ≫
        R.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient D).obj J) := by
  intro S₀ d
  rw [derived_adjunct_chain]
  let T₀ : CochainComplex.Plus D :=
    ⟨(CochainComplex.singleFunctor D 0).obj (L.obj A), 0, inferInstance⟩
  let gc : T₀ ⟶ J := ObjectProperty.homMk c
  have hmap :
      (DerivedCategory.Plus.singleFunctor C 0).map (adj.unit.app A) ≫
        (R.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 _).inv ≫
        DerivedCategory.Plus.Qh.map
          (R.mapHomotopyCategoryPlus.map ((HomotopyCategory.Plus.quotient D).map gc)) =
      DerivedCategory.Plus.Q.map
        (ObjectProperty.homMk d : S₀ ⟶ R.mapCochainComplexPlus.obj J) := by
    apply DerivedCategory.Plus.ι.map_injective
    simp only [Functor.map_comp, Functor.mapHomotopyCategoryPlusSingleFunctorQhObjIso,
      Functor.preimageIso_inv, Functor.map_preimage, Functor.mapIso_inv]
    change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ ≫
      DerivedCategory.Q.map _ = DerivedCategory.Q.map d
    rw [← Functor.map_comp, ← Functor.map_comp]
    simp only [d, ordinaryComplexAdjunct_eq]
    rfl
  simpa only [Category.assoc] using congrArg
    (fun k ↦ k ≫ R.rightDerivedFunctorPlusUnit.app
      ((HomotopyCategory.Plus.quotient D).obj J)) hmap

private theorem single_homology_comparison
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] (A : C) :
    let S₀ : CochainComplex.Plus C :=
      ⟨(CochainComplex.singleFunctor C 0).obj A, 0, inferInstance⟩;
      (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app A ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso S₀ 0).hom =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 A).inv := by
    intro S₀
    simp only [Functor.id_obj, Functor.comp_obj,
      DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso,
      DerivedCategory.singleFunctorCompHomologyFunctorIso,
      HomologicalComplex.homologyFunctorSingleIso, Iso.trans_inv,
      Functor.isoWhiskerLeft_inv, Category.assoc, Functor.isoWhiskerRight_inv,
      Functor.mapIso_inv, SingleFunctors.evaluation_map, NatTrans.comp_app,
      NatIso.ofComponents_inv_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Category.id_comp,
      DerivedCategory.Plus.homologyFunctorObjQIso, ObjectProperty.ι_obj,
      Iso.trans_hom, Iso.app_hom, S₀]
    rw [DerivedCategory.singleFunctorsPostcompQIso_inv_hom]
    change _ ≫ _ ≫ (DerivedCategory.homologyFunctor _ 0).map (𝟙 _) ≫
      (DerivedCategory.homologyFunctorFactorsh _ 0).hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj S₀.obj) ≫ _ = _
    rw [CategoryTheory.Functor.map_id, Category.id_comp,
      DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj]
    have hq : (DerivedCategory.quotientCompQhIso _).hom.app S₀.obj = 𝟙 _ := rfl
    rw [hq, CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [Category.assoc]
    change _ ≫ (DerivedCategory.homologyFunctorFactors _ 0).inv.app S₀.obj ≫
      (DerivedCategory.homologyFunctorFactors _ 0).hom.app S₀.obj ≫
      (HomotopyCategory.homologyFunctorFactors _ (.up ℤ) 0).inv.app S₀.obj ≫
      (HomotopyCategory.homologyFunctorFactors _ (.up ℤ) 0).hom.app S₀.obj = _
    simp

private theorem adjunct_homology
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)
    (A : C) (J : CochainComplex.Plus D)
    (c : (CochainComplex.singleFunctor D 0).obj (L.obj A) ⟶ J.obj)
    {T : DerivedCategory.Plus D} (a : DerivedCategory.Plus.Q.obj J ⟶ T) :
    let d : (CochainComplex.singleFunctor C 0).obj A ⟶
        (R.mapHomologicalComplex (.up ℤ)).obj J.obj :=
      ordinaryComplexAdjunct L R adj A J.obj c
    let H := DerivedCategory.Plus.homologyFunctor C 0
    (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app A ≫
      H.map (adj.derivedPlus.homEquiv _ _
        ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫
          (DerivedCategory.Plus.ι.preimage
            (X := (DerivedCategory.Plus.singleFunctor D 0).obj (L.obj A))
            (Y := DerivedCategory.Plus.Q.obj J) (DerivedCategory.Q.map c) ≫ a))) =
    (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 A).inv ≫
      HomologicalComplex.homologyMap d 0 ≫
      (DerivedCategory.Plus.homologyFunctorObjQIso (R.mapCochainComplexPlus.obj J) 0).inv ≫
      H.map (R.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient D).obj J)) ≫
      H.map (R.rightDerivedFunctorPlus.map a) := by
  intro d H
  let S₀ : CochainComplex.Plus C :=
    ⟨(CochainComplex.singleFunctor C 0).obj A, 0, inferInstance⟩
  let d' : S₀ ⟶ R.mapCochainComplexPlus.obj J := ObjectProperty.homMk d
  have hd := localized_termwise_adjunct L R adj A J c
  dsimp only at hd
  have hm : (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app A ≫
      H.map (DerivedCategory.Plus.Q.map d') =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 A).inv ≫
        HomologicalComplex.homologyMap d 0 ≫
        (DerivedCategory.Plus.homologyFunctorObjQIso (R.mapCochainComplexPlus.obj J) 0).inv := by
    apply (cancel_mono
      (DerivedCategory.Plus.homologyFunctorObjQIso (R.mapCochainComplexPlus.obj J) 0).hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    erw [DerivedCategory.Plus.homologyFunctorObjQIso_hom_naturality d' 0]
    simpa only [Category.assoc, S₀, d', ObjectProperty.homMk] using
      congrArg (fun k ↦ k ≫ HomologicalComplex.homologyMap d 0)
        (single_homology_comparison A)
  rw [← Category.assoc _ _ a, Adjunction.homEquiv_naturality_right]
  rw [hd]
  simp only [Functor.map_comp, Category.assoc]
  simpa only [Category.assoc, d', d, S₀] using congrArg (fun k ↦ k ≫
    H.map (R.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient D).obj J)) ≫
    H.map (R.rightDerivedFunctorPlus.map a)) hm

private theorem combine_tail
    {C : Type*} [Category C] {A B D E G J M W : C}
    (s : A ⟶ B) (x : B ⟶ M) (y : A ⟶ D) (z : D ⟶ E)
    (r₁ : E ⟶ G) (r₂ : G ⟶ J) (r₃ : J ⟶ M) (v : M ⟶ W) (t : E ⟶ W)
    (h : s ≫ x = y ≫ z ≫ r₁ ≫ r₂ ≫ r₃)
    (ht : r₁ ≫ r₂ ≫ r₃ ≫ v = t) : s ≫ x ≫ v = y ≫ z ≫ t := by
  rw [← Category.assoc, h]
  simp only [Category.assoc]
  rw [ht]

private theorem adjunct_homology_finish
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
    (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)
    (A : C) (J : CochainComplex.Plus D)
    (c : (CochainComplex.singleFunctor D 0).obj (L.obj A) ⟶ J.obj)
    {T : DerivedCategory.Plus D} (a : DerivedCategory.Plus.Q.obj J ⟶ T)
    {W : C}
    (v : (DerivedCategory.Plus.homologyFunctor C 0).obj
      (R.rightDerivedFunctorPlus.obj T) ⟶ W)
    (t : ((R.mapHomologicalComplex (.up ℤ)).obj J.obj).homology 0 ⟶ W)
    (ht : (DerivedCategory.Plus.homologyFunctorObjQIso
          (R.mapCochainComplexPlus.obj J) 0).inv ≫
        (DerivedCategory.Plus.homologyFunctor C 0).map
          (R.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient D).obj J)) ≫
        (DerivedCategory.Plus.homologyFunctor C 0).map
          (R.rightDerivedFunctorPlus.map a) ≫ v = t) :
    let d : (CochainComplex.singleFunctor C 0).obj A ⟶
        (R.mapHomologicalComplex (.up ℤ)).obj J.obj :=
      ordinaryComplexAdjunct L R adj A J.obj c
    (DerivedCategory.Plus.singleFunctorCompHomologyFunctorIso 0).inv.app A ≫
      (DerivedCategory.Plus.homologyFunctor C 0).map (adj.derivedPlus.homEquiv _ _
        ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app A ≫
          (DerivedCategory.Plus.ι.preimage
            (X := (DerivedCategory.Plus.singleFunctor D 0).obj (L.obj A))
            (Y := DerivedCategory.Plus.Q.obj J) (DerivedCategory.Q.map c) ≫ a))) ≫ v =
      (HomologicalComplex.singleObjHomologySelfIso (.up ℤ) 0 A).inv ≫
        HomologicalComplex.homologyMap d 0 ≫ t := by
  intro d
  have h := adjunct_homology L R adj A J c a
  dsimp only at h
  exact combine_tail _ _ _ _ _ _ _ _ _ h ht

private theorem evaluated_comparison
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {A B : Sheaf J AddCommGrpCat} (m n : A ⟶ B) (h : m = n)
    (V : Cᵒᵖ) (e : A.obj.obj V) {x : B.obj.obj V}
    (hx : x = (n.hom.app V).hom e) : x = (m.hom.app V).hom e := by
  exact hx.trans (congrArg (fun f : A ⟶ B ↦ (f.hom.app V).hom e) h.symm)

attribute [local irreducible] normalizationResolutionClass normalizationResolutionCocycleIso
  RawRestrictedComparison.chainEvaluation abelianHigherDirectImageClass

/-- The sheafified section cocycle is the derived-adjunction class.
Source: Stacks Project, Tag 072W (lemma-higher-direct-images), and derived.tex,
Tags 0DVC and 09T5 (pre-derived and derived adjoint functors).
(blueprint: lem-weil-pbc-resolution-cocycle-adjunction-class).

Proof: Form the ordinary termwise adjunct d of c. The single-object unit identity
of DerivedAdjunctionSingleZero and naturality of rightDerivedFunctorPlusUnit show
that the derived adjunct of Q(c) is Q(d) followed by that unit. The private lemma
localized_termwise_adjunct proves this identity by applying the faithful inclusion
and composing the three localized chain maps. Applying zeroth homology and
homologyFunctorObjQIso naturality identifies the source factor with the inverse
single-object homology comparison and H^0(d). Naturality of derived adjunction
moves the inverse shifted augmentation to the right. The separate
resolution_shifted_unit_homology calculation identifies that tail with the
termwise shift, homology shift and inverse classical resolution comparisons.

The independent resolution_section_cocycle_sheafification calculation says that
the sheafified section cocycle is evaluation of H^0(d), the complex shift and the
two inverse classical resolution comparisons at the represented identity generator.
Evaluate the previous morphism equality at the same generator.
Expansion of normalizationResolutionClass and abelianHigherDirectImageClass,
and functoriality of evaluation, give the asserted equality. The two imported
calculations cover q=0, zero maps and empty charts as well. -/
theorem resolutionCocycle_adjunction_class {X S : Scheme.{u}} (f : X ⟶ S)
    (q : ℕ) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (I : InjectiveResolution F) (V : S.Etale)
    (c : (CochainComplex.singleFunctor _ 0).obj
      ((upperStar AddCommGrpCat.{u + 1} f).obj (RawRestrictedComparison.freeSheaf S V)) ⟶
        (normalizationShiftedResolution F I q).obj) :
    (normalizationResolutionClass f q F I).app (op V)
      ((normalizationResolutionCocycleIso f q F I V).hom
        (RawRestrictedComparison.chainEvaluation f V _ c)) =
      abelianHigherDirectImageClass f q F V
        (DerivedCategory.Plus.ι.preimage
          (X := (DerivedCategory.Plus.singleFunctor _ 0).obj
            ((upperStar AddCommGrpCat.{u + 1} f).obj (RawRestrictedComparison.freeSheaf S V)))
          (Y := DerivedCategory.Plus.Q.obj (normalizationShiftedResolution F I q))
          (DerivedCategory.Q.map c) ≫
          (normalizationShiftedAugmentation F I q).inv)  := by
  let R := lowerStar AddCommGrpCat.{u + 1} f
  let A := RawRestrictedComparison.freeSheaf S V
  let J := normalizationShiftedResolution F I q
  have hunit := resolution_shifted_unit_homology f q F I
  dsimp only at hunit
  have hc := adjunct_homology_finish (upperStar AddCommGrpCat.{u + 1} f) R
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f) A J c
    (normalizationShiftedAugmentation F I q).inv
    (abelianComparisonShift f q F).hom
    (resolutionCocycleHomologyTail f q F I) hunit
  dsimp only at hc
  have hs := resolution_section_cocycle_sheafification f q F I V c
  dsimp only at hs
  have hout := evaluated_comparison _ _ hc (op V)
    (((toSheafify S.smallEtaleTopology
      (uliftYoneda.{u + 1}.obj V ⋙ AddCommGrpCat.free)).app (op V)).hom
        (FreeAbelianGroup.of (ULift.up (𝟙 V)))) hs
  unfold abelianHigherDirectImageClass
  simpa only [] using! hout

end AlgebraicGeometry.Etale
