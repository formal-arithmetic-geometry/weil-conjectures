/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q98
-/
module

public import Sheaf.AlgebraicGeometry.SupportTriangleCompatibility
public import Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.ClosedImmersion
import Sheaf.AlgebraicGeometry.SupportTriangleConstruction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Injective

/-!
# Localization for the ambient bounded-below exceptional inverse image

Source: blueprint main-20261015, sec-six-functors-basics/sk-prop-a1-kummer,
`lem-pur-support-localization-triangle` (blueprint: lem-pur-support-localization-triangle).
The categories are all constant-coefficient module sheaves, as in
`def-pur-flasque-support`; there is no constructibility condition. The right derived
functors below are the existing ordinary injective-derived functors on `D⁺`.
-/

@[expose] public section

set_option autoImplicit false


universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local irreducible] Functor.rightDerivedFunctor
  Functor.rightDerivedFunctorPlus Functor.rightDerivedFunctorPlusCompatibility
  Functor.mapDerivedCategory
  Adjunction.derivedPlus

attribute [local irreducible] DerivedCategory.Q DerivedCategory.Qh
  DerivedCategory.quotientCompQhIso

section GenericModelComparisons
universe v
variable {C : Type u} {D : Type v} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

/-- Transport a model isomorphism through an exact functor, with the fixed derived
factorization. Source: blueprint lem-pur-support-localization-triangle, step 5
(blueprint: lem-pur-support-localization-triangle). -/
noncomputable def CategoryTheory.Functor.supportExactModelComparison
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (I : CochainComplex C ℤ) (K : DerivedCategory.Plus C)
    (e : DerivedCategory.Q.obj I ≅ K.obj) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ≅
      (F.mapDerivedCategoryPlus.obj K).obj :=
  (F.mapDerivedCategoryFactors.app I).symm ≪≫ F.mapDerivedCategory.mapIso e ≪≫
    (F.mapDerivedCategoryPlusCompatibility.app K).symm

/-- Compute a right derived functor on a K-injective model with its fixed unit.
Source: blueprint lem-pur-support-localization-triangle, steps 1 and 4
(blueprint: lem-pur-support-localization-triangle). -/
noncomputable def CategoryTheory.Functor.supportRightModelComparison
    [EnoughInjectives C] [CategoryTheory.Abelian.HasKInjectiveResolutions C]
    (F : C ⥤ D) [F.Additive] (I : CochainComplex C ℤ) [I.IsKInjective]
    (K : DerivedCategory.Plus C) (e : DerivedCategory.Q.obj I ≅ K.obj) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj I) ≅
      (F.rightDerivedFunctorPlus.obj K).obj :=
  (F.rightDerivedFunctorObjQIso I).symm ≪≫ F.rightDerivedFunctor.mapIso e ≪≫
    (F.rightDerivedFunctorPlusCompatibility.app K).symm

end GenericModelComparisons

section ExplicitTriangle
variable {C : Type u} [Category C] [Abelian C] [HasDerivedCategory C]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem explicitSupportTriangle_map
    {S T : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) (hT : T.ShortExact)
    (hqS : IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)))
    (hqT : IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex T)))
    (f : S ⟶ T) :
    ∃ t : AlgebraicGeometry.ProEtale.supportSequenceTriangle S hqS ⟶
      AlgebraicGeometry.ProEtale.supportSequenceTriangle T hqT,
      t.hom₁ = DerivedCategory.Q.map f.τ₁ ∧
      t.hom₂ = DerivedCategory.Q.map f.τ₂ ∧
      t.hom₃ = DerivedCategory.Q.map f.τ₃ :=
  ⟨DerivedCategory.triangleOfSES.map hS hT f, rfl, rfl, rfl⟩

end ExplicitTriangle

section ModelComparison
universe v
variable {C : Type u} {D : Type v} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  [CategoryTheory.Abelian.HasKInjectiveResolutions C]

omit [CategoryTheory.Abelian.HasKInjectiveResolutions C] in
private theorem plus_injective_representative (K : DerivedCategory.Plus C) :
    ∃ I : CochainComplex.Plus C, (∀ n : ℤ, Injective (I.obj.X n)) ∧
      Nonempty (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj I) ≅ K) := by
  obtain ⟨n, hn⟩ := K.property
  have : K.IsGE n := (K.isGE_ι_obj_iff n).mp hn
  obtain ⟨L, hL, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
  let I := ((InjectiveObject.ι _).mapCochainComplexPlus.obj L)
  exact ⟨I, fun m ↦ inferInstanceAs (Injective ((InjectiveObject.ι _).obj (L.obj.X m))),
    ⟨e⟩⟩

private theorem plus_unit_compare (F : C ⥤ D) [F.Additive]
    (H : HomotopyCategory.Plus C) :
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app H) ≫
      F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj H) =
    F.rightDerivedFunctorUnit.app H.obj := by
  simpa [Functor.rightDerivedFunctorPlusCompatibility,
    Functor.rightDerivedUnique, Functor.rightDerivedNatIso,
    Functor.rightDerivedFunctorPlusιUnit, Functor.ιRightDerivedFunctorUnit]
    using Functor.rightDerivedNatTrans_app
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
      (DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor)
      F.rightDerivedFunctorPlusιUnit F.ιRightDerivedFunctorUnit
      (HomotopyCategory.Plus.quasiIso C)
      (𝟙 (F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι)) H

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem model_compare (F : C ⥤ D) [F.Additive]
    (J : CochainComplex.Plus C) [J.obj.IsKInjective]
    (K : DerivedCategory.Plus C)
    (e : DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj J) ≅ K) :
    (F.rightDerivedFunctorObjQIso J.obj).inv ≫
      F.rightDerivedFunctor.map
        (((DerivedCategory.quotientCompQhIso C).inv.app J.obj) ≫
          DerivedCategory.Plus.ι.map e.hom) ≫
      F.rightDerivedFunctorPlusCompatibility.inv.app K =
    (DerivedCategory.quotientCompQhIso D).inv.app
        ((F.mapHomologicalComplex (.up ℤ)).obj J.obj) ≫
      DerivedCategory.Plus.ι.map
        (F.rightDerivedFunctorPlusUnit.app ((HomotopyCategory.Plus.quotient C).obj J)) ≫
      DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlus.map e.hom) := by
  dsimp only [Functor.rightDerivedFunctorObjQIso]
  simp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv,
    asIso_hom, Functor.map_comp,
    Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  erw [← plus_unit_compare F ((HomotopyCategory.Plus.quotient C).obj J)]
  have h := F.rightDerivedFunctorPlusCompatibility.hom.naturality e.hom
  dsimp at h
  simp only [Category.assoc]
  erw [← reassoc_of% h]
  simp

section Counit
variable [EnoughInjectives D] [CategoryTheory.Abelian.HasKInjectiveResolutions D]
  (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
omit [EnoughInjectives C] [CategoryTheory.Abelian.HasKInjectiveResolutions C] in
private theorem model_counit
    (J : CochainComplex.Plus D) [J.obj.IsKInjective]
    (K : DerivedCategory.Plus D)
    (e : DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient D).obj J) ≅ K) :
    DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app J.obj) ≫
      ((DerivedCategory.quotientCompQhIso D).inv.app J.obj ≫
        DerivedCategory.Plus.ι.map e.hom) =
    L.mapDerivedCategoryFactors.inv.app ((R.mapHomologicalComplex (.up ℤ)).obj J.obj) ≫
      L.mapDerivedCategory.map
        ((R.rightDerivedFunctorObjQIso J.obj).inv ≫
          R.rightDerivedFunctor.map
            ((DerivedCategory.quotientCompQhIso D).inv.app J.obj ≫
              DerivedCategory.Plus.ι.map e.hom) ≫
          R.rightDerivedFunctorPlusCompatibility.inv.app K) ≫
      DerivedCategory.Plus.ι.map (adj.derivedPlus.counit.app K) := by
  rw [model_compare R J K e, Functor.map_comp, Functor.map_comp]
  let H := (HomotopyCategory.Plus.quotient D).obj J
  have hc := congrArg (fun f ↦ DerivedCategory.Plus.ι.map f)
    (adj.derivedPlus_counit_app_fac H)
  have hn := congrArg (fun f ↦ DerivedCategory.Plus.ι.map f)
    (adj.derivedPlus.counit.naturality e.hom)
  simp only [Functor.map_comp] at hc hn
  simp only [Category.assoc]
  change _ = _ ≫ _ ≫ _ ≫
    DerivedCategory.Plus.ι.map ((R.rightDerivedFunctorPlus ⋙ L.mapDerivedCategoryPlus).map
      e.hom) ≫ DerivedCategory.Plus.ι.map (adj.derivedPlus.counit.app K)
  rw [hn]
  erw [reassoc_of% hc]
  rw [Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app]
  erw [Functor.mapDerivedCategoryFactorsh_hom_app L
    ((R.mapHomologicalComplex (.up ℤ)).obj J.obj)]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    Iso.inv_hom_id_app_assoc]
  have ht : (L.mapHomotopyCategoryFactors (.up ℤ)).inv.app
      ((R.mapHomologicalComplex (.up ℤ)).obj J.obj) = 𝟙 _ := rfl
  have hqt := congrArg (fun k ↦ DerivedCategory.Qh.map k) ht
  have hqi : DerivedCategory.Qh.map
      ((L.mapHomotopyCategoryFactors (.up ℤ)).inv.app
        ((R.mapHomologicalComplex (.up ℤ)).obj J.obj)) = 𝟙 _ :=
    hqt.trans (CategoryTheory.Functor.map_id DerivedCategory.Qh _)
  have hco := Adjunction.ι_map_mapHomotopyCategoryPlus_counit_app adj H
  have hco' := Adjunction.mapHomotopyCategory_counit_app_quotient (.up ℤ) adj J.obj
  have hqco : DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.counit.app H)) =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient D (.up ℤ)).map
      ((adj.mapHomologicalComplex (.up ℤ)).counit.app J.obj)) :=
    congrArg (fun k ↦ DerivedCategory.Qh.map k) (hco.trans hco')
  have hg := congrArg (fun k ↦ k ≫ DerivedCategory.Plus.ι.map
    (DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.counit.app H))) hqi
  have hg' := hg.trans ((Category.id_comp _).trans hqco)
  have hcEq := DerivedCategory.quotientCompQhIso_inv_naturality
    ((adj.mapHomologicalComplex (.up ℤ)).counit.app J.obj)
  have hEq := congrArg (fun k ↦ k ≫ DerivedCategory.Plus.ι.map e.hom) hcEq
  have hLast := congrArg (fun k ↦
    (DerivedCategory.quotientCompQhIso D).inv.app
      ((L.mapHomologicalComplex (.up ℤ)).obj
        ((R.mapHomologicalComplex (.up ℤ)).obj J.obj)) ≫ k ≫
          DerivedCategory.Plus.ι.map e.hom) hg'.symm
  simpa only [Functor.id_map, Category.assoc] using!
    hEq.trans ((Category.assoc _ _ _).trans hLast)

end Counit

section Unit
variable [EnoughInjectives D] [CategoryTheory.Abelian.HasKInjectiveResolutions D]
  (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
omit [EnoughInjectives C] [CategoryTheory.Abelian.HasKInjectiveResolutions C] in
private theorem model_unit
    (J : CochainComplex.Plus C)
    [CochainComplex.IsKInjective ((L.mapHomologicalComplex (.up ℤ)).obj J.obj)]
    (K : DerivedCategory.Plus C)
    (e : DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj J) ≅ K) :
    DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app J.obj) ≫
      (R.rightDerivedFunctorObjQIso
        ((L.mapHomologicalComplex (.up ℤ)).obj J.obj)).inv ≫
      R.rightDerivedFunctor.map
        (L.mapDerivedCategoryFactors.inv.app J.obj ≫
          L.mapDerivedCategory.map
            ((DerivedCategory.quotientCompQhIso C).inv.app J.obj ≫
              DerivedCategory.Plus.ι.map e.hom)) ≫
      R.rightDerivedFunctorPlusCompatibility.inv.app (L.mapDerivedCategoryPlus.obj K) =
    (DerivedCategory.quotientCompQhIso C).inv.app J.obj ≫
      DerivedCategory.Plus.ι.map e.hom ≫
      DerivedCategory.Plus.ι.map (adj.derivedPlus.unit.app K) := by
  let H := (HomotopyCategory.Plus.quotient C).obj J
  let A := L.mapCochainComplexPlus.obj J
  let eL : DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient D).obj A) ≅
      L.mapDerivedCategoryPlus.obj K :=
    (L.mapDerivedCategoryPlusFactorsh.app H).symm ≪≫ L.mapDerivedCategoryPlus.mapIso e
  have hL : (DerivedCategory.quotientCompQhIso D).inv.app A.obj ≫
      DerivedCategory.Plus.ι.map eL.hom =
    L.mapDerivedCategoryFactors.inv.app J.obj ≫
      L.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).inv.app J.obj ≫
        DerivedCategory.Plus.ι.map e.hom) := by
    dsimp only [eL]
    simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.map_comp,
      Functor.mapIso_hom]
    have hi := L.mapDerivedCategoryPlusFactorsh.inv_hom_id_app H
    have hh := Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app L H
    have he : DerivedCategory.Plus.ι.map (L.mapDerivedCategoryPlusFactorsh.inv.app H) =
      L.mapDerivedCategoryFactorsh.inv.app H.obj := by
      apply (cancel_mono (L.mapDerivedCategoryFactorsh.hom.app H.obj)).1
      erw [← hh, ← Functor.map_comp, hi]
      simp only [CategoryTheory.Functor.map_id]
      erw [hh, Iso.inv_hom_id_app]
      rfl
    rw [he]
    have hp := Functor.mapDerivedCategoryFactorsh_hom_app L J.obj
    have ht : (L.mapHomotopyCategoryFactors (.up ℤ)).inv.app J.obj = 𝟙 _ := rfl
    have hm : DerivedCategory.Qh.map
        ((L.mapHomotopyCategoryFactors (.up ℤ)).inv.app J.obj) = 𝟙 _ :=
      (congrArg (fun k ↦ DerivedCategory.Qh.map k) ht).trans
        (CategoryTheory.Functor.map_id DerivedCategory.Qh _)
    erw [hm, Category.comp_id] at hp
    have hpIso : L.mapDerivedCategoryFactorsh.app H.obj =
        L.mapDerivedCategory.mapIso ((DerivedCategory.quotientCompQhIso C).app J.obj) ≪≫
          L.mapDerivedCategoryFactors.app J.obj ≪≫
            ((DerivedCategory.quotientCompQhIso D).app A.obj).symm := by
      apply Iso.ext
      exact hp
    have hpi := congrArg Iso.inv hpIso
    dsimp only [Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv] at hpi
    simp only [Iso.app_inv, Iso.app_hom] at hpi
    erw [hpi]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rfl
  have : A.obj.IsKInjective :=
    inferInstanceAs (CochainComplex.IsKInjective
      ((L.mapHomologicalComplex (.up ℤ)).obj J.obj))
  rw [← hL]
  erw [model_compare R A (L.mapDerivedCategoryPlus.obj K) eL]
  have hu := congrArg (fun f ↦ DerivedCategory.Plus.ι.map f)
    (adj.derivedPlus_unit_app_fac H)
  have hn := congrArg (fun f ↦ DerivedCategory.Plus.ι.map f)
    (adj.derivedPlus.unit.naturality e.hom)
  simp only [Functor.map_comp] at hu hn
  erw [DerivedCategory.quotientCompQhIso_inv_naturality_assoc]
  have hunit := Adjunction.mapHomotopyCategory_unit_app_quotient (.up ℤ) adj J.obj
  have hu' := Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app adj H
  have hqunit := congrArg (fun k ↦ DerivedCategory.Qh.map k) (hu'.trans hunit)
  have hqu : DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app H)) =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient C (.up ℤ)).map
      ((adj.mapHomologicalComplex (.up ℤ)).unit.app J.obj)) := hqunit
  erw [← hqu, ← reassoc_of% hu]
  have heL : R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app H) ≫
      R.rightDerivedFunctorPlus.map eL.hom =
    R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlus.map e.hom) := by
    dsimp only [eL, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Functor.mapIso_hom]
    rw [← Functor.map_comp, Iso.hom_inv_id_app_assoc]
  have hiL := congrArg (fun k ↦ DerivedCategory.Plus.ι.map k) heL
  simp only [Functor.map_comp] at hiL
  erw [hiL]
  exact congrArg (fun k ↦ (DerivedCategory.quotientCompQhIso C).inv.app J.obj ≫ k) hn.symm
end Unit

section NormalizedComparisons
variable [EnoughInjectives D] [CategoryTheory.Abelian.HasKInjectiveResolutions D]
  (L : C ⥤ D) (R : D ⥤ C) [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L] (adj : L ⊣ R)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
omit [EnoughInjectives C] [CategoryTheory.Abelian.HasKInjectiveResolutions C] in
private theorem model_counit_normalized
    (J : CochainComplex.Plus D) [J.obj.IsKInjective] (K : DerivedCategory.Plus D)
    (e : DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient D).obj J) ≅ K) :
    let eB := (DerivedCategory.quotientCompQhIso D).symm.app J.obj ≪≫
      DerivedCategory.Plus.ι.mapIso e
    DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).counit.app J.obj) ≫
      eB.hom =
    (L.supportExactModelComparison ((R.mapHomologicalComplex (.up ℤ)).obj J.obj)
      (R.rightDerivedFunctorPlus.obj K) (R.supportRightModelComparison J.obj K eB)).hom ≫
      DerivedCategory.Plus.ι.map (adj.derivedPlus.counit.app K) := by
  dsimp only
  have h := model_counit L R adj J K e
  simp only [Functor.supportExactModelComparison, Functor.supportRightModelComparison,
    Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.mapIso_hom,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_inv, NatTrans.id_app,
    Category.assoc]
  erw [Category.id_comp (DerivedCategory.Plus.ι.map (adj.derivedPlus.counit.app K))]
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
omit [EnoughInjectives C] [CategoryTheory.Abelian.HasKInjectiveResolutions C] in
private theorem model_unit_normalized (J : CochainComplex.Plus C)
    [CochainComplex.IsKInjective ((L.mapHomologicalComplex (.up ℤ)).obj J.obj)]
    (K : DerivedCategory.Plus C)
    (e : DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient C).obj J) ≅ K) :
    let eB := (DerivedCategory.quotientCompQhIso C).symm.app J.obj ≪≫
      DerivedCategory.Plus.ι.mapIso e
    DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app J.obj) ≫
      (R.supportRightModelComparison ((L.mapHomologicalComplex (.up ℤ)).obj J.obj)
        (L.mapDerivedCategoryPlus.obj K) (L.supportExactModelComparison J.obj K eB)).hom =
    eB.hom ≫ DerivedCategory.Plus.ι.map (adj.derivedPlus.unit.app K) := by
  dsimp only
  have h := model_unit L R adj J K e
  simp only [Functor.supportExactModelComparison, Functor.supportRightModelComparison,
    Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.mapIso_hom,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_inv, NatTrans.id_app,
    Category.assoc]
  erw [Category.comp_id]
  exact h

end NormalizedComparisons

end ModelComparison

namespace AlgebraicGeometry.ProEtale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)
  [hs : IsClosedImmersion s] [hj : IsOpenImmersion j] [hqc : QuasiCompact j]
  (hPair : IsCompl (Set.range s) (Set.range j))

/-- The termwise-induced closed direct image on D⁺, using its exactness, rather than
an independently chosen functor. Source: blueprint lem-pur-support-localization-triangle
(blueprint: lem-pur-support-localization-triangle). -/
noncomputable def supportClosedDerivedPlus :
    DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  letI := preservesFiniteColimits_lowerStar_of_isCompl (R := Λ) s j hPair
  (lowerStar (ModuleCat.{u + 1} Λ) s).mapDerivedCategoryPlus

set_option linter.unusedSectionVars false in
/-- A model in the stated class is K-injective.
Source: Stacks Tag 070J; blueprint lem-pur-support-localization-triangle, step 1
(blueprint: lem-pur-support-localization-triangle).
Proof: choose a lower bound from hI. Its terms are injective by hI. Apply
CochainComplex.isKInjective_of_injective with that bound. -/
theorem supportModelKInjective (I : SupportComplex Λ X)
    (hI : IsSupportInjectiveModel Λ I) : I.IsKInjective := by
  obtain ⟨⟨n, hn⟩, hInj⟩ := hI
  have := hn
  have := hInj
  exact CochainComplex.isKInjective_of_injective I n

include hj in
set_option linter.unusedSectionVars false in
/-- Open restriction of a bounded below injective model is K-injective.
Source: Stacks Tag 08FI; blueprint lem-pur-support-localization-triangle, step 4
(blueprint: lem-pur-support-localization-triangle).
Proof: identify open inverse image with the slice restriction by
lem-weil-proetale-weakly-etale-localization. Its exact left adjoint, extension by
zero, implies that it preserves injectives (lem-weil-pbc-proetale-restriction-injectives).
It preserves the lower bound since it is additive. Apply Stacks Tag 070J. -/
theorem supportOpenModelKInjective (I : SupportComplex Λ X)
    (hI : IsSupportInjectiveModel Λ I) :
    CochainComplex.IsKInjective
      (((upperStar (ModuleCat.{u + 1} Λ) j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) := by
  obtain ⟨⟨n, hn⟩, hInj⟩ := hI
  have := hn
  have := hInj
  have hTerms : ∀ m : ℤ, Injective
      ((((upperStar (ModuleCat.{u + 1} Λ) j).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).X m) := fun m ↦
    injective_upperStar_obj_of_weaklyEtale (ModuleCat.{u + 1} Λ) j (I.X m)
  exact CochainComplex.isKInjective_of_injective _ n

/-- The canonical computation of Rs^! on the chosen model, normalized by the derived
functor unit and by the bounded/unbounded comparison; no model isomorphism is chosen.
Source: blueprint lem-pur-support-localization-triangle, steps 1 and 3
(blueprint: lem-pur-support-localization-triangle). -/
noncomputable def supportShriekModelComparison
    (I : SupportComplex Λ X) (hI : IsSupportInjectiveModel Λ I)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (eB : DerivedCategory.Q.obj I ≅ K.obj) :
    DerivedCategory.Q.obj
        (((finiteClosedUpperShriek Λ s j).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≅
      ((finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus.obj K).obj :=
  letI := supportModelKInjective Λ I hI
  (finiteClosedUpperShriek Λ s j).supportRightModelComparison I K eB

/-- The canonical first-term comparison, using termwise exact s_* and the preceding
unit-normalized computation of Rs^!.
Source: blueprint lem-pur-support-localization-triangle, step 5
(blueprint: lem-pur-support-localization-triangle). -/
noncomputable def supportFirstModelComparison
    (I : SupportComplex Λ X) (hI : IsSupportInjectiveModel Λ I)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (eB : DerivedCategory.Q.obj I ≅ K.obj) :
    DerivedCategory.Q.obj (supportedSectionsComplex Λ s j hPair I) ≅
      ((supportClosedDerivedPlus Λ s j hPair).obj
        ((finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus.obj K)).obj :=
  letI := preservesFiniteColimits_lowerStar_of_isCompl (R := Λ) s j hPair
  (lowerStar (ModuleCat.{u + 1} Λ) s).supportExactModelComparison
    (((finiteClosedUpperShriek Λ s j).mapHomologicalComplex (.up ℤ)).obj I)
    ((finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus.obj K)
    (supportShriekModelComparison Λ s j I hI K eB)

/-- The canonical third-term comparison, using injectivity after open restriction,
the derived functor unit, and the ordinary bounded/unbounded comparison for Rj_*.
Source: blueprint lem-pur-support-localization-triangle, steps 4 and 5
(blueprint: lem-pur-support-localization-triangle). -/
noncomputable def supportThirdModelComparison
    (I : SupportComplex Λ X) (hI : IsSupportInjectiveModel Λ I)
    (K : DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)))
    (eB : DerivedCategory.Q.obj I ≅ K.obj) :
    DerivedCategory.Q.obj (supportCComplex Λ j I) ≅
      ((lowerStar (ModuleCat.{u + 1} Λ) j).rightDerivedFunctorPlus.obj
        ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K)).obj :=
  letI := supportOpenModelKInjective Λ j I hI
  (lowerStar (ModuleCat.{u + 1} Λ) j).supportRightModelComparison
    (((upperStar (ModuleCat.{u + 1} Λ) j).mapHomologicalComplex (.up ℤ)).obj I)
    ((upperStar (ModuleCat.{u + 1} Λ) j).mapDerivedCategoryPlus.obj K)
    ((upperStar (ModuleCat.{u + 1} Λ) j).supportExactModelComparison I K eB)

/-- On every bounded below injective model the specified cone quotient is invertible,
and its specified triangle is distinguished.
Source: Stacks Tag 0152; blueprint lem-pur-support-localization-triangle, step 5
(blueprint: lem-pur-support-localization-triangle).
Proof: injective terms are flasque for the open restriction. Indeed the free module
sheaf on the open fibre product embeds in the free module sheaf on each test object;
an arrow to an injective extends across this embedding. The open unit is therefore
surjective on sections and epic. Its kernel is canonically s_*s^!I via the supported
unit comparison. Degreewise this gives the short exact sequence A→I→C of
lem-pur-support-exact. The explicit cone-to-quotient map q is a quasi-isomorphism
by lem-pc-cone-short-exact-quasi-iso, hence Q(q) is invertible. Transporting the
mapping-cone distinguished triangle along it gives precisely supportModelTriangle,
whose boundary is the negative shifted projection after Q(q) inverse. -/
theorem supportInjectiveConeDistinguished (I : SupportComplex Λ X)
    (hI : IsSupportInjectiveModel Λ I) :
    (supportModelSequence Λ s j hPair I).ShortExact ∧
      ∃ hq : IsIso (DerivedCategory.Q.map (supportConeQuotient Λ s j hPair I)),
        supportModelTriangle Λ s j hPair I hq ∈
          distTriang (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) := by
  have := hI.2
  have hcmp := finiteSupportedClosedComparison_isIso Λ s j hPair
  obtain ⟨f, g, hf, hg, w, hS⟩ := shortExact_sectionsWithSupport Λ s j hPair I
  have hf' : f = (supportModelSequence Λ s j hPair I).f := by
    ext n : 1
    apply (cancel_epi ((finiteSupportedClosedComparison Λ s j).app (I.X n))).1
    simpa [supportModelSequence, supportModelInclusion, finiteSupportedClosedComparison]
      using hf n
  have hg' : g = (supportModelSequence Λ s j hPair I).g := by
    ext n : 1
    exact hg n
  subst f
  subst g
  have hS' : (supportModelSequence Λ s j hPair I).ShortExact := hS
  have : QuasiIso (supportConeQuotient Λ s j hPair I) :=
    CochainComplex.mappingCone.quasiIso_descShortComplex hS'
  have hq : IsIso (DerivedCategory.Q.map (supportConeQuotient Λ s j hPair I)) :=
    inferInstance
  exact ⟨hS', hq, DerivedCategory.triangleOfSES_distinguished hS'⟩

private theorem supportModelTriangle_eq_sequence (I : SupportComplex Λ X)
    (hq : IsIso (DerivedCategory.Q.map (supportConeQuotient Λ s j hPair I))) :
    supportModelTriangle Λ s j hPair I hq =
      supportSequenceTriangle (supportModelSequence Λ s j hPair I) hq := rfl

attribute [local irreducible] supportModelTriangle

/-- The same specified cone starts from an actual bounded below input complex and
an injective-resolution arrow, rather than only an abstract derived object.
Source: Stacks Tags 013K, 070J and 0152; blueprint
lem-pur-support-localization-triangle, steps 1 and 5
(blueprint: lem-pur-support-localization-triangle).
Proof: enough injectives gives a bounded below injective representative I of QK.
K-injectivity and the derived Hom bijection lift the representing isomorphism to
r:K→I. Since Qr is invertible, r is a quasi-isomorphism. Apply the specified cone
construction and supportInjectiveConeDistinguished. -/
theorem supportResolutionCone (K : SupportComplex Λ X) (hK : ∃ n : ℤ, K.IsStrictlyGE n) :
    ∃ (I : SupportComplex Λ X) (r : K ⟶ I),
      IsSupportInjectiveModel Λ I ∧ QuasiIso r ∧
      ∃ hq : IsIso (DerivedCategory.Q.map (supportConeQuotient Λ s j hPair I)),
        supportModelTriangle Λ s j hPair I hq ∈
          distTriang (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) := by
  obtain ⟨n, hn⟩ := hK
  have := hn
  obtain ⟨I, r, hr, hInj, hBound⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective K n
  have hI : IsSupportInjectiveModel Λ I := ⟨⟨n, hBound⟩, hInj⟩
  obtain ⟨_, hq, hd⟩ := supportInjectiveConeDistinguished Λ s j hPair I hI
  exact ⟨I, r, hI, hr, hq, hd⟩

attribute [local irreducible] upperStar lowerStar upperStarLowerStarAdjunction
  finiteClosedUpperShriek

private noncomputable def supportKernelIsKernel
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :=
  isLimitOfHasKernelOfPreservesLimit
    ((evaluation _ _).obj M)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit

set_option linter.unusedSectionVars false in
private theorem supportMap_unit_zero
    (hPair : IsCompl (Set.range s) (Set.range j))
    (N : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ))
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (f : (lowerStar (ModuleCat.{u + 1} Λ) s).obj N ⟶ M) :
    f ≫ (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app M = 0 := by
  apply ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).homEquiv _ _).symm.injective
  have hz := isZero_upperStar_lowerStar_of_disjoint (ModuleCat.{u + 1} Λ) s j
    hPair.disjoint N
  exact hz.eq_of_src _ _

attribute [local irreducible] supportKernelIsKernel

private noncomputable def supportSheafHomEquiv
    (N : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ))
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    ((lowerStar (ModuleCat.{u + 1} Λ) s).obj N ⟶ M) ≃
      (N ⟶ (finiteClosedUpperShriek Λ s j).obj M) := by
  have := finiteSupportedClosedComparison_isIso Λ s j hPair
  let q := (asIso (finiteSupportedClosedComparison Λ s j)).app M
  let e : ((lowerStar (ModuleCat.{u + 1} Λ) s).obj N ⟶ M) ≃
      ((lowerStar (ModuleCat.{u + 1} Λ) s).obj N ⟶
        (finiteSupportedSections Λ j).obj M) :=
    { toFun := fun f ↦ (supportKernelIsKernel Λ j M).lift
        (KernelFork.ofι f (supportMap_unit_zero Λ s j hPair N M f))
      invFun := fun f ↦ f ≫ (finiteSupportedSectionsι Λ j).app M
      left_inv := by
        intro f
        exact (supportKernelIsKernel Λ j M).fac _ WalkingParallelPair.zero
      right_inv := by
        intro f
        apply Fork.IsLimit.hom_ext (supportKernelIsKernel Λ j M)
        exact (supportKernelIsKernel Λ j M).fac _ WalkingParallelPair.zero }
  exact e.trans ((Iso.homCongr (Iso.refl _) q).trans
    (fullyFaithfulLowerStar Λ s).homEquiv.symm)
private theorem supportSheafHomEquiv_symm
    (N : Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ))
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (f : N ⟶ (finiteClosedUpperShriek Λ s j).obj M) :
    (supportSheafHomEquiv Λ s j hPair N M).symm f =
      (lowerStar (ModuleCat.{u + 1} Λ) s).map f ≫
        (supportModelInclusion Λ s j hPair).app M := by
  simp [supportSheafHomEquiv, supportKernelIsKernel, Iso.homCongr, supportModelInclusion]

attribute [local irreducible] supportSheafHomEquiv

private noncomputable def supportSheafAdjunction :
    lowerStar (ModuleCat.{u + 1} Λ) s ⊣ finiteClosedUpperShriek Λ s j :=
  Adjunction.mkOfHomEquiv
    { homEquiv := supportSheafHomEquiv Λ s j hPair
      homEquiv_naturality_left_symm := by
        intros
        simp only [supportSheafHomEquiv_symm, Functor.map_comp, Category.assoc]
      homEquiv_naturality_right := by
        intro N M M' f g
        apply (supportSheafHomEquiv Λ s j hPair N M').symm.injective
        rw [Equiv.symm_apply_apply, supportSheafHomEquiv_symm, Functor.map_comp,
          Category.assoc]
        change f ≫ g = _ ≫
          (finiteClosedUpperShriek Λ s j ⋙ lowerStar (ModuleCat.{u + 1} Λ) s).map g ≫ _
        rw [(supportModelInclusion Λ s j hPair).naturality g,
          ← Category.assoc, ← supportSheafHomEquiv_symm, Equiv.symm_apply_apply]
        rfl }

attribute [local irreducible] supportSheafAdjunction

private noncomputable def supportDerivedAdjunction :
    supportClosedDerivedPlus Λ s j hPair ⊣
      (finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus := by
  letI := preservesFiniteColimits_lowerStar_of_isCompl (R := Λ) s j hPair
  exact (supportSheafAdjunction Λ s j hPair).derivedPlus

private theorem supportSheafAdjunction_counit :
    (supportSheafAdjunction Λ s j hPair).counit =
      supportModelInclusion Λ s j hPair := by
  apply NatTrans.ext
  funext M
  simpa [supportSheafAdjunction] using
    supportSheafHomEquiv_symm Λ s j hPair _ M (𝟙 _)


attribute [local irreducible] supportDerivedAdjunction
  supportShriekModelComparison supportFirstModelComparison supportThirdModelComparison


universe v w

private theorem map_additive_model_eq
    {C : Type u} {D : Type v} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
    {I J : CochainComplex C ℤ} [J.IsKInjective] (f g : I ⟶ J)
    (h : DerivedCategory.Q.map f = DerivedCategory.Q.map g) :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f) =
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map g) := by
  have he : (HomotopyCategory.quotient C (.up ℤ)).map f =
      (HomotopyCategory.quotient C (.up ℤ)).map g := by
    apply (CochainComplex.IsKInjective.Qh_map_bijective _ J).injective
    apply (cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app J)).1
    simpa only [DerivedCategory.quotientCompQhIso_hom_naturality] using
      congrArg (fun k ↦ (DerivedCategory.quotientCompQhIso C).hom.app I ≫ k) h
  exact DerivedCategory.Q_map_eq_of_homotopy D
    (F.mapHomotopy (HomotopyCategory.homotopyOfEq f g he))

private theorem map_additive_model_iso
    {C : Type u} {D : Type v} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] (F : C ⥤ D) [F.Additive]
    {I J : CochainComplex C ℤ} [I.IsKInjective] [J.IsKInjective] (f : I ⟶ J)
    (h : IsIso (DerivedCategory.Q.map f)) :
    IsIso (DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map f)) := by
  have : QuasiIso f := (DerivedCategory.isIso_Q_map_iff_quasiIso C f).mp h
  have hq : IsIso ((HomotopyCategory.quotient C (.up ℤ)).map f) :=
    (HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences f).mpr
      ((CochainComplex.IsKInjective.quasiIso_iff f).mp inferInstance)
  have : IsIso ((HomotopyCategory.quotient D (.up ℤ)).map
      ((F.mapHomologicalComplex (.up ℤ)).map f)) :=
    inferInstanceAs (IsIso ((F.mapHomotopyCategory (.up ℤ)).map
      ((HomotopyCategory.quotient C (.up ℤ)).map f)))
  have : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient D (.up ℤ)).map
        ((F.mapHomologicalComplex (.up ℤ)).map f))) := inferInstance
  apply (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso D) _).mp
  change IsIso (DerivedCategory.Qh.map
    ((HomotopyCategory.quotient D (.up ℤ)).map
      ((F.mapHomologicalComplex (.up ℤ)).map f)))
  infer_instance


private noncomputable def supportSequenceMap {I J : SupportComplex Λ X} (f : I ⟶ J) :
    supportModelSequence Λ s j hPair I ⟶ supportModelSequence Λ s j hPair J where
  τ₁ := supportAMap Λ s j hPair f
  τ₂ := f
  τ₃ := supportCMap Λ j f
  comm₁₂ := by
    ext n : 1
    exact (supportModelInclusion Λ s j hPair).naturality (f.f n)
  comm₂₃ := by
    ext n : 1
    exact (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.naturality (f.f n)

private theorem supportFunctoriality : SupportTriangleFunctoriality Λ s j hPair := by
  intro I J hI hJ hqI hqJ f
  simp only [supportModelTriangle_eq_sequence]
  have hS := (supportInjectiveConeDistinguished Λ s j hPair I hI).1
  have hT := (supportInjectiveConeDistinguished Λ s j hPair J hJ).1
  obtain ⟨t, ht₁, ht₂, ht₃⟩ := explicitSupportTriangle_map hS hT hqI hqJ
    (supportSequenceMap Λ s j hPair f)
  refine ⟨t, ⟨ht₁, ht₂, ht₃⟩, ?_⟩
  intro t' ht'
  ext
  · exact ht'.1.trans ht₁.symm
  · exact ht'.2.1.trans ht₂.symm
  · exact ht'.2.2.trans ht₃.symm
set_option linter.unusedSectionVars false in
private theorem supportCanonicality : SupportTriangleCanonicality Λ s j hPair := by
  intro I J hI hJ
  have := supportModelKInjective Λ I hI
  have := supportModelKInjective Λ J hJ
  constructor
  · intro f g h
    dsimp only [supportAMap, supportCMap]
    exact ⟨map_additive_model_eq _ f g h, map_additive_model_eq _ f g h⟩
  · intro f h
    dsimp only [supportAMap, supportCMap]
    exact ⟨map_additive_model_iso _ f h, map_additive_model_iso _ f h⟩


end AlgebraicGeometry.ProEtale

section EtaleComparison
universe v
section GenericTriangle
variable {C : Type u} {D : Type v} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]

private noncomputable def shortComplexIsoFromQuotient
    {S T : ShortComplex C} (hS : S.ShortExact) (hT : T.ShortExact)
    (b : S.X₂ ≅ T.X₂) (c : S.X₃ ≅ T.X₃) (h : b.hom ≫ T.g = S.g ≫ c.hom) :
    S ≅ T := by
  let a := hT.fIsKernel.lift (KernelFork.ofι (S.f ≫ b.hom) (by
    rw [Category.assoc, h, ← Category.assoc, S.zero, zero_comp]))
  let a' := hS.fIsKernel.lift (KernelFork.ofι (T.f ≫ b.inv) (by
    rw [← cancel_mono c.hom, zero_comp, Category.assoc, Category.assoc, ← h,
      Iso.inv_hom_id_assoc, T.zero]))
  have ha : a ≫ T.f = S.f ≫ b.hom := hT.fIsKernel.fac _ WalkingParallelPair.zero
  have ha' : a' ≫ S.f = T.f ≫ b.inv := hS.fIsKernel.fac _ WalkingParallelPair.zero
  have := hS.mono_f
  have := hT.mono_f
  let aIso : S.X₁ ≅ T.X₁ :=
    { hom := a
      inv := a'
      hom_inv_id := by
        apply (cancel_mono S.f).1
        rw [Category.assoc, ha', ← Category.assoc, ha, Category.assoc,
          Iso.hom_inv_id, Category.comp_id, Category.id_comp]
      inv_hom_id := by
        apply (cancel_mono T.f).1
        rw [Category.assoc, ha, ← Category.assoc, ha', Category.assoc,
          Iso.inv_hom_id, Category.comp_id, Category.id_comp] }
  exact ShortComplex.isoMk aIso b c ha h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private noncomputable def mapTriangleOfSESIso
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact) :
    F.mapDerivedCategory.mapTriangle.obj (DerivedCategory.triangleOfSES hS) ≅
      DerivedCategory.triangleOfSES
        (hS.map_of_exact (F.mapHomologicalComplex (.up ℤ))) := by
  refine Triangle.isoMk _ _ (F.mapDerivedCategoryFactors.app S.X₁)
    (F.mapDerivedCategoryFactors.app S.X₂) (F.mapDerivedCategoryFactors.app S.X₃) ?_ ?_ ?_
  · exact (F.mapDerivedCategoryFactors.hom.naturality S.f)
  · exact (F.mapDerivedCategoryFactors.hom.naturality S.g)
  · change (F.mapDerivedCategory.map (DerivedCategory.triangleOfSESδ hS) ≫
        (F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app _) ≫
        (shiftFunctor _ (1 : ℤ)).map (F.mapDerivedCategoryFactors.hom.app S.X₁) = _
    rw [DerivedCategory.map_triangleOfSESδ]
    simp

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem transportShortExactTriangle
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {S : ShortComplex (CochainComplex C ℤ)} (hS : S.ShortExact)
    {T : ShortComplex (CochainComplex D ℤ)} (hT : T.ShortExact)
    (hqS : IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex S)))
    (hqT : IsIso (DerivedCategory.Q.map (CochainComplex.mappingCone.descShortComplex T)))
    (b : ((F.mapHomologicalComplex (.up ℤ)).obj S.X₂) ≅ T.X₂)
    (c : ((F.mapHomologicalComplex (.up ℤ)).obj S.X₃) ≅ T.X₃)
    (h : b.hom ≫ T.g = (F.mapHomologicalComplex (.up ℤ)).map S.g ≫ c.hom) :
    ∃ (e : S.map (F.mapHomologicalComplex (.up ℤ)) ≅ T)
      (t : F.mapDerivedCategory.mapTriangle.obj
          (AlgebraicGeometry.ProEtale.supportSequenceTriangle S hqS) ≅
        AlgebraicGeometry.ProEtale.supportSequenceTriangle T hqT),
      e.hom.τ₂ = b.hom ∧ e.hom.τ₃ = c.hom ∧
      t.hom.hom₁ = F.mapDerivedCategoryFactors.hom.app S.X₁ ≫
        DerivedCategory.Q.map e.hom.τ₁ ∧
      t.hom.hom₂ = F.mapDerivedCategoryFactors.hom.app S.X₂ ≫
        DerivedCategory.Q.map b.hom ∧
      t.hom.hom₃ = F.mapDerivedCategoryFactors.hom.app S.X₃ ≫
        DerivedCategory.Q.map e.hom.τ₃ := by
  have hSm := hS.map_of_exact (F.mapHomologicalComplex (.up ℤ))
  let e := shortComplexIsoFromQuotient hSm hT b c h
  let t2 := DerivedCategory.triangleOfSES.map hSm hT e.hom
  have he1 : IsIso e.hom.τ₁ := inferInstance
  have he2 : IsIso e.hom.τ₂ := inferInstance
  have he3 : IsIso e.hom.τ₃ := inferInstance
  have : IsIso t2 := Triangle.isIso_of_isIsos t2
    (inferInstanceAs (IsIso (DerivedCategory.Q.map e.hom.τ₁)))
    (inferInstanceAs (IsIso (DerivedCategory.Q.map e.hom.τ₂)))
    (inferInstanceAs (IsIso (DerivedCategory.Q.map e.hom.τ₃)))
  exact ⟨e, mapTriangleOfSESIso F hS ≪≫ asIso t2, rfl, rfl, rfl, rfl, rfl⟩

end GenericTriangle

open AlgebraicGeometry AlgebraicGeometry.ProEtale
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X U X' U' : Scheme.{u}} (j : U ⟶ X)
  (v : X' ⟶ X) (vU : U' ⟶ U) (j' : U' ⟶ X')
  [Etale v] [Etale vU] (sq : vU ≫ j = j' ≫ v)

namespace AlgebraicGeometry.ProEtale

section
universe u₁ u₂
variable {C : Type u₁} {D : Type u₂} [Category C] [Category D]
  {L₁ L₂ L₃ L₄ : C ⥤ D} {R₁ R₂ R₃ R₄ : D ⥤ C}
  (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : L₃ ⊣ R₃) (d : L₄ ⊣ R₄)

private theorem conjugateTriple (e₁ : L₂ ≅ L₁) (e₂ : L₂ ≅ L₃) (e₃ : L₃ ≅ L₄) :
    conjugateEquiv a d (e₁.symm ≪≫ e₂ ≪≫ e₃).inv =
      (conjugateEquiv a b e₁.hom ≫ conjugateEquiv b c e₂.inv) ≫
        conjugateEquiv c d e₃.inv := by
  simp only [Iso.trans_inv, Iso.symm_inv, Category.assoc]
  rw [← conjugateEquiv_comp a c d, ← conjugateEquiv_comp a b c]
  exact Category.assoc _ _ _
private theorem conjugateTripleEq (e₁ : L₂ ≅ L₁) (e₂ : L₂ ≅ L₃) (e₃ : L₃ ≅ L₄)
    (f₁ : R₁ ≅ R₂) (f₂ : R₂ ≅ R₃) (f₃ : R₄ ≅ R₃)
    (h₁ : conjugateEquiv a b e₁.hom = f₁.hom)
    (h₂ : conjugateEquiv b c e₂.inv = f₂.hom)
    (h₃ : conjugateEquiv c d e₃.inv = f₃.inv) :
    conjugateEquiv a d (e₁.symm ≪≫ e₂ ≪≫ e₃).inv =
      (f₁ ≪≫ f₂ ≪≫ f₃.symm).hom := by
  rw [conjugateTriple a b c d, h₁, h₂, h₃]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]

end

section Mate
universe u₁ u₂ u₃ u₄
variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  [Category A] [Category B] [Category C] [Category D]
  {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}

private theorem mateOfConjugate (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (c : F₁ ⊣ U₁) (d : F₂ ⊣ U₂)
    (α : TwoSquare F₁ L₁ L₂ F₂) (β : TwoSquare U₂ R₂ R₁ U₁)
    (h : conjugateEquiv (a.comp d) (c.comp b) α = β.natTrans) :
    mateEquiv a b α = (mateEquiv d c).symm β := by
  apply (mateEquiv d c).injective
  rw [Equiv.apply_symm_apply]
  apply TwoSquare.ext
  intro M
  exact NatTrans.congr_app ((iterated_mateEquiv_conjugateEquiv a b c d α).trans h) M

private theorem mateIso_unit (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (e : L₁ ⋙ F₂ ≅ F₁ ⋙ L₂) (β : R₁ ⋙ F₁ ⟶ F₂ ⋙ R₂)
    (h : (mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)).natTrans = β) (M : A) :
    F₁.map (a.unit.app M) ≫ β.app (L₁.obj M) ≫ R₂.map (e.hom.app M) =
      b.unit.app (F₁.obj M) := by
  rw [← h, ← Category.assoc, unit_mateEquiv a b, Category.assoc,
    ← Functor.map_comp]
  change b.unit.app (F₁.obj M) ≫ R₂.map (e.inv.app M ≫ e.hom.app M) = _
  rw [Iso.inv_hom_id_app]
  exact (congrArg (fun f ↦ b.unit.app (F₁.obj M) ≫ f)
    (R₂.map_id ((F₁ ⋙ L₂).obj M))).trans (Category.comp_id _)

private theorem quotientMate_unit (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂)
    (e : L₁ ⋙ F₂ ≅ F₁ ⋙ L₂) (β : R₁ ⋙ F₁ ⟶ F₂ ⋙ R₂)
    (h : (mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)).natTrans = β) :
    Functor.whiskerRight a.unit F₁ ≫
      (Functor.whiskerLeft L₁ β ≫ Functor.whiskerRight e.hom R₂) =
      Functor.whiskerLeft F₁ b.unit := by
  ext M
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    using mateIso_unit a b e β h M

end Mate

attribute [local irreducible] upperStarComp upperStarCongr lowerStarComp lowerStarCongr
  upperStar lowerStar upperStarLowerStarAdjunction
  squareLowerStarIso baseChangeMap
  mateEquiv conjugateEquiv Adjunction.comp Functor.whiskerLeft Functor.whiskerRight

omit [Finite Λ] [Etale v] [Etale vU] in
private theorem supportSquareConjugate :
    conjugateEquiv
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) vU))
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).comp
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j'))
      (((upperStarComp (ModuleCat.{u + 1} Λ) vU j).symm ≪≫
        upperStarCongr (ModuleCat.{u + 1} Λ) sq ≪≫
        upperStarComp (ModuleCat.{u + 1} Λ) j' v).inv) =
      (squareLowerStarIso (ModuleCat.{u + 1} Λ) (CommSq.mk sq.symm)).hom := by
  unfold squareLowerStarIso
  exact conjugateTripleEq
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) vU))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (vU ≫ j))
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (j' ≫ v))
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v).comp
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j'))
    (upperStarComp (ModuleCat.{u + 1} Λ) vU j)
    (upperStarCongr (ModuleCat.{u + 1} Λ) sq)
    (upperStarComp (ModuleCat.{u + 1} Λ) j' v)
    (lowerStarComp (ModuleCat.{u + 1} Λ) vU j)
    (lowerStarCongr (ModuleCat.{u + 1} Λ) sq)
    (lowerStarComp (ModuleCat.{u + 1} Λ) j' v)
    (conjugateEquiv_upperStarComp_hom (ModuleCat.{u + 1} Λ) vU j)
    (conjugateEquiv_upperStarCongr_inv (ModuleCat.{u + 1} Λ) sq)
    (conjugateEquiv_upperStarComp_inv (ModuleCat.{u + 1} Λ) j' v)


omit [Finite Λ] [Etale v] [Etale vU] in
private theorem supportSquareMate :
    (mateEquiv
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j')
      (TwoSquare.mk _ _ _ _
        (((upperStarComp (ModuleCat.{u + 1} Λ) vU j).symm ≪≫
          upperStarCongr (ModuleCat.{u + 1} Λ) sq ≪≫
          upperStarComp (ModuleCat.{u + 1} Λ) j' v).inv))).natTrans =
      baseChangeMap (ModuleCat.{u + 1} Λ) (CommSq.mk sq.symm) := by
  unfold baseChangeMap
  exact congrArg TwoSquare.natTrans
    (mateOfConjugate
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j')
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) v)
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) vU)
      _ _ (supportSquareConjugate Λ j v vU j' sq))

attribute [local irreducible] finiteSupportedSections finiteClosedUpperShriek
  supportModelInclusion

omit [Finite Λ] in
private theorem supportOpenBaseChange_unit
    (M : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) :
    (upperStar (ModuleCat.{u + 1} Λ) v).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit.app M) ≫
      supportOpenBaseChangeApp Λ j v vU j' sq M =
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j').unit.app
      ((upperStar (ModuleCat.{u + 1} Λ) v).obj M) := by
  have h := quotientMate_unit
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j')
    ((upperStarComp (ModuleCat.{u + 1} Λ) vU j).symm ≪≫
      upperStarCongr (ModuleCat.{u + 1} Λ) sq ≪≫
      upperStarComp (ModuleCat.{u + 1} Λ) j' v)
    (baseChangeMap (ModuleCat.{u + 1} Λ) (CommSq.mk sq.symm))
    (supportSquareMate Λ j v vU j' sq)
  change Functor.whiskerRight
      (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).unit
      (upperStar (ModuleCat.{u + 1} Λ) v) ≫
      supportOpenBaseChange Λ j v vU j' sq = _ at h
  simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    supportOpenBaseChangeApp] using NatTrans.congr_app h M


variable {Z Z' : Scheme.{u}} (s : Z ⟶ X) (vZ : Z' ⟶ Z) (s' : Z' ⟶ X')
  [IsClosedImmersion s] [IsOpenImmersion j] [QuasiCompact j]
  [IsClosedImmersion s'] [IsOpenImmersion j'] [QuasiCompact j']
  (hPair : IsCompl (Set.range s) (Set.range j))
  (hPair' : IsCompl (Set.range s') (Set.range j'))

omit [Finite Λ] in
private theorem pullback_model (I : SupportComplex Λ X)
    (hI : IsSupportInjectiveModel Λ I) :
    IsSupportInjectiveModel Λ (supportPullbackComplex Λ v I) := by
  obtain ⟨⟨n, hn⟩, hInj⟩ := hI
  have := hn
  have := hInj
  have ha : (upperStar (ModuleCat.{u + 1} Λ) v).Additive :=
    additive_upperStar (ModuleCat.{u + 1} Λ) v
  refine ⟨⟨n, ?_⟩, fun m ↦
    injective_upperStar_obj_of_weaklyEtale (ModuleCat.{u + 1} Λ) v (I.X m)⟩
  exact HomologicalComplex.map_isStrictlySupported I
    (upperStar (ModuleCat.{u + 1} Λ) v) (ComplexShape.embeddingUpIntGE n)


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem supportEtaleBaseChange : SupportTriangleEtaleBaseChange Λ s j hPair := by
  intro X' Z' U' v vZ vU s' j' _ _ _ _ _ hPair' hs hj I hI hq
  let F := upperStar (ModuleCat.{u + 1} Λ) v
  have hS := (supportInjectiveConeDistinguished Λ s j hPair I hI).1
  have hIb := pullback_model Λ v I hI
  obtain ⟨hT, hq', _⟩ := supportInjectiveConeDistinguished Λ s' j' hPair'
    (supportPullbackComplex Λ v I) hIb
  let c := supportOpenBaseChangeComplex Λ j v vU j' hj.w I
  have hbc := isIso_baseChangeMap_of_isPullback (ModuleCat.{u + 1} Λ) hj.flip
  have hc (n : ℤ) : IsIso (c.f n) := by
    dsimp only [c, supportOpenBaseChangeComplex]
    simp only [supportOpenBaseChangeApp, supportOpenBaseChange, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  have : IsIso c := HomologicalComplex.Hom.isIso_of_components c
  obtain ⟨e, t, he2, he3, ht1, ht2, ht3⟩ :=
    transportShortExactTriangle F hS hT hq hq' (Iso.refl _) (asIso c) (by
      ext n : 1
      exact (supportOpenBaseChange_unit Λ j v vU j' hj.w (I.X n)).symm)
  refine ⟨hIb, hq', e, ?_⟩
  refine ⟨t, he2, he3, ht1, ?_, ?_⟩
  · have h := ht2
    erw [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.comp_id] at h
    exact h
  · change t.hom.hom₃ = _
    exact ht3
end AlgebraicGeometry.ProEtale

end EtaleComparison

namespace AlgebraicGeometry.ProEtale
variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
  {X Z U : Scheme.{u}} (s : Z ⟶ X) (j : U ⟶ X)
  [IsClosedImmersion s] [IsOpenImmersion j] [QuasiCompact j]
  (hPair : IsCompl (Set.range s) (Set.range j))
attribute [local irreducible] upperStar lowerStar upperStarLowerStarAdjunction
  finiteClosedUpperShriek supportShriekModelComparison supportFirstModelComparison
  supportThirdModelComparison supportSheafAdjunction supportDerivedAdjunction
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The injective cone is the ambient localization triangle with its actual adjunction
arrows. Rs^! is the right derived functor of the recorded sheaf supported-kernel functor.
Any other right adjoint to this same s_* on D⁺ has the unique counit-compatible
identification. The final conjunct gives resolution independence, derived functoriality,
and etale base change of this specified triangle, including the boundary.

Source: blueprint lem-pur-support-localization-triangle; Stacks Tags 013K, 070J,
05TI, 09AA, 09AH, 09AG, 09BN, 08FI, 0152 and 015F
(blueprint: lem-pur-support-localization-triangle).

Proof, following the eight steps of the node:
1. The module-sheaf categories on the compatible small sites are Grothendieck abelian,
hence have enough injectives. Every D⁺ object has a bounded below injective model I.
The derived Hom theorem realizes its comparison isomorphism by a quasi-isomorphism
from any bounded below input complex. Right derivation of s^! is computed by s^!I.
2. A map s_*N→M has zero open restriction. It factors uniquely through the kernel
G_Z(M) of the open unit. The canonical comparison G_Z(M)≅s_*s^!M and full
faithfulness of s_* give s_*⊣s^!, with counit the specified inverse-comparison inclusion.
3. Exactness of s_* makes s^! preserve injectives. The termwise adjunction descends
to homotopy categories. Derived Hom into the bounded below injective models then
gives s_*⊣Rs^! on D⁺, with that same counit. Uniqueness of a right adjoint gives
the displayed unique natural isomorphism with any other right adjoint.
4. Open restriction preserves injectives and lower bounds. Thus j^*I computes j^*K,
and j_*j^*I computes Rj_*j^*K. The derived open unit is its termwise unit.
The bounded-below and unbounded right derived direct images agree on these models.
5. Apply supportInjectiveConeDistinguished. Its three terms represent s_*Rs^!K,
K, and Rj_*j^*K. Their canonical comparison isomorphisms carry the first two
arrows to the exceptional counit and open unit, respectively.
6. Every derived morphism between injective models has a unique homotopy class of
chain representatives. Apply the three additive functors to such a representative.
Naturality gives a map of the short exact sequences; the diagonal cone map satisfies
q' t = c q and p' t = a[1] p. Inverting q and q' gives the boundary square.
Additive functors preserve homotopies. Identity and composition follow componentwise;
comparison maps representing the identity are invertible and satisfy the cocycle law.
7. Etale inverse image is restriction to the localized site and preserves injectives.
On a test object V over X', the open direct images both evaluate at V×_X U.
The canonical base-change mate identifies these evaluations and their open units.
Exact pullback identifies their kernels, and hence their first terms via the supported
unit comparisons. This gives the specified short-complex isomorphism.
8. Exact pullback carries the cone differential, quotient and negative projection
to those of the primed cone. It preserves the inverse of Q(q). Hence the full
triangle isomorphism has the specified three components and boundary square.
Comparison with any other injective model uses step 6. -/
theorem supportLocalizationTriangle :
    ∃ adj : supportClosedDerivedPlus Λ s j hPair ⊣
        (finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus,
      (∀ (G : DerivedCategory.Plus
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) ⥤
          DerivedCategory.Plus (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} Λ)))
        (adj' : supportClosedDerivedPlus Λ s j hPair ⊣ G),
        ∃! e : (finiteClosedUpperShriek Λ s j).rightDerivedFunctorPlus ≅ G,
          ∀ K : DerivedCategory.Plus
              (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)),
            (supportClosedDerivedPlus Λ s j hPair).map (e.hom.app K) ≫
            adj'.counit.app K = adj.counit.app K) ∧
      (∀ K : DerivedCategory.Plus
          (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)),
        ∃ (I : SupportComplex Λ X) (hI : IsSupportInjectiveModel Λ I)
          (hq : IsIso (DerivedCategory.Q.map (supportConeQuotient Λ s j hPair I)))
          (eB : DerivedCategory.Q.obj I ≅ K.obj),
          supportModelTriangle Λ s j hPair I hq ∈
              distTriang (DerivedCategory
                (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) ∧
          DerivedCategory.Q.map (supportModelSequence Λ s j hPair I).f ≫ eB.hom =
            (supportFirstModelComparison Λ s j hPair I hI K eB).hom ≫
              DerivedCategory.Plus.ι.map (adj.counit.app K) ∧
          DerivedCategory.Q.map (supportModelSequence Λ s j hPair I).g ≫
              (supportThirdModelComparison Λ j I hI K eB).hom =
            eB.hom ≫ DerivedCategory.Plus.ι.map
              ((derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) j).unit.app K)) ∧
      supportTriangleMeaning Λ s j hPair := by
  let adj := supportDerivedAdjunction Λ s j hPair
  refine ⟨adj, ?_, ?_, ?_⟩
  · intro G adj'
    refine ⟨Adjunction.rightAdjointUniq adj adj', ?_, ?_⟩
    · exact Adjunction.rightAdjointUniq_hom_app_counit adj adj'
    · intro e he
      apply Iso.ext
      apply NatTrans.ext
      funext K
      apply (adj'.homEquiv _ _).symm.injective
      exact (he K).trans (Adjunction.rightAdjointUniq_hom_app_counit adj adj' K).symm
  · intro K
    obtain ⟨I, hTerms, ⟨e⟩⟩ := plus_injective_representative K
    let hI : IsSupportInjectiveModel Λ I.obj := ⟨I.property, hTerms⟩
    obtain ⟨_, hq, hd⟩ := supportInjectiveConeDistinguished Λ s j hPair I.obj hI
    let eB := (DerivedCategory.quotientCompQhIso _).symm.app I.obj ≪≫
      DerivedCategory.Plus.ι.mapIso e
    refine ⟨I.obj, hI, hq, eB, hd, ?_, ?_⟩
    · have := supportModelKInjective Λ I.obj hI
      have := preservesFiniteColimits_lowerStar_of_isCompl (R := Λ) s j hPair
      have h := model_counit_normalized (lowerStar (ModuleCat.{u + 1} Λ) s)
        (finiteClosedUpperShriek Λ s j) (supportSheafAdjunction Λ s j hPair) I K e
      have hc : (supportModelSequence Λ s j hPair I.obj).f =
          ((supportSheafAdjunction Λ s j hPair).mapHomologicalComplex (.up ℤ)).counit.app
            I.obj := by
        ext n : 1
        exact (congrArg (fun α ↦ α.app (I.obj.X n))
          (supportSheafAdjunction_counit Λ s j hPair)).symm
      rw [hc]
      simpa only [adj, supportDerivedAdjunction, supportFirstModelComparison,
        supportShriekModelComparison] using h
    · have := supportOpenModelKInjective Λ j I.obj hI
      have h := model_unit_normalized (upperStar (ModuleCat.{u + 1} Λ) j)
        (lowerStar (ModuleCat.{u + 1} Λ) j)
        (upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j) I K e
      have hg : (supportModelSequence Λ s j hPair I.obj).g =
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) j).mapHomologicalComplex
            (.up ℤ)).unit.app I.obj := by
        ext n : 1
        rfl
      rw [hg]
      simpa only [supportThirdModelComparison, derivedUpperStarLowerStarAdjunctionPlus,
        Adjunction.derivedAdjunctionPlus_eq_derivedPlus] using h
  · exact ⟨supportCanonicality Λ s j hPair, supportFunctoriality Λ s j hPair,
      supportEtaleBaseChange Λ j s hPair⟩

end AlgebraicGeometry.ProEtale
