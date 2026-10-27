/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF groups Q03 and A6
-/
module

public import Sheaf.CategoryTheory.ConstantModulePlusComparisonData
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

import Sheaf.CategoryTheory.EtaleConstantModuleGeometricRealization
import Sheaf.CategoryTheory.EtaleConstantModuleTensorNormalization
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import Sheaf.CategoryTheory.DerivedExactMate
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import Sheaf.CategoryTheory.ConstantModuleOrdinaryRealization
import Sheaf.CategoryTheory.ConstantModuleTensorSquareDescent
import Mathlib.CategoryTheory.Adjunction.Restrict
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate

/-! # Constant-module realization and the canonical derived projection map

Source: Stacks Project, Cohomology on Sites, Tags 07A4 and 07A6
(blueprint: lem-sfb-constant-module-derived-projection-identification).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genInjectivity false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- The imported sequence-site module registers a global standard localization for all
-- ring-sheaf module categories; the etale clause uses the Grothendieck-abelian one.
attribute [-instance] WeilConjectures.SemilinearSections.hasDerived
attribute [-instance] CategoryTheory.ConstantScalarRestriction.ringPreadditive
  CategoryTheory.ConstantScalarRestriction.fixedPreadditive
  CategoryTheory.ConstantScalarRestriction.ringZeroMorphisms
  CategoryTheory.ConstantScalarRestriction.fixedZeroMorphisms
universe u v w z
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Abelian
open CategoryTheory.ConstantScalarRestriction
namespace ConstantModuleDerivedSquare
private theorem ordinaryMate_eq
    {B E F H : Type*} [Category* B] [Category* E] [Category* F] [Category* H]
    {L : B ⥤ E} {R : E ⥤ B} {L' : F ⥤ H} {R' : H ⥤ F}
    {S : B ⥤ F} {T : E ⥤ H} (a : L ⊣ R) (b : L' ⊣ R')
    (oL : L ⋙ T ≅ S ⋙ L') (oR : R ⋙ S ≅ T ⋙ R')
    (oh : ∀ M N (f : L.obj M ⟶ N),
      b.homEquiv _ _ (oL.inv.app M ≫ T.map f) = S.map (a.homEquiv M N f) ≫ oR.hom.app N) :
    (mateEquiv a b oL.inv).natTrans = oR.hom := by
  ext N
  apply (b.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit]
  have hc := oh (R.obj N) N (a.counit.app N)
  have he : a.homEquiv (R.obj N) N (a.counit.app N) = 𝟙 _ := by
    simp [Adjunction.homEquiv_unit]
  rw [he, CategoryTheory.Functor.map_id, Category.id_comp] at hc
  have hc' := (b.homEquiv _ _).symm_apply_eq.mpr hc.symm
  rw [Adjunction.homEquiv_counit] at hc'
  have hm := mateEquiv_counit a b oL.inv N
  change L'.map ((mateEquiv a b oL.inv).natTrans.app N) ≫
    b.counit.app (T.obj N) = _ at hm
  exact hm.trans hc'.symm

variable {B E F H : Type*} [Category* B] [Category* E] [Category* F] [Category* H]
  [Abelian B] [Abelian E] [Abelian F] [Abelian H]
  [HasDerivedCategory B] [HasDerivedCategory E] [HasDerivedCategory F] [HasDerivedCategory H]
  [HasKInjectiveResolutions E] [HasKInjectiveResolutions H]
  {L : B ⥤ E} {R : E ⥤ B} {L' : F ⥤ H} {R' : H ⥤ F}
  {S : B ⥤ F} {T : E ⥤ H}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [S.Additive] [T.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [S.IsEquivalence] [T.IsEquivalence]
private def normalizedLeft (oL : L ⋙ T ≅ S ⋙ L') :
    L.mapDerivedCategory ⋙ T.mapDerivedCategory ≅
      S.mapDerivedCategory ⋙ L'.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso L T).symm ≪≫
    Functor.mapDerivedCategoryNatIso oL ≪≫
      Functor.mapDerivedCategoryCompIso S L'

omit [HasKInjectiveResolutions E] [HasKInjectiveResolutions H]
  [S.IsEquivalence] [T.IsEquivalence] in
private theorem normalizedLeft_fac (oL : L ⋙ T ≅ S ⋙ L') :
    CategoryTheory.ConstantModuleDerivedProjection.LeftLocalizationCondition
      L L' S T oL (normalizedLeft oL) := by
  intro P
  dsimp only [normalizedLeft, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc, Category.assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_factors,
    Functor.mapDerivedCategoryNatIso_fac]
  apply (cancel_epi
    ((Functor.mapDerivedCategoryCompIso L T).hom.app
      (DerivedCategory.Q.obj P))).mp
  rw [Iso.hom_inv_id_app_assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_factors_assoc]
  rfl

omit [HasKInjectiveResolutions E] [HasKInjectiveResolutions H]
  [S.IsEquivalence] [T.IsEquivalence] in
private theorem normalizedLeft_fac_h (oL : L ⋙ T ≅ S ⋙ L') (P : HomotopyCategory B (.up ℤ)) :
    (normalizedLeft oL).hom.app (DerivedCategory.Qh.obj P) ≫
      L'.mapDerivedCategory.map (S.mapDerivedCategoryFactorsh.hom.app P) ≫
      L'.mapDerivedCategoryFactorsh.hom.app
        ((S.mapHomotopyCategory (.up ℤ)).obj P) =
    T.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app P) ≫
      T.mapDerivedCategoryFactorsh.hom.app
        ((L.mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory oL.hom (.up ℤ)).app P) := by
  dsimp only [normalizedLeft, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  rw [Category.assoc, Category.assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_factorsh,
    Functor.mapDerivedCategoryNatIso_fach]
  apply (cancel_epi
    ((Functor.mapDerivedCategoryCompIso L T).hom.app
      (DerivedCategory.Qh.obj P))).mp
  rw [Iso.hom_inv_id_app_assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_factorsh_assoc]

omit [HasKInjectiveResolutions E] [HasKInjectiveResolutions H]
  [S.IsEquivalence] [T.IsEquivalence] in
private theorem normalizedLeft_inv_fac_h (oL : L ⋙ T ≅ S ⋙ L') (P : HomotopyCategory B (.up ℤ)) :
    (normalizedLeft oL).inv.app (DerivedCategory.Qh.obj P) ≫
      T.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app P) ≫
      T.mapDerivedCategoryFactorsh.hom.app
        ((L.mapHomotopyCategory (.up ℤ)).obj P) =
    L'.mapDerivedCategory.map (S.mapDerivedCategoryFactorsh.hom.app P) ≫
      L'.mapDerivedCategoryFactorsh.hom.app
        ((S.mapHomotopyCategory (.up ℤ)).obj P) ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory oL.inv (.up ℤ)).app P) := by
  have hc : ((NatTrans.mapHomotopyCategory oL.inv (.up ℤ)).app P) ≫
      ((NatTrans.mapHomotopyCategory oL.hom (.up ℤ)).app P) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, oL.inv_hom_id,
      NatTrans.mapHomotopyCategory_id, NatTrans.id_app]
  have hq : IsIso (DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory oL.hom (.up ℤ)).app P)) := by
    have : IsIso (NatTrans.mapHomotopyCategory oL.hom (.up ℤ)) := by
      refine ⟨⟨NatTrans.mapHomotopyCategory oL.inv (.up ℤ), ?_, ?_⟩⟩
      · rw [← NatTrans.mapHomotopyCategory_comp, oL.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
      · rw [← NatTrans.mapHomotopyCategory_comp, oL.inv_hom_id,
          NatTrans.mapHomotopyCategory_id]
    infer_instance
  apply (cancel_mono (DerivedCategory.Qh.map
    ((NatTrans.mapHomotopyCategory oL.hom (.up ℤ)).app P))).mp
  simp only [Category.assoc, ← Functor.map_comp, hc]
  rw [← normalizedLeft_fac_h, Iso.inv_hom_id_app_assoc]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

private theorem normalizedMate_isIso (a : L ⊣ R) (b : L' ⊣ R') (oL : L ⋙ T ≅ S ⋙ L') :
    IsIso (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
      b.mapDerivedCategoryRightDerivedAdjunction (normalizedLeft oL).inv).natTrans := by
  refine (NatTrans.isIso_iff_isIso_app _).2 (fun N ↦ ?_)
  exact a.mapDerivedCategoryRightDerivedAdjunction.isIso_mateEquiv_app_of_isIso
    b.mapDerivedCategoryRightDerivedAdjunction (normalizedLeft oL).symm
    S.mapDerivedCategory.asEquivalence.toAdjunction
    T.mapDerivedCategory.asEquivalence.toAdjunction N

private def normalizedRight (a : L ⊣ R) (b : L' ⊣ R') (oL : L ⋙ T ≅ S ⋙ L') :
    R.rightDerivedFunctor ⋙ S.mapDerivedCategory ≅
      T.mapDerivedCategory ⋙ R'.rightDerivedFunctor :=
  letI := normalizedMate_isIso a b oL
  asIso (mateEquiv a.mapDerivedCategoryRightDerivedAdjunction
    b.mapDerivedCategoryRightDerivedAdjunction (normalizedLeft oL).inv).natTrans

private theorem normalizedRight_fac (a : L ⊣ R) (b : L' ⊣ R')
    (oL : L ⋙ T ≅ S ⋙ L') (oR : R ⋙ S ≅ T ⋙ R')
    (hm : (mateEquiv a b oL.inv).natTrans = oR.hom) :
    CategoryTheory.ConstantModuleDerivedProjection.RightLocalizationCondition
      R R' S T oR (normalizedRight a b oL) := by
  intro P
  have h := a.derivedExact_mateEquiv_app_fac b oL.inv
    (normalizedLeft oL).inv (normalizedLeft_inv_fac_h oL)
    ((HomotopyCategory.quotient _ (.up ℤ)).obj P)
  rw [hm] at h
  have hh := congrArg (fun f ↦ f ≫ R'.rightDerivedFunctor.map
    (T.mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P))) h
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app] at hh
  erw [R'.rightDerivedFunctor.map_id, Category.comp_id] at hh
  change S.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) ≫
      (normalizedRight a b oL).hom.app (DerivedCategory.Q.obj P) ≫
      R'.rightDerivedFunctor.map (T.mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj P)) =
    S.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
      ((R.mapHomologicalComplex (.up ℤ)).obj P)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (.up ℤ)).map
        ((NatIso.mapHomologicalComplex oR (.up ℤ)).hom.app P)) ≫
      R'.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ (.up ℤ)).obj
        ((T.mapHomologicalComplex (.up ℤ)).obj P)) at hh
  simp only [normalizedRight, asIso_hom, Functor.mapDerivedCategoryFactorsh_hom_app,
    DerivedCategory.quotientCompQhIso,
    HomologicalComplexUpToQuasiIso.quotientCompQhIso, Functor.mapHomotopyCategoryFactors,
    Quotient.lift.isLift_hom, Quotient.lift.isLift_inv, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.comp_id] at hh
  erw [T.mapDerivedCategory.map_id, S.mapDerivedCategory.map_id] at hh
  erw [Category.comp_id, Category.comp_id, Category.id_comp, Category.id_comp] at hh
  exact hh

private theorem normalizedDerivedHom (a : L ⊣ R) (b : L' ⊣ R') (oL : L ⋙ T ≅ S ⋙ L')
    (M : DerivedCategory B) (N : DerivedCategory E)
    (f : L.mapDerivedCategory.obj M ⟶ N) :
    b.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
      ((normalizedLeft oL).inv.app M ≫ T.mapDerivedCategory.map f) =
    S.mapDerivedCategory.map
      (a.mapDerivedCategoryRightDerivedAdjunction.homEquiv M N f) ≫
      (normalizedRight a b oL).hom.app N := by
  let aD := a.mapDerivedCategoryRightDerivedAdjunction
  let bD := b.mapDerivedCategoryRightDerivedAdjunction
  let θ : TwoSquare S.mapDerivedCategory L.mapDerivedCategory L'.mapDerivedCategory
      T.mapDerivedCategory := (normalizedLeft oL).inv
  have hu := unit_mateEquiv aD bD θ M
  have hn := (mateEquiv aD bD θ).natTrans.naturality f
  change _ = _ ≫ (mateEquiv aD bD θ).natTrans.app N
  simp only [Adjunction.homEquiv_unit]
  change bD.unit.app (S.mapDerivedCategory.obj M) ≫
    R'.rightDerivedFunctor.map (θ.app M ≫ T.mapDerivedCategory.map f) = _
  rw [R'.rightDerivedFunctor.map_comp, ← Category.assoc]
  erw [← hu]
  simp only [Category.assoc, Functor.comp_map] at hn ⊢
  rw [← hn, ← S.mapDerivedCategory.map_comp_assoc]

end ConstantModuleDerivedSquare


namespace CategoryTheory.Adjunction
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasKInjectiveResolutions D]
  [EnoughInjectives D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

private def exactDerivedRestriction (adj : L ⊣ R) :
    L.mapDerivedCategoryPlus ⊣ R.rightDerivedFunctorPlus :=
  adj.mapDerivedCategoryRightDerivedAdjunction.restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    L.mapDerivedCategoryPlusCompatibility.symm
    R.rightDerivedFunctorPlusCompatibility.symm

private theorem exactDerivedRestriction_unit_fac (adj : L ⊣ R)
    (K : HomotopyCategory.Plus C) :
    (exactDerivedRestriction adj).unit.app (DerivedCategory.Plus.Qh.obj K) ≫
        R.rightDerivedFunctorPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K) =
      DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app K) ≫
        R.rightDerivedFunctorPlusUnit.app (L.mapHomotopyCategoryPlus.obj K) := by
  apply DerivedCategory.Plus.ι.map_injective
  simp only [Functor.map_comp, exactDerivedRestriction,
    Adjunction.map_restrictFullyFaithful_unit_app]
  have h₁ := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit ((HomotopyCategory.Plus.ι C).obj K)
  have h₃ : R.rightDerivedFunctorPlusιUnit.app (L.mapHomotopyCategoryPlus.obj K) ≫
      R.rightDerivedFunctorPlusCompatibility.hom.app
        (DerivedCategory.Plus.Qh.obj (L.mapHomotopyCategoryPlus.obj K)) =
      R.ιRightDerivedFunctorUnit.app (L.mapHomotopyCategoryPlus.obj K) := by
    simp [Functor.rightDerivedFunctorPlusCompatibility]
  have h₄ : DerivedCategory.Plus.ι.map
      (R.rightDerivedFunctorPlusUnit.app (L.mapHomotopyCategoryPlus.obj K)) =
      R.ιRightDerivedFunctorUnit.app (L.mapHomotopyCategoryPlus.obj K) ≫
        R.rightDerivedFunctorPlusCompatibility.inv.app
          (DerivedCategory.Plus.Qh.obj (L.mapHomotopyCategoryPlus.obj K)) := by
    rw [← h₃, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have h₅ := R.rightDerivedFunctorPlusCompatibility.inv.naturality
    (L.mapDerivedCategoryPlusFactorsh.hom.app K)
  simp only [Functor.comp_map, Functor.ι_map_mapDerivedCategoryPlusFactorsh_hom_app] at h₅
  have h₇ : DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Qh.map (adj.mapHomotopyCategoryPlus.unit.app K)) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).unit.app
        ((HomotopyCategory.Plus.ι C).obj K)) := by
    exact congrArg DerivedCategory.Qh.map
      (Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app adj K)
  rw [h₄, h₇]
  dsimp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom, Iso.refl_inv,
    NatTrans.id_app, Iso.symm_inv]
  erw [Functor.map_id, Category.id_comp]
  erw [Category.assoc, ← h₅, ← Category.assoc, h₁, Category.assoc]
  rfl

private theorem exactDerivedRestriction_eq (adj : L ⊣ R) :
    exactDerivedRestriction adj = adj.derivedPlus :=
  Adjunction.ext (adj.derivedPlus_unit_eq _ (exactDerivedRestriction_unit_fac adj))

private theorem exactDerived_counit_compatibility (adj : L ⊣ R)
    (N : DerivedCategory.Plus D) :
    L.mapDerivedCategoryPlusCompatibility.hom.app (R.rightDerivedFunctorPlus.obj N) ≫
      L.mapDerivedCategory.map (R.rightDerivedFunctorPlusCompatibility.hom.app N) ≫
      adj.mapDerivedCategoryRightDerivedAdjunction.counit.app N.obj =
        DerivedCategory.Plus.ι.map (adj.derivedPlus.counit.app N) := by
  rw [← exactDerivedRestriction_eq adj]
  exact (adj.mapDerivedCategoryRightDerivedAdjunction.map_restrictFullyFaithful_counit_app
    (ObjectProperty.fullyFaithfulι _) (ObjectProperty.fullyFaithfulι _)
    L.mapDerivedCategoryPlusCompatibility.symm
    R.rightDerivedFunctorPlusCompatibility.symm N).symm

private theorem exactDerived_hom_compatibility (adj : L ⊣ R)
    (M : DerivedCategory.Plus C) (N : DerivedCategory.Plus D)
    (f : L.mapDerivedCategoryPlus.obj M ⟶ N) :
    adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv M.obj N.obj
        (DerivedCategory.Plus.ι.map f) =
      DerivedCategory.Plus.ι.map (adj.derivedPlus.homEquiv M N f) ≫
        R.rightDerivedFunctorPlusCompatibility.hom.app N := by
  rw [← exactDerivedRestriction_eq adj, exactDerivedRestriction,
    Adjunction.restrictFullyFaithful_homEquiv_apply,
    Functor.FullyFaithful.map_preimage]
  simp only [ObjectProperty.ι_map, ObjectProperty.ι_obj, Functor.comp_obj, Iso.symm_hom,
    Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  erw [Functor.map_id, Category.id_comp]
  rw [Adjunction.homEquiv_unit]

end CategoryTheory.Adjunction


namespace ConstantModulePlusSquare
variable {B E F H : Type*} [Category* B] [Category* E] [Category* F] [Category* H]
  [Abelian B] [Abelian E] [Abelian F] [Abelian H]
  [HasDerivedCategory B] [HasDerivedCategory E] [HasDerivedCategory F] [HasDerivedCategory H]
  [HasKInjectiveResolutions E] [HasKInjectiveResolutions H]
  [EnoughInjectives E] [EnoughInjectives H]
  {L : B ⥤ E} {R : E ⥤ B} {L' : F ⥤ H} {R' : H ⥤ F}
  {S : B ⥤ F} {T : E ⥤ H}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [S.Additive] [T.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits S] [PreservesFiniteColimits S]
  [PreservesFiniteLimits T] [PreservesFiniteColimits T]
private theorem hom (a : L ⊣ R) (b : L' ⊣ R')
    (i : L.mapDerivedCategory ⋙ T.mapDerivedCategory ≅
      S.mapDerivedCategory ⋙ L'.mapDerivedCategory)
    (j : R.rightDerivedFunctor ⋙ S.mapDerivedCategory ≅
      T.mapDerivedCategory ⋙ R'.rightDerivedFunctor)
    (l : L.mapDerivedCategoryPlus ⋙ T.mapDerivedCategoryPlus ≅
      S.mapDerivedCategoryPlus ⋙ L'.mapDerivedCategoryPlus)
    (r : R.rightDerivedFunctorPlus ⋙ S.mapDerivedCategoryPlus ≅
      T.mapDerivedCategoryPlus ⋙ R'.rightDerivedFunctorPlus)
    (hl : ∀ M, DerivedCategory.Plus.ι.map (l.inv.app M) = i.inv.app M.obj)
    (hr : ∀ N, DerivedCategory.Plus.ι.map (r.hom.app N) ≫
      R'.rightDerivedFunctorPlusCompatibility.hom.app (T.mapDerivedCategoryPlus.obj N) =
      S.mapDerivedCategory.map (R.rightDerivedFunctorPlusCompatibility.hom.app N) ≫
        j.hom.app N.obj)
    (he : ∀ M N (f : L.mapDerivedCategory.obj M ⟶ N),
      b.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
        (i.inv.app M ≫ T.mapDerivedCategory.map f) =
      S.mapDerivedCategory.map (a.mapDerivedCategoryRightDerivedAdjunction.homEquiv M N f) ≫
        j.hom.app N) :
    ∀ (M : DerivedCategory.Plus B) (N : DerivedCategory.Plus E)
      (f : L.mapDerivedCategoryPlus.obj M ⟶ N),
      b.derivedPlus.homEquiv _ _ (l.inv.app M ≫ T.mapDerivedCategoryPlus.map f) =
      S.mapDerivedCategoryPlus.map (a.derivedPlus.homEquiv M N f) ≫ r.hom.app N := by
  intro M N f
  apply DerivedCategory.Plus.ι.map_injective
  apply (cancel_mono (R'.rightDerivedFunctorPlusCompatibility.hom.app
    (T.mapDerivedCategoryPlus.obj N))).mp
  rw [Functor.map_comp, Category.assoc, hr]
  have hfixed := Adjunction.exactDerived_hom_compatibility b
    (S.mapDerivedCategoryPlus.obj M) (T.mapDerivedCategoryPlus.obj N)
    (l.inv.app M ≫ T.mapDerivedCategoryPlus.map f)
  have hring := Adjunction.exactDerived_hom_compatibility a M N f
  rw [← hfixed, Functor.map_comp, hl]
  change b.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
      (i.inv.app M.obj ≫ T.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f)) = _
  rw [he, ← Category.assoc]
  have hh := congrArg S.mapDerivedCategory.map hring
  rw [Functor.map_comp] at hh
  exact congrArg (fun z ↦ z ≫ j.hom.app N.obj) hh
end ConstantModulePlusSquare

namespace CategoryTheory.ConstantModuleDerivedProjection
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {A : Type (max u v)} [CommRing A]
  [HasDerivedCategory.{w} (Modules J A)] [HasDerivedCategory.{w} (Modules K A)]
  [HasDerivedCategory.{w} (Fixed J A)] [HasDerivedCategory.{w} (Fixed K A)]

attribute [local instance] CategoryTheory.Limits.comp_preservesFiniteLimits
  CategoryTheory.Limits.comp_preservesFiniteColimits in
omit [HasDerivedCategory (Modules J A)] [HasDerivedCategory (Modules K A)]
  [HasDerivedCategory (Fixed J A)] [HasDerivedCategory (Fixed K A)] in
private theorem exactData_of_tensor (d : GeometricData J K A)
    (o : OrdinaryIdentification d) (t : FixedTensorData d) : Nonempty (ExactData d) := by
  let : d.pullA.IsLeftAdjoint := d.fixedAdj.isLeftAdjoint
  let : d.pushA.IsRightAdjoint := d.fixedAdj.isRightAdjoint
  let : d.pullR.IsLeftAdjoint := d.ringAdj.isLeftAdjoint
  let : d.pullA.Additive :=
    rightExactFunctor_le_additiveFunctor _ _ _ ⟨inferInstance⟩
  let : d.pushA.Additive :=
    leftExactFunctor_le_additiveFunctor _ _ _ ⟨inferInstance⟩
  let : PreservesFiniteLimits (d.pullA ⋙
      sheafCompose K (forget (ModuleCat.{max u v} A))) :=
    preservesFiniteLimits_of_natIso t.underlying.symm
  let : PreservesFiniteLimits d.pullA :=
    preservesFiniteLimits_of_reflects_of_preserves d.pullA
      (sheafCompose K (forget (ModuleCat.{max u v} A)))
  let : PreservesFiniteLimits (d.pullR ⋙ restriction K A) :=
    preservesFiniteLimits_of_natIso o.left.symm
  let : PreservesFiniteLimits d.pullR :=
    preservesFiniteLimits_of_reflects_of_preserves d.pullR (restriction K A)
  exact ⟨{}⟩

private theorem adjunctionSquare_of_hom
    {B E F H : Type*} [Category* B] [Category* E] [Category* F] [Category* H]
    {L : B ⥤ E} {R : E ⥤ B} {L' : F ⥤ H} {R' : H ⥤ F}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (S : B ⥤ F) (T : E ⥤ H)
    (i : L ⋙ T ≅ S ⋙ L') (j : R ⋙ S ≅ T ⋙ R')
    (h : ∀ M N (f : L.obj M ⟶ N),
      adj'.homEquiv _ _ (i.inv.app M ≫ T.map f) =
        S.map (adj.homEquiv M N f) ≫ j.hom.app N) :
    AdjunctionSquare L R L' R' adj adj' S T i j := by
  refine ⟨h, ?_, ?_⟩
  · intro M
    have hu := h M (L.obj M) (𝟙 _)
    simp only [Functor.map_id, Adjunction.homEquiv_id] at hu
    rw [← Category.assoc, ← hu, Adjunction.homEquiv_unit, Category.assoc, ← R'.map_comp]
    simp
  · intro N
    have hc := h (R.obj N) N (adj.counit.app N)
    have he : adj.homEquiv (R.obj N) N (adj.counit.app N) = 𝟙 _ := by
      simp [Adjunction.homEquiv_unit]
    rw [he, S.map_id, Category.id_comp] at hc
    have hc' := (adj'.homEquiv _ _).symm_apply_eq.mpr hc.symm
    rw [Adjunction.homEquiv_counit] at hc'
    apply (cancel_epi (i.inv.app (R.obj N))).mp
    simpa only [Category.assoc, Iso.inv_hom_id_app_assoc] using hc'.symm

private theorem projectionSquare_of_tensor_adjunction
    {B E F H : Type*} [Category* B] [Category* E] [Category* F] [Category* H]
    [MonoidalCategory B] [MonoidalCategory E] [MonoidalCategory F] [MonoidalCategory H]
    {L : B ⥤ E} {R : E ⥤ B} {L' : F ⥤ H} {R' : H ⥤ F}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (S : B ⥤ F) (T : E ⥤ H)
    (mL : L.Monoidal) (mL' : L'.Monoidal) (mS : S.Monoidal) (mT : T.Monoidal)
    (i : L ⋙ T ≅ S ⋙ L') (j : R ⋙ S ≅ T ⋙ R')
    (ht : TensorSquare L L' S T mL mL' mS mT i)
    (ha : AdjunctionSquare L R L' R' adj adj' S T i j) :
    ProjectionSquare L R L' R' adj adj' S T mL mL' mS mT i j := by
  let := mL
  let := mL'
  let := mS
  let := mT
  let cT := asIso (Functor.OplaxMonoidal.δNatTrans T)
  let cS := asIso (Functor.OplaxMonoidal.δNatTrans S)
  have hm : (mateEquiv adj adj' i.inv).natTrans = j.hom := by
    ext N
    apply (adj'.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit]
    have hm := mateEquiv_counit adj adj' i.inv N
    change L'.map (((mateEquiv adj adj') i.inv).natTrans.app N) ≫
      adj'.counit.app (T.obj N) = _ at hm
    have hj := ha.2.2 N
    change T.map (adj.counit.app N) = _ at hj
    rw [hm, hj]
    simp only [Iso.inv_hom_id_app_assoc]
  have hc : Adjunction.ComparisonCompatible i.symm
      (Functor.OplaxMonoidal.δNatTrans L) (Functor.OplaxMonoidal.δNatTrans L') cT cS := by
    intro X Y
    change T.map (Functor.OplaxMonoidal.δ L X Y) ≫ Functor.OplaxMonoidal.δ T _ _ = _
    apply (cancel_mono (i.hom.app X ⊗ₘ i.hom.app Y)).mp
    rw [Category.assoc, ht X Y]
    simp [cS, Category.assoc, ← tensorHom_def, tensorHom_comp_tensorHom]
  intro X Y
  have h := adj.map_rightAdjointProjectionMap_comp_mateEquiv adj' hc X Y
  have hma (N : E) : ((mateEquiv adj adj' i.symm.hom).app N) = j.hom.app N :=
    NatTrans.congr_app hm N
  simp only [hma] at h
  simpa only [cT, cS, asIso_hom, Functor.OplaxMonoidal.δNatTrans_app_app,
    tensorHom_def, Iso.symm_inv, curriedTensor_obj_obj, curriedTensor_obj_map,
    curriedTensor_map_app, id_whiskerRight, whiskerLeft_id, Category.id_comp,
    Category.comp_id] using h


section
attribute [local irreducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

private def plusLeft (d : GeometricData J K A) (x : ExactData d)
    (o : OrdinaryIdentification d) (t : FixedTensorData d)
    (cJ : DerivedComparison.{u, v, w, w} J A)
    (cK : DerivedComparison.{u, v, w, w} K A)
    (e : DerivedIdentification d x o t cJ cK) :
    d.pullR.mapDerivedCategoryPlus ⋙ (restriction K A).mapDerivedCategoryPlus ≅
      (restriction J A).mapDerivedCategoryPlus ⋙ d.pullA.mapDerivedCategoryPlus :=
  NatIso.ofComponents (fun M ↦ ObjectProperty.isoMk _ (e.left.app M.obj)) (by
    intro M N f
    apply DerivedCategory.Plus.ι.map_injective
    exact e.left.hom.naturality (DerivedCategory.Plus.ι.map f))

private theorem plusLeft_inclusion (d : GeometricData J K A) (x : ExactData d)
    (o : OrdinaryIdentification d) (t : FixedTensorData d)
    (cJ : DerivedComparison.{u, v, w, w} J A)
    (cK : DerivedComparison.{u, v, w, w} K A)
    (e : DerivedIdentification d x o t cJ cK)
    (M : DerivedCategory.Plus (Modules J A)) :
    DerivedCategory.Plus.ι.map ((plusLeft d x o t cJ cK e).hom.app M) =
      e.left.hom.app M.obj := by
  rfl

private def plusRight (d : GeometricData J K A) (x : ExactData d)
    (o : OrdinaryIdentification d) (t : FixedTensorData d)
    (cJ : DerivedComparison.{u, v, w, w} J A)
    (cK : DerivedComparison.{u, v, w, w} K A)
    (e : DerivedIdentification d x o t cJ cK) :
    d.pushR.rightDerivedFunctorPlus ⋙ (restriction J A).mapDerivedCategoryPlus ≅
      (restriction K A).mapDerivedCategoryPlus ⋙ d.pushA.rightDerivedFunctorPlus :=
  NatIso.ofComponents (fun N ↦ ObjectProperty.isoMk _
    ((onDerived J A).mapIso (d.pushR.rightDerivedFunctorPlusCompatibility.app N) ≪≫
      e.right.app N.obj ≪≫
      (d.pushA.rightDerivedFunctorPlusCompatibility.app
        ((restriction K A).mapDerivedCategoryPlus.obj N)).symm)) (by
    intro M N f
    apply DerivedCategory.Plus.ι.map_injective
    change (onDerived J A).map
        (DerivedCategory.Plus.ι.map (d.pushR.rightDerivedFunctorPlus.map f)) ≫
          ((onDerived J A).map (d.pushR.rightDerivedFunctorPlusCompatibility.hom.app N) ≫
            e.right.hom.app N.obj ≫
            d.pushA.rightDerivedFunctorPlusCompatibility.inv.app
              ((restriction K A).mapDerivedCategoryPlus.obj N)) =
      ((onDerived J A).map (d.pushR.rightDerivedFunctorPlusCompatibility.hom.app M) ≫
        e.right.hom.app M.obj ≫
        d.pushA.rightDerivedFunctorPlusCompatibility.inv.app
          ((restriction K A).mapDerivedCategoryPlus.obj M)) ≫
      DerivedCategory.Plus.ι.map (d.pushA.rightDerivedFunctorPlus.map
        ((restriction K A).mapDerivedCategoryPlus.map f))
    have hr := d.pushR.rightDerivedFunctorPlusCompatibility.hom.naturality f
    have he := e.right.hom.naturality (DerivedCategory.Plus.ι.map f)
    have ha := d.pushA.rightDerivedFunctorPlusCompatibility.inv.naturality
      ((restriction K A).mapDerivedCategoryPlus.map f)
    simp only [Functor.comp_map] at hr he ha
    simp only [Category.assoc]
    erw [← (onDerived J A).map_comp_assoc, hr, Functor.map_comp_assoc, reassoc_of% he, ha]
    rfl)

private theorem plusRight_inclusion (d : GeometricData J K A) (x : ExactData d)
  (o : OrdinaryIdentification d) (t : FixedTensorData d)
  (cJ : DerivedComparison.{u, v, w, w} J A)
  (cK : DerivedComparison.{u, v, w, w} K A)
  (e : DerivedIdentification d x o t cJ cK)
  (N : DerivedCategory.Plus (Modules K A)) :
    DerivedCategory.Plus.ι.map ((plusRight d x o t cJ cK e).hom.app N) ≫
      d.pushA.rightDerivedFunctorPlusCompatibility.hom.app
        ((restriction K A).mapDerivedCategoryPlus.obj N) =
    (onDerived J A).map (d.pushR.rightDerivedFunctorPlusCompatibility.hom.app N) ≫
      e.right.hom.app N.obj := by
  change ((onDerived J A).map
      (d.pushR.rightDerivedFunctorPlusCompatibility.hom.app N) ≫
    e.right.hom.app N.obj ≫ d.pushA.rightDerivedFunctorPlusCompatibility.inv.app
      ((restriction K A).mapDerivedCategoryPlus.obj N)) ≫ _ = _
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

private theorem plusIdentification_exists (d : GeometricData J K A) (x : ExactData d)
    (o : OrdinaryIdentification d) (t : FixedTensorData d)
    (cJ : DerivedComparison.{u, v, w, w} J A)
    (cK : DerivedComparison.{u, v, w, w} K A)
    (e : DerivedIdentification d x o t cJ cK) :
    Nonempty (PlusIdentification d x o t cJ cK e) := by
  let l := plusLeft d x o t cJ cK e
  let r := plusRight d x o t cJ cK e
  have hr := plusRight_inclusion d x o t cJ cK e
  refine ⟨{
    left := l
    right := r
    left_inclusion := plusLeft_inclusion d x o t cJ cK e
    right_inclusion := hr
    hom := ?_
    ring_counit := Adjunction.exactDerived_counit_compatibility d.ringAdj
    fixed_counit := Adjunction.exactDerived_counit_compatibility d.fixedAdj }⟩
  apply ConstantModulePlusSquare.hom d.ringAdj d.fixedAdj e.left e.right l r
  · intro M
    rfl
  · exact hr
  · exact e.adjunction.1


end

section
-- Keep the derived tensor model abstract while assembling its normalized squares.
attribute [local irreducible]
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

private def localizedLeft (d : GeometricData J K A) (x : ExactData d)
    (o : OrdinaryIdentification d) :
    d.pullR.mapDerivedCategory ⋙ onDerived K A ≅
      onDerived J A ⋙ d.pullA.mapDerivedCategory :=
  ConstantModuleDerivedSquare.normalizedLeft o.left
private theorem localizedLeft_fac (d : GeometricData J K A) (x : ExactData d)
    (o : OrdinaryIdentification d) : LeftLocalizationSquare d x o (localizedLeft d x o) :=
  ConstantModuleDerivedSquare.normalizedLeft_fac o.left
private def localizedRight (d : GeometricData J K A) (x : ExactData d)
    (o : OrdinaryIdentification d) :
    d.pushR.rightDerivedFunctor ⋙ onDerived J A ≅
      onDerived K A ⋙ d.pushA.rightDerivedFunctor :=
  ConstantModuleDerivedSquare.normalizedRight d.ringAdj d.fixedAdj o.left
private theorem localizedRight_fac (d : GeometricData J K A) (x : ExactData d)
    (o : OrdinaryIdentification d) : RightLocalizationSquare d x o (localizedRight d x o) :=
  ConstantModuleDerivedSquare.normalizedRight_fac d.ringAdj d.fixedAdj o.left o.right
    (ConstantModuleDerivedSquare.ordinaryMate_eq d.ringAdj d.fixedAdj o.left o.right o.hom)
private theorem localizedHom (d : GeometricData J K A) (x : ExactData d)
    (o : OrdinaryIdentification d) :
    ∀ (M : DerivedCategory (Modules J A)) (N : DerivedCategory (Modules K A))
      (f : d.pullR.mapDerivedCategory.obj M ⟶ N),
      d.fixedAdj.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _
        ((localizedLeft d x o).inv.app M ≫ (onDerived K A).map f) =
      (onDerived J A).map
        (d.ringAdj.mapDerivedCategoryRightDerivedAdjunction.homEquiv M N f) ≫
          (localizedRight d x o).hom.app N :=
  ConstantModuleDerivedSquare.normalizedDerivedHom d.ringAdj d.fixedAdj o.left

-- This interface avoids unfolding the concrete localization witnesses during assembly.
private theorem derivedIdentification_of_squares (d : GeometricData J K A) (x : ExactData d)
    (o : OrdinaryIdentification d) (t : FixedTensorData d)
    (cJ : DerivedComparison.{u, v, w, w} J A)
    (cK : DerivedComparison.{u, v, w, w} K A)
    (i : d.pullR.mapDerivedCategory ⋙ onDerived K A ≅
      onDerived J A ⋙ d.pullA.mapDerivedCategory)
    (j : d.pushR.rightDerivedFunctor ⋙ onDerived J A ≅
      onDerived K A ⋙ d.pushA.rightDerivedFunctor)
    (hi : LeftLocalizationSquare d x o i) (hj : RightLocalizationSquare d x o j)
    (ha : AdjunctionSquare d.pullR.mapDerivedCategory d.pushR.rightDerivedFunctor
      d.pullA.mapDerivedCategory d.pushA.rightDerivedFunctor
      d.ringAdj.mapDerivedCategoryRightDerivedAdjunction
      d.fixedAdj.mapDerivedCategoryRightDerivedAdjunction
      (onDerived J A) (onDerived K A) i j) :
    Nonempty (DerivedIdentification d x o t cJ cK) := by
  obtain ⟨tensor, ht⟩ := constant_module_tensor_square_descent d x o t cJ cK i hi
  exact ⟨{
    left := i
    right := j
    tensor := tensor
    left_normalized := hi
    right_normalized := hj
    tensor_square := ht
    adjunction := ha
    projection := projectionSquare_of_tensor_adjunction
      d.ringAdj.mapDerivedCategoryRightDerivedAdjunction
      d.fixedAdj.mapDerivedCategoryRightDerivedAdjunction
      (onDerived J A) (onDerived K A)
      tensor.val.1 tensor.val.2.2 cJ.val cK.val i j ht ha }⟩

private theorem derivedIdentification_exists (d : GeometricData J K A) (x : ExactData d)
    (o : OrdinaryIdentification d) (t : FixedTensorData d)
    (cJ : DerivedComparison.{u, v, w, w} J A)
    (cK : DerivedComparison.{u, v, w, w} K A) :
    Nonempty (DerivedIdentification d x o t cJ cK) := by
  exact derivedIdentification_of_squares d x o t cJ cK
    (localizedLeft d x o) (localizedRight d x o)
    (localizedLeft_fac d x o) (localizedRight_fac d x o)
    (adjunctionSquare_of_hom
      d.ringAdj.mapDerivedCategoryRightDerivedAdjunction
      d.fixedAdj.mapDerivedCategoryRightDerivedAdjunction
      (onDerived J A) (onDerived K A)
      (localizedLeft d x o) (localizedRight d x o) (localizedHom d x o))

/-- Constant scalar restriction identifies the canonical derived adjunction, tensors,
projection maps, and bounded-below restrictions for a geometric morphism.
Source: Stacks Tags 03EL, 07A4, 07A6, 013K and 070J
(blueprint: lem-sfb-constant-module-derived-projection-identification).
Proof: obtain the normalized ordinary comparison and fixed tensor data from
constant_module_ordinary_realization. Reflect finite limits along the underlying
fixed-module sheaf functor and the scalar equivalence; adjunctions provide colimits.
Localize the ordinary left comparison by the exact-functor composition isomorphisms.
Its derived adjunction mate is invertible since scalar restriction is an equivalence.
The exact derived-mate factorization proves the right localization square, while
the unit-mate equation and naturality prove the full Hom equation. Identities give
the unit and counit squares. Apply constant_module_tensor_square_descent for the
two normalized derived tensor structures and their scalar square. The abstract
projection-map mate equation gives precisely the projection square. Finally restrict
the unbounded adjunction along the fully faithful bounded-below inclusions. Its unit
has the canonical plus localization equation, so uniqueness identifies it with
derivedPlus. The restriction Hom and counit formulas prove all plus equations. -/
theorem constant_module_derived_projection_identification [Finite A]
    (d : GeometricData J K A) :
    ∃ x : ExactData d, ∃ o : OrdinaryIdentification d, ∃ t : FixedTensorData d,
      ∀ (cJ : DerivedComparison.{u, v, w, w} J A)
      (cK : DerivedComparison.{u, v, w, w} K A),
        Nonempty (Σ e : DerivedIdentification d x o t cJ cK,
          PlusIdentification d x o t cJ cK e) := by
  obtain ⟨o, ⟨t⟩⟩ := constant_module_ordinary_realization d
  obtain ⟨x⟩ := exactData_of_tensor d o t
  let := x
  refine ⟨x, o, t, ?_⟩
  intro cJ cK
  obtain ⟨e⟩ := derivedIdentification_exists d x o t cJ cK
  obtain ⟨p⟩ := plusIdentification_exists d x o t cJ cK e
  exact ⟨⟨e, p⟩⟩

end

-- Restore the recorded scalar structures for the existing etale data interface.
attribute [instance] CategoryTheory.ConstantScalarRestriction.ringPreadditive
  CategoryTheory.ConstantScalarRestriction.fixedPreadditive
  CategoryTheory.ConstantScalarRestriction.ringZeroMorphisms
  CategoryTheory.ConstantScalarRestriction.fixedZeroMorphisms

/-- The etale instance of the normalized tensor, adjunction and projection comparison.
Its left and right normalizations are the canonical derived comparison isomorphisms.
The monoidal structure supplied below has exactly the published tensor comparison,
and its adjunction projection map is the published etale projection-formula map.
Source: Stacks Tags 07A4 and 07A6
(blueprint: lem-sfb-constant-module-derived-projection-identification). -/
def EtaleIdentification {X Y : AlgebraicGeometry.Scheme.{z}} (f : X ⟶ Y)
    (B : Type (z + 1)) [CommRing B]
    (d : GeometricData Y.smallEtaleTopology X.smallEtaleTopology B) (x : ExactData d)
    (o : OrdinaryIdentification d) (t : FixedTensorData d)
    (cY : DerivedComparison.{z + 1, z, z + 1, z + 1} Y.smallEtaleTopology B)
    (cX : DerivedComparison.{z + 1, z, z + 1, z + 1} X.smallEtaleTopology B)
    (e : DerivedIdentification d x o t cY cX)
    (hL : d.pullA = AlgebraicGeometry.Etale.upperStar (ModuleCat.{z + 1} B) f)
    (hR : d.pushA = AlgebraicGeometry.Etale.lowerStar (ModuleCat.{z + 1} B) f) :=
  NormalizedComparison
    d.pullA.mapDerivedCategory d.pushA.rightDerivedFunctor
    (AlgebraicGeometry.Etale.upperStar (ModuleCat.{z + 1} B) f).leftDerivedFunctor
    (AlgebraicGeometry.Etale.lowerStar (ModuleCat.{z + 1} B) f).rightDerivedFunctor
    d.fixedAdj.mapDerivedCategoryRightDerivedAdjunction
    (AlgebraicGeometry.Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{z + 1} B) f)
    (𝟭 _) (𝟭 _) inferInstance inferInstance
    (fun left ↦ left = Functor.mapDerivedCategoryNatIso (eqToIso hL) ≪≫
      (AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory
        (ModuleCat.{z + 1} B) f).symm)
    (fun right ↦ right = Functor.rightDerivedFunctorNatIso (eqToIso hR))
    (fun _ ↦ PUnit)
    (fun _ _ ↦ e.tensor.val.2.2)
    (fun _ _ ↦ AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal (ModuleCat.{z + 1} B) f)

private theorem etaleAdjunctionSquare
    {X Y : AlgebraicGeometry.Scheme.{z}} (f : X ⟶ Y)
    (B : Type (z + 1)) [CommRing B]
    {L : Fixed Y.smallEtaleTopology B ⥤ Fixed X.smallEtaleTopology B}
    {R : Fixed X.smallEtaleTopology B ⥤ Fixed Y.smallEtaleTopology B}
    [L.Additive] [R.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (a : L ⊣ R)
    (hL : L = AlgebraicGeometry.Etale.upperStar (ModuleCat.{z + 1} B) f)
    (hR : R = AlgebraicGeometry.Etale.lowerStar (ModuleCat.{z + 1} B) f)
    (ha : HEq a
      (AlgebraicGeometry.Etale.upperStarLowerStarAdjunction (ModuleCat.{z + 1} B) f)) :
    AdjunctionSquare L.mapDerivedCategory R.rightDerivedFunctor
      (AlgebraicGeometry.Etale.upperStar (ModuleCat.{z + 1} B) f).leftDerivedFunctor
      (AlgebraicGeometry.Etale.lowerStar (ModuleCat.{z + 1} B) f).rightDerivedFunctor
      a.mapDerivedCategoryRightDerivedAdjunction
      (AlgebraicGeometry.Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{z + 1} B) f)
      (𝟭 _) (𝟭 _)
      (Functor.mapDerivedCategoryNatIso (eqToIso hL) ≪≫
        (AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory
          (ModuleCat.{z + 1} B) f).symm)
      (Functor.rightDerivedFunctorNatIso (eqToIso hR)) := by
  subst L
  subst R
  have ha' := eq_of_heq ha
  subst a
  apply adjunctionSquare_of_hom
  intro M N g
  have h := AlgebraicGeometry.Etale.mapDerivedUpperStarLowerStarAdjunction_eq
    (ModuleCat.{z + 1} B) f
  change _ =
    (AlgebraicGeometry.Etale.mapDerivedUpperStarLowerStarAdjunction
      (ModuleCat.{z + 1} B) f).homEquiv M N g ≫ _
  rw [h, Adjunction.homEquiv_ofNatIsoLeft_apply]
  simp [Functor.mapDerivedCategoryNatIso, Localization.liftNatIso,
    NatIso.mapHomologicalComplex, Functor.rightDerivedFunctorNatIso,
    Functor.rightDerivedFunctorNatTrans]

/-- For the small etale geometric morphism the scalar comparison identifies the published
inverse image, its canonical tensor comparison and the projection-formula morphism.
Source: Stacks Tags 07A4 and 07A6
(blueprint: lem-sfb-constant-module-derived-projection-identification).
Proof: apply etaleInverseImageModulesExact to construct the ring lift, constant-section
isomorphism, module action and abelian-normalized module adjunction. Use the constant
module equivalences to obtain the ordinary geometric datum. Apply the general comparison
above, choosing derived_comparison for both scalar equivalences. The canonical etale
left-derived/termwise isomorphism and the identity ordinary direct-image comparison
identify the derived Hom bijections. The etale tensor comparison is the localization of
the same ordinary pure-tensor map on flat-term K-flat representatives (07A4), so its
comparison square commutes by two-variable resolving descent. Finally the published
rightDerivedLowerStarProjectionMap is the adjunct of exactly this comparison followed
by counit tensor identity. Agreement of Hom bijections identifies the projection maps.
The bounded-below compatibility is the one already supplied by the general comparison. -/
theorem etale_constant_module_derived_projection_identification
    {X Y : AlgebraicGeometry.Scheme.{z}} (f : X ⟶ Y)
    (B : Type (z + 1)) [CommRing B] [Finite B] :
    ∃ d : GeometricData Y.smallEtaleTopology X.smallEtaleTopology B,
      d.inverse = AlgebraicGeometry.Scheme.etaleSetPullback f ∧
      d.direct = AlgebraicGeometry.Etale.lowerStar (Type (z + 1)) f ∧
      ∃ (hL : d.pullA = AlgebraicGeometry.Etale.upperStar (ModuleCat.{z + 1} B) f)
        (hR : d.pushA = AlgebraicGeometry.Etale.lowerStar (ModuleCat.{z + 1} B) f),
        HEq d.fixedAdj
          (AlgebraicGeometry.Etale.upperStarLowerStarAdjunction (ModuleCat.{z + 1} B) f) ∧
        ∃ (x : ExactData d) (o : OrdinaryIdentification d) (t : FixedTensorData d)
          (cY : DerivedComparison.{z + 1, z, z + 1, z + 1} Y.smallEtaleTopology B)
          (cX : DerivedComparison.{z + 1, z, z + 1, z + 1} X.smallEtaleTopology B)
          (e : DerivedIdentification d x o t cY cX),
          Nonempty (PlusIdentification d x o t cY cX e) ∧
          Nonempty (EtaleIdentification f B d x o t cY cX e hL hR) := by
  obtain ⟨d, hi, hd, hL, hR, ha, t, hm⟩ :=
    etale_constant_module_geometric_realization f B
  obtain ⟨o, _⟩ := constant_module_ordinary_realization d
  obtain ⟨x⟩ := exactData_of_tensor d o t
  let := x
  obtain ⟨cY⟩ := derived_comparison Y.smallEtaleTopology B
  obtain ⟨cX⟩ := derived_comparison X.smallEtaleTopology B
  obtain ⟨e⟩ := derivedIdentification_exists d x o t cY cX
  obtain ⟨p⟩ := plusIdentification_exists d x o t cY cX e
  refine ⟨d, hi, hd, hL, hR, ha, x, o, t, cY, cX, e, ⟨p⟩, ?_⟩
  let i := Functor.mapDerivedCategoryNatIso (eqToIso hL) ≪≫
    (AlgebraicGeometry.Etale.leftDerivedUpperStarIsoMapDerivedCategory
      (ModuleCat.{z + 1} B) f).symm
  let j := Functor.rightDerivedFunctorNatIso (eqToIso hR)
  have ht := etale_constant_module_tensor_normalization f B d x t hL hm
    e.tensor.val.2.2 e.tensor.property.2.2
  have haD := etaleAdjunctionSquare f B d.fixedAdj hL hR ha
  refine ⟨{
    left := i
    right := j
    tensor := PUnit.unit
    left_normalized := rfl
    right_normalized := rfl
    tensor_square := ht
    adjunction := haD
    projection := ?_ }⟩
  exact projectionSquare_of_tensor_adjunction
    d.fixedAdj.mapDerivedCategoryRightDerivedAdjunction
    (AlgebraicGeometry.Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{z + 1} B) f)
    (𝟭 _) (𝟭 _) e.tensor.val.2.2
    (AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal (ModuleCat.{z + 1} B) f)
    inferInstance inferInstance i j ht haD

end CategoryTheory.ConstantModuleDerivedProjection
