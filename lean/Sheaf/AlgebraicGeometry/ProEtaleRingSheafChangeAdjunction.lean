/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all Sheaf.AlgebraicGeometry.ProEtaleOperations
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import Sheaf.AlgebraicGeometry.ProEtaleModuleInverseImageCanonicalUnit
import WeilConjectures.Mathlib.CategoryTheory.Functor.Derived.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-!
# Compatible changes of ring sheaves and derived adjunctions

Source: Stacks Project, Cohomology on Sites, Tags 0D6D, 0D6E and 07A6;
Modules on Sites, lemma-adjoint-push-pull-modules
(blueprint: lem-weil-pbc-ring-sheaf-change-adjunction).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

private theorem exactSquare_factorsh
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (L : A ⥤ B) (L' : C ⥤ D) (G : A ⥤ C) (H : B ⥤ D)
    [L.Additive] [L'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (s : G ⋙ L' ≅ L ⋙ H) (K : HomotopyCategory A (.up ℤ)) :
    ((Functor.mapDerivedCategoryCompIso G L').symm ≪≫
        Functor.mapDerivedCategoryNatIso s ≪≫ Functor.mapDerivedCategoryCompIso L H).hom.app
          (DerivedCategory.Qh.obj K) ≫
        H.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app K) ≫
        H.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj K) =
      L'.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app K) ≫
        L'.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ L')) (.up ℤ)).hom.app K ≫
            (NatTrans.mapHomotopyCategory s.hom (.up ℤ)).app K ≫
            (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).inv.app K) := by
  have h₁ := Functor.mapDerivedCategoryCompIso_fach L H K
  have h₂ := Functor.mapDerivedCategoryCompIso_fach G L' K
  have h₃ := Functor.mapDerivedCategoryNatIso_fach s K
  apply (cancel_mono (DerivedCategory.Qh.map
    ((Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).hom.app K))).1
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [h₁, h₃, ← h₂]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_app_assoc]
  have hc : DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).inv.app K) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).hom.app K) = 𝟙 _ := by
    rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  rw [hc, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem homotopy_mate
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H)
    (K : HomotopyCategory B (.up ℤ)) :
    (mateEquiv (adj.mapHomotopyCategory (.up ℤ)) (adj'.mapHomotopyCategory (.up ℤ))
      (TwoSquare.mk _ _ _ _
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ L')) (.up ℤ)).hom ≫
          NatTrans.mapHomotopyCategory s.hom (.up ℤ) ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).inv))).app K =
      (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ G)) (.up ℤ)).hom.app K ≫
        (NatTrans.mapHomotopyCategory
          (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)).natTrans (.up ℤ)).app K ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (H ⋙ R')) (.up ℤ)).inv.app K := by
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [mateEquiv_apply, TwoSquare.mk, NatTrans.comp_app, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp]
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  change (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _ =
    (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C (.up ℤ)).map _
  simp only [← CategoryTheory.Functor.map_comp]
  congr 1
  ext n
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Adjunction.mapHomologicalComplex_unit_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f, Functor.mapHomologicalComplexCompIso]
  simp only [ NatTrans.comp_app, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp]
  simp only [Functor.id_obj, NatIso.mapHomologicalComplex_hom_app_f, Iso.refl_hom,
    NatTrans.id_app, Functor.comp_obj, NatIso.mapHomologicalComplex_inv_app_f, Iso.refl_inv,
    Functor.map_comp, HomologicalComplex.id_f, Category.comp_id, Category.assoc,
    Functor.comp_map]
  change adj'.unit.app (G.obj (R.obj (K.X n))) ≫
      R'.map (𝟙 (L'.obj (G.obj (R.obj (K.X n))))) ≫
      R'.map (s.hom.app (R.obj (K.X n))) ≫
      R'.map (𝟙 (H.obj (L.obj (R.obj (K.X n))))) ≫
      R'.map (H.map (adj.counit.app (K.X n))) =
    𝟙 _ ≫ adj'.unit.app (G.obj (R.obj (K.X n))) ≫
      R'.map (s.hom.app (R.obj (K.X n))) ≫
      R'.map (H.map (adj.counit.app (K.X n))) ≫ 𝟙 _
  simp only [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  erw [R'.map_id, Category.id_comp, Category.id_comp]

private theorem derived_mate_factorsh
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H)
    (K : HomotopyCategory B (.up ℤ)) :
    G.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
      (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
        adj'.mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _
          ((Functor.mapDerivedCategoryCompIso G L').symm ≪≫
            Functor.mapDerivedCategoryNatIso s ≪≫
            Functor.mapDerivedCategoryCompIso L H).hom)).app (DerivedCategory.Qh.obj K) ≫
      R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactorsh.hom.app K) =
    G.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map
        ((Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ G)) (.up ℤ)).hom.app K ≫
          (NatTrans.mapHomotopyCategory
            (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)).natTrans (.up ℤ)).app K ≫
          (Functor.mapHomotopyCategoryCompIso (Iso.refl (H ⋙ R')) (.up ℤ)).inv.app K) ≫
      R'.rightDerivedFunctorUnit.app ((H.mapHomotopyCategory (.up ℤ)).obj K) := by
  rw [← homotopy_mate adj adj' s K]
  exact Adjunction.derived_mateEquiv_app_fac
    (adj.mapHomotopyCategory (.up ℤ)) (adj'.mapHomotopyCategory (.up ℤ))
    (HomotopyCategory.quasiIso A (.up ℤ)) (HomotopyCategory.quasiIso B (.up ℤ))
    (HomotopyCategory.quasiIso C (.up ℤ)) (HomotopyCategory.quasiIso D (.up ℤ))
    L.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctorUnit
    L'.mapDerivedCategoryFactorsh.hom R'.rightDerivedFunctorUnit
    G.mapDerivedCategoryFactorsh.hom H.mapDerivedCategoryFactorsh.hom
    (TwoSquare.mk _ _ _ _
      ((Functor.mapHomotopyCategoryCompIso (Iso.refl (G ⋙ L')) (.up ℤ)).hom ≫
        NatTrans.mapHomotopyCategory s.hom (.up ℤ) ≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (L ⋙ H)) (.up ℤ)).inv))
    (TwoSquare.mk _ _ _ _
      ((Functor.mapDerivedCategoryCompIso G L').symm ≪≫
        Functor.mapDerivedCategoryNatIso s ≪≫ Functor.mapDerivedCategoryCompIso L H).hom)
    K (exactSquare_factorsh L L' G H s _)

private noncomputable def chainDerivedUnit
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    [HasDerivedCategory A] [HasDerivedCategory B] [Abelian.HasKInjectiveResolutions A]
    (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ) :
    DerivedCategory.Q.obj ((F.mapHomologicalComplex (.up ℤ)).obj K) ⟶
      F.rightDerivedFunctor.obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso B).inv.app _ ≫
    F.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K) ≫
    F.rightDerivedFunctor.map ((DerivedCategory.quotientCompQhIso A).hom.app K)

private theorem quotient_hom_id {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (K : CochainComplex A ℤ) :
    (DerivedCategory.quotientCompQhIso A).hom.app K = 𝟙 (DerivedCategory.Q.obj K) := rfl

private theorem quotient_inv_id {A : Type*} [Category A] [Abelian A]
    [HasDerivedCategory A] (K : CochainComplex A ℤ) :
    (DerivedCategory.quotientCompQhIso A).inv.app K = 𝟙 (DerivedCategory.Q.obj K) := rfl

private theorem homotopyFactors_inv_id
    {A B : Type*} [Category A] [Category B] [Abelian A] [Abelian B]
    (F : A ⥤ B) [F.Additive] (K : CochainComplex A ℤ) :
    (F.mapHomotopyCategoryFactors (.up ℤ)).inv.app K =
      𝟙 ((HomotopyCategory.quotient B (.up ℤ)).obj
        ((F.mapHomologicalComplex (.up ℤ)).obj K)) := rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_mate_factors
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions B] [Abelian.HasKInjectiveResolutions D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [H.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : G ⋙ L' ≅ L ⋙ H)
    (K : CochainComplex B ℤ) :
    G.mapDerivedCategory.map (chainDerivedUnit R K) ≫
      (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
        adj'.mapDerivedCategoryRightDerivedAdjunction
        (TwoSquare.mk _ _ _ _
          ((Functor.mapDerivedCategoryCompIso G L').symm ≪≫
            Functor.mapDerivedCategoryNatIso s ≪≫
            Functor.mapDerivedCategoryCompIso L H).hom)).app (DerivedCategory.Q.obj K) ≫
      R'.rightDerivedFunctor.map (H.mapDerivedCategoryFactors.hom.app K) =
    G.mapDerivedCategoryFactors.hom.app ((R.mapHomologicalComplex (.up ℤ)).obj K) ≫
      DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex
          (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)).natTrans (.up ℤ)).app K) ≫
      chainDerivedUnit R' ((H.mapHomologicalComplex (.up ℤ)).obj K) := by
  have hf := derived_mate_factorsh adj adj' s ((HomotopyCategory.quotient _ _).obj K)
  have hG := G.mapDerivedCategoryFactorsh_hom_app
    ((R.mapHomologicalComplex (.up ℤ)).obj K)
  change G.mapDerivedCategoryFactorsh.hom.app
      ((R.mapHomotopyCategory (.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj K)) = _ at hG
  rw [hG] at hf
  have hq : (Functor.mapHomotopyCategoryCompIso (Iso.refl (R ⋙ G)) (.up ℤ)).hom.app
      ((HomotopyCategory.quotient _ _).obj K) = 𝟙 _ := rfl
  have hq' : (Functor.mapHomotopyCategoryCompIso (Iso.refl (H ⋙ R')) (.up ℤ)).inv.app
      ((HomotopyCategory.quotient _ _).obj K) = 𝟙 _ := rfl
  have hτ : DerivedCategory.Qh.map
      ((NatTrans.mapHomotopyCategory
        (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)).natTrans (.up ℤ)).app
          ((HomotopyCategory.quotient _ _).obj K)) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ s.hom)).natTrans (.up ℤ)).app K) := rfl
  simp only [Functor.mapDerivedCategoryFactorsh_hom_app, hq, hq', hτ,
    chainDerivedUnit, quotient_hom_id, quotient_inv_id, homotopyFactors_inv_id,
    CategoryTheory.Functor.map_comp, Category.assoc] at hf ⊢
  repeat first
    | erw [G.mapDerivedCategory.map_id] at hf
    | erw [H.mapDerivedCategory.map_id] at hf
    | erw [R'.rightDerivedFunctor.map_id] at hf
    | erw [(DerivedCategory.Qh (C := C)).map_id] at hf
    | erw [(DerivedCategory.Qh (C := D)).map_id] at hf
    | erw [Category.id_comp] at hf
    | erw [Category.comp_id] at hf
  repeat first
    | erw [G.mapDerivedCategory.map_id]
    | erw [R.rightDerivedFunctor.map_id]
    | erw [R'.rightDerivedFunctor.map_id]
    | erw [Category.id_comp]
    | erw [Category.comp_id]
  exact hf

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_comp_ext
    {A B C : Type*} [Category A] [Category B] [Category C]
    [Abelian A] [Abelian B] [Abelian C]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [Abelian.HasKInjectiveResolutions A]
    (R : A ⥤ B) (G : B ⥤ C) [R.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (T : DerivedCategory A ⥤ DerivedCategory C)
    (x y : R.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶ T)
    (h : ∀ K : CochainComplex A ℤ,
      G.mapDerivedCategory.map (chainDerivedUnit R K) ≫ x.app (DerivedCategory.Q.obj K) =
      G.mapDerivedCategory.map (chainDerivedUnit R K) ≫ y.app (DerivedCategory.Q.obj K)) :
    x = y := by
  apply Functor.rightDerived_ext (R.rightDerivedFunctor ⋙ G.mapDerivedCategory)
    (Functor.rightDerivedFunctorCompMapDerivedCategoryUnit R G)
    (HomotopyCategory.quasiIso A (.up ℤ)) T x y
  apply NatTrans.ext
  funext K
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have hx := x.naturality ((DerivedCategory.quotientCompQhIso A).hom.app K)
  have hy := y.naturality ((DerivedCategory.quotientCompQhIso A).hom.app K)
  dsimp only [Functor.comp_map] at hx hy
  have hk := h K
  dsimp only [chainDerivedUnit] at hk
  simp only [Functor.map_comp, Category.assoc] at hk
  erw [hx, hy] at hk
  have hk' := (cancel_epi (G.mapDerivedCategory.map
    ((DerivedCategory.quotientCompQhIso B).inv.app
      ((R.mapHomologicalComplex (.up ℤ)).obj K)))).mp hk
  have hk'' := (cancel_mono
    (T.map ((DerivedCategory.quotientCompQhIso A).hom.app K))).mp
      (by simpa only [← Category.assoc] using hk')
  dsimp [Functor.rightDerivedFunctorCompMapDerivedCategoryUnit]
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  erw [hk'']
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem mate_adjunct
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    {L : A ⥤ B} {R : B ⥤ A} {L' : C ⥤ D} {R' : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (s : TwoSquare G L L' H)
    (M : A) (N : B) (t : L.obj M ⟶ N) :
    adj'.homEquiv _ _ (s.app M ≫ H.map t) =
      G.map (adj.homEquiv M N t) ≫ (mateEquiv adj adj' s).app N := by
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hu := unit_mateEquiv adj adj' s M
  dsimp only [Functor.id_obj] at hu
  rw [← Category.assoc, ← hu, Category.assoc]
  have hn := (mateEquiv adj adj' s).natTrans.naturality t
  dsimp only [Functor.comp_map] at hn
  rw [← hn, ← Category.assoc, ← G.map_comp]

private theorem isoOfAdjunct
    {A B : Type*} [Category A] [Category B] {L : A ⥤ B} {R : B ⥤ A}
    (adj : L ⊣ R) {X : A} {Y Z : B} (g : X ⟶ R.obj Y) (h : X ⟶ R.obj Z)
    (k : Y ⟶ Z) (hg : IsIso ((adj.homEquiv X Y).symm g))
    (hh : IsIso ((adj.homEquiv X Z).symm h)) (hk : g ≫ R.map k = h) : IsIso k := by
  let := hg
  let := hh
  have : IsIso ((adj.homEquiv X Y).symm g ≫ k) := by
    rw [← adj.homEquiv_naturality_right_symm, hk]
    exact hh
  exact IsIso.of_isIso_comp_left ((adj.homEquiv X Y).symm g) k

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ringUnitComparison
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (adj : proEtaleRingModulePullback f R S c ⊣ proEtaleRingModuleDirectImage f R S c)
    (M : proEtaleRingModules Y R) :
    IsIso (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv
      ((SheafOfModules.toSheaf _).obj M)
      ((SheafOfModules.toSheaf _).obj ((proEtaleRingModulePullback f R S c).obj M))).symm
        ((SheafOfModules.toSheaf _).map (adj.unit.app M))) := by
  let A := (sheafCompose (ProEt.topology Y)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let B := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
      ((proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R)
  let C := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let P := SheafOfModules.toSheaf.{u + 1} A
  let Q := SheafOfModules.toSheaf.{u + 1} B
  let Q' := SheafOfModules.toSheaf.{u + 1} C
  let a := proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}
  obtain ⟨a₀, h₀⟩ := proEtaleModuleInverseImage_canonicalUnitComparison f R
  let rc := (sheafCompose (ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).mapIso c
  let a₁ : proEtaleRingExtension f R S c ⊣
      SheafOfModules.restrictScalars.{u + 1} rc.hom :=
    proEtaleRingExtensionAdjunction f R S c
  have : (SheafOfModules.restrictScalars.{u + 1} rc.hom).IsEquivalence :=
    inferInstanceAs (proEtaleScalarEquivalence X rc).functor.IsEquivalence
  have : IsIso a₁.unit := by infer_instance
  have : IsIso (a₁.unit.app ((proEtaleModuleInverseImage f R).obj M)) := inferInstance
  let ac := a₀.comp a₁
  change proEtaleRingModulePullback f R S c ⊣ _ at ac
  let T := SheafOfModules.pushforward.{u + 1} (F := proEtaleBaseChange f)
    (J := ProEt.topology Y) (K := ProEt.topology X) (S := A) (R := B)
      ⟨Functor.whiskerRight ((proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.app R).hom
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})⟩
  let er : SheafOfModules.restrictScalars rc.hom ⋙ T ≅
      proEtaleRingModuleDirectImage f R S c := by
    refine NatIso.ofComponents (fun N ↦ ?_) ?_
    · apply (SheafOfModules.fullyFaithfulForget _).preimageIso
      exact PresheafOfModules.isoMk (fun U ↦ Iso.refl _) (by intros; rfl)
    · intro N N' h
      apply SheafOfModules.hom_ext
      apply PresheafOfModules.hom_ext
      intro U
      rfl
  let ab := ac.ofNatIsoRight er
  let β₀ := (a.homEquiv (P.obj M)
    (Q.obj ((proEtaleModuleInverseImage f R).obj M))).symm
      (P.map (a₀.unit.app M))
  have : IsIso β₀ := h₀ M
  let k := Q.map (a₁.unit.app ((proEtaleModuleInverseImage f R).obj M))
  have : IsIso k := inferInstance
  have he : (a.homEquiv (P.obj M)
      (Q'.obj ((proEtaleRingModulePullback f R S c).obj M))).symm
        (P.map (ab.unit.app M)) = β₀ ≫ k := by
    rw [← a.homEquiv_naturality_right_symm]
    congr 1
  have hb : IsIso ((a.homEquiv (P.obj M)
      (Q'.obj ((proEtaleRingModulePullback f R S c).obj M))).symm
        (P.map (ab.unit.app M))) := by
    rw [he]
    infer_instance
  let e := ab.leftAdjointUniq adj
  have hu := Adjunction.unit_leftAdjointUniq_hom_app ab adj M
  have hh : (a.homEquiv (P.obj M)
      (Q'.obj ((proEtaleRingModulePullback f R S c).obj M))).symm
        (P.map (adj.unit.app M)) =
      (a.homEquiv (P.obj M)
        (Q'.obj ((proEtaleRingModulePullback f R S c).obj M))).symm
          (P.map (ab.unit.app M)) ≫ Q'.map (e.hom.app M) := by
    rw [← a.homEquiv_naturality_right_symm]
    congr 1
    rw [← hu, P.map_comp]
    rfl
  change IsIso ((a.homEquiv (P.obj M)
      (Q'.obj ((proEtaleRingModulePullback f R S c).obj M))).symm
        (P.map (adj.unit.app M)))
  rw [hh]
  infer_instance



/-- Restriction along a commutative ring-sheaf map on the original small site.
Source: Stacks, Modules on Sites (blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
noncomputable abbrev proEtaleRingRestrictScalars {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    proEtaleRingModules T S ⥤ proEtaleRingModules T R :=
  SheafOfModules.restrictScalars.{u + 1}
    ((sheafCompose (ProEt.topology T) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map a)

/-- Restriction is exact and conservative before deriving.
Source: Stacks, Derived Categories, Tag 05RT
(blueprint: lem-weil-pbc-ring-sheaf-change-adjunction).
Proof: restriction leaves the underlying abelian sheaf and its kernels and sheafified
cokernels unchanged. A bijective linear sheaf map has a linear inverse: apply the map
to the proposed scalar-linearity equality for its inverse. Thus restriction reflects
isomorphisms and preserves finite limits and finite colimits. -/
theorem proEtaleRingRestrictScalars_properties {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    PreservesFiniteLimits (proEtaleRingRestrictScalars a) ∧
    PreservesFiniteColimits (proEtaleRingRestrictScalars a) ∧
    (proEtaleRingRestrictScalars a).ReflectsIsomorphisms := by
  let R₀ := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj R
  let S₀ := (sheafCompose (ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj S
  let F := proEtaleRingRestrictScalars a
  have he : F ⋙ SheafOfModules.toSheaf.{u + 1} R₀ ≅ SheafOfModules.toSheaf.{u + 1} S₀ := Iso.refl _
  have : F.ReflectsIsomorphisms := by
    have : (F ⋙ SheafOfModules.toSheaf.{u + 1} R₀).ReflectsIsomorphisms :=
      reflectsIsomorphisms_of_iso he.symm
    exact reflectsIsomorphisms_of_comp F (SheafOfModules.toSheaf.{u + 1} R₀)
  have : PreservesFiniteLimits F := by
    have : PreservesFiniteLimits (F ⋙ SheafOfModules.toSheaf.{u + 1} R₀) :=
      preservesFiniteLimits_of_natIso he.symm
    exact preservesFiniteLimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{u + 1} R₀)
  have : ReflectsFiniteColimits (SheafOfModules.toSheaf.{u + 1} R₀) :=
    { reflects := fun _ ↦ reflectsColimitsOfShape_of_reflectsIsomorphisms }
  have : PreservesFiniteColimits F := by
    have : PreservesFiniteColimits (F ⋙ SheafOfModules.toSheaf.{u + 1} R₀) :=
      preservesFiniteColimits_of_natIso he.symm
    exact preservesFiniteColimits_of_reflects_of_preserves F (SheafOfModules.toSheaf.{u + 1} R₀)
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Left exactness of restriction. Source: Stacks, Tag 05RT
(blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
theorem proEtaleRingRestrictScalars_preservesFiniteLimits {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    PreservesFiniteLimits (proEtaleRingRestrictScalars a) :=
  (proEtaleRingRestrictScalars_properties a).1

attribute [local instance] proEtaleRingRestrictScalars_preservesFiniteLimits

/-- Right exactness of restriction. Source: Stacks, Tag 05RT
(blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
theorem proEtaleRingRestrictScalars_preservesFiniteColimits {T : Scheme.{u}}
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (a : R ⟶ S) :
    PreservesFiniteColimits (proEtaleRingRestrictScalars a) :=
  (proEtaleRingRestrictScalars_properties a).2.1

attribute [local instance] proEtaleRingRestrictScalars_preservesFiniteColimits

variable {U V : Scheme.{u}} (f : U ⟶ V)
  (RV SV : Sheaf (ProEt.topology V) CommRingCat.{u + 1})
  (RU SU : Sheaf (ProEt.topology U) CommRingCat.{u + 1})
  (aV : RV ⟶ SV) (aU : RU ⟶ SU)
  (cR : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj RV ≅ RU)
  (cS : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj SV ≅ SU)
  (comm : cR.hom ≫ aU = (proEtaleSheafInverseImage f CommRingCat.{u + 1}).map aV ≫ cS.hom)

include comm in
private theorem restrictionDirectImageMap_square :
    aV ≫ proEtaleRingDirectImageMap f SV SU cS =
      proEtaleRingDirectImageMap f RV RU cR ≫
        (proEtaleSheafDirectImage f CommRingCat.{u + 1}).map aU := by
  dsimp [proEtaleRingDirectImageMap]
  have hn := (proEtaleSheafAdjunction f CommRingCat.{u + 1}).unit.naturality aV
  simp only [Functor.id_map, Functor.comp_map] at hn
  rw [← Category.assoc, hn]
  rw [Category.assoc, ← Functor.map_comp, ← comm, Functor.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include comm in
private noncomputable def restrictionDirectImageHom (N : proEtaleRingModules U SU) :
    ((proEtaleRingModuleDirectImage f SV SU cS ⋙ proEtaleRingRestrictScalars aV).obj N) ⟶
      ((proEtaleRingRestrictScalars aU ⋙ proEtaleRingModuleDirectImage f RV RU cR).obj N) where
  val :=
    { app W := ModuleCat.ofHom
        (X := ((proEtaleRingModuleDirectImage f SV SU cS ⋙
          proEtaleRingRestrictScalars aV).obj N).val.obj W)
        (Y := ((proEtaleRingRestrictScalars aU ⋙
          proEtaleRingModuleDirectImage f RV RU cR).obj N).val.obj W)
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro r n
            change (proEtaleRingDirectImageMap f SV SU cS).hom.app W
                (aV.hom.app W r) • (show N.val.obj ((proEtaleBaseChange f).op.obj W) from n) =
              aU.hom.app ((proEtaleBaseChange f).op.obj W)
                ((proEtaleRingDirectImageMap f RV RU cR).hom.app W r) •
                (show N.val.obj ((proEtaleBaseChange f).op.obj W) from n)
            congr 1
            exact congrArg (fun h ↦ h.hom.app W r)
              (restrictionDirectImageMap_square f RV SV RU SU aV aU cR cS comm) }
      naturality := by intros; ext n; rfl }

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
include comm in
private noncomputable def restrictionDirectImageInv (N : proEtaleRingModules U SU) :
    ((proEtaleRingRestrictScalars aU ⋙ proEtaleRingModuleDirectImage f RV RU cR).obj N) ⟶
      ((proEtaleRingModuleDirectImage f SV SU cS ⋙ proEtaleRingRestrictScalars aV).obj N) where
  val :=
    { app W := ModuleCat.ofHom
        (X := ((proEtaleRingRestrictScalars aU ⋙
          proEtaleRingModuleDirectImage f RV RU cR).obj N).val.obj W)
        (Y := ((proEtaleRingModuleDirectImage f SV SU cS ⋙
          proEtaleRingRestrictScalars aV).obj N).val.obj W)
        { toFun := id
          map_add' := fun _ _ ↦ rfl
          map_smul' := by
            intro r n
            change aU.hom.app ((proEtaleBaseChange f).op.obj W)
                ((proEtaleRingDirectImageMap f RV RU cR).hom.app W r) •
                (show N.val.obj ((proEtaleBaseChange f).op.obj W) from n) =
              (proEtaleRingDirectImageMap f SV SU cS).hom.app W
                (aV.hom.app W r) • (show N.val.obj ((proEtaleBaseChange f).op.obj W) from n)
            congr 1
            exact congrArg (fun h ↦ h.hom.app W r)
              (restrictionDirectImageMap_square f RV SV RU SU aV aU cR cS comm).symm }
      naturality := by intros; ext n; rfl }

include comm in
/-- The underived comparison is uniquely specified by identity on every section.
Source: Stacks, Tag 0D6E (blueprint: lem-weil-pbc-ring-sheaf-change-adjunction).
Proof: both composites have sections `N(U ×_V W)`. Their actions coincide by taking
adjoints of the coefficient-square identity. Identity on those sections is linear,
commutes with restrictions and module maps, and is its own inverse. Sectionwise
faithfulness determines the natural isomorphism uniquely. -/
theorem proEtaleRingRestrictionDirectImage_existsUnique :
    ∃! e : proEtaleRingModuleDirectImage f SV SU cS ⋙ proEtaleRingRestrictScalars aV ≅
        proEtaleRingRestrictScalars aU ⋙ proEtaleRingModuleDirectImage f RV RU cR,
      ∀ (N : proEtaleRingModules U SU) (W : V.ProEtᵒᵖ)
        (n : N.val.obj ((proEtaleBaseChange f).op.obj W)),
        (e.hom.app N).val.app W n = n := by
  classical
  let e : proEtaleRingModuleDirectImage f SV SU cS ⋙ proEtaleRingRestrictScalars aV ≅
      proEtaleRingRestrictScalars aU ⋙ proEtaleRingModuleDirectImage f RV RU cR :=
    NatIso.ofComponents (fun N ↦
      { hom := restrictionDirectImageHom f RV SV RU SU aV aU cR cS comm N
        inv := restrictionDirectImageInv f RV SV RU SU aV aU cR cS comm N
        hom_inv_id := by
          apply SheafOfModules.hom_ext
          apply PresheafOfModules.hom_ext
          intro W
          ext n
          rfl
        inv_hom_id := by
          apply SheafOfModules.hom_ext
          apply PresheafOfModules.hom_ext
          intro W
          ext n
          rfl }) (by
        intros
        apply SheafOfModules.hom_ext
        apply PresheafOfModules.hom_ext
        intro W
        ext n
        rfl)
  refine ⟨e, fun _ _ _ ↦ rfl, ?_⟩
  intro e' he'
  apply Iso.ext
  apply NatTrans.ext
  funext N
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  ext n
  exact he' N W n

/-- Canonical direct-image comparison, determined by the actual identity on sections.
Source: Stacks, Tag 0D6E (blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
noncomputable def proEtaleRingRestrictionDirectImage :
    proEtaleRingModuleDirectImage f SV SU cS ⋙ proEtaleRingRestrictScalars aV ≅
      proEtaleRingRestrictScalars aU ⋙ proEtaleRingModuleDirectImage f RV RU cR :=
  Classical.choose
    (proEtaleRingRestrictionDirectImage_existsUnique f RV SV RU SU aV aU cR cS comm)

/-- The inverse-image comparison before inversion is the mate of identity on sections.
Source: Stacks, lemma-adjoint-push-pull-modules
(blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
noncomputable def proEtaleRingRestrictionPullbackApp (M : proEtaleRingModules V SV) :
    (proEtaleRingModulePullback f RV RU cR).obj ((proEtaleRingRestrictScalars aV).obj M) ⟶
      (proEtaleRingRestrictScalars aU).obj ((proEtaleRingModulePullback f SV SU cS).obj M) :=
  (proEtaleRingModulePullback f RV RU cR).map
    ((proEtaleRingRestrictScalars aV).map
      ((proEtaleRingModuleAdjunction f SV SU cS).unit.app M)) ≫
  (proEtaleRingModulePullback f RV RU cR).map
    ((proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm).hom.app
      ((proEtaleRingModulePullback f SV SU cS).obj M)) ≫
  (proEtaleRingModuleAdjunction f RV RU cR).counit.app _

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem ringModuleMap_isIso
    (M : proEtaleRingModules V SV) (N : proEtaleRingModules U RU)
    (N' : proEtaleRingModules U SU)
    (g : (proEtaleRingRestrictScalars aV).obj M ⟶
      (proEtaleRingModuleDirectImage f RV RU cR).obj N)
    (h : M ⟶ (proEtaleRingModuleDirectImage f SV SU cS).obj N')
    (k : N ⟶ (proEtaleRingRestrictScalars aU).obj N')
    (hg : IsIso (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv
      ((SheafOfModules.toSheaf _).obj ((proEtaleRingRestrictScalars aV).obj M))
      ((SheafOfModules.toSheaf _).obj N)).symm ((SheafOfModules.toSheaf _).map g)))
    (hh : IsIso (((proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}).homEquiv
      ((SheafOfModules.toSheaf _).obj M)
      ((SheafOfModules.toSheaf _).obj N')).symm ((SheafOfModules.toSheaf _).map h)))
    (hk : g ≫ (proEtaleRingModuleDirectImage f RV RU cR).map k =
      (proEtaleRingRestrictScalars aV).map h ≫
        (proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm).hom.app N') :
    IsIso k := by
  let P := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (ProEt.topology V)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RV)
  let P' := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (ProEt.topology V)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj SV)
  let Q := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj RU)
  let Q' := SheafOfModules.toSheaf.{u + 1}
    ((sheafCompose (ProEt.topology U)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj SU)
  let a := proEtaleSheafAdjunction f AddCommGrpCat.{u + 1}
  have he : P.map
      ((proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm).hom.app N') =
      𝟙 _ := by
    ext W n
    exact (Classical.choose_spec
      (proEtaleRingRestrictionDirectImage_existsUnique
        f RV SV RU SU aV aU cR cS comm)).1 _ W n
  have htP := congrArg P.map hk
  simp only [P.map_comp, he] at htP
  erw [Category.comp_id] at htP
  have htP' : P.map g ≫ (proEtaleSheafDirectImage f AddCommGrpCat.{u + 1}).map
      (Q.map k) = P'.map h := by
    ext W n
    exact ConcreteCategory.congr_hom (congrArg (fun z ↦ z.hom.app W) htP) n
  have : IsIso (Q.map k) := isoOfAdjunct a (X := P'.obj M) (Y := Q.obj N) (Z := Q'.obj N')
    (P.map g) (P'.map h) (Q.map k) hg hh htP'
  exact isIso_of_reflects_iso k Q

attribute [local irreducible] proEtaleRingRestrictionPullbackApp
  proEtaleRingModulePullback proEtaleRingModuleAdjunction

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- The specified mate is natural and invertible.
Source: Stacks, Modules on Sites, lemma-adjoint-push-pull-modules
(blueprint: lem-weil-pbc-ring-sheaf-change-adjunction).
Proof: unit and counit naturality and naturality of the sectionwise identity give
naturality. Under the tensor-unit normalized adjunctions this mate is identity on
underlying inverse-image abelian sheaves. Its two scalar actions are equal because
`cS.inv aU = inverseImage(aV) cR.inv`, the coefficient-square equation. Hence it is
an isomorphism. No flatness of the coefficient-change maps is used. -/
theorem proEtaleRingRestrictionPullbackApp_properties :
    (∀ (M N : proEtaleRingModules V SV) (h : M ⟶ N),
      (proEtaleRingModulePullback f RV RU cR).map
          ((proEtaleRingRestrictScalars aV).map h) ≫
        proEtaleRingRestrictionPullbackApp f RV SV RU SU aV aU cR cS comm N =
      proEtaleRingRestrictionPullbackApp f RV SV RU SU aV aU cR cS comm M ≫
        (proEtaleRingRestrictScalars aU).map
          ((proEtaleRingModulePullback f SV SU cS).map h)) ∧
    ∀ M : proEtaleRingModules V SV,
      IsIso (proEtaleRingRestrictionPullbackApp f RV SV RU SU aV aU cR cS comm M) := by
  let adjS := proEtaleRingModuleAdjunction f SV SU cS
  let adjR := proEtaleRingModuleAdjunction f RV RU cR
  let d := proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm
  let s := (mateEquiv adjS adjR).symm (TwoSquare.mk _ _ _ _ d.hom)
  have hs (M : proEtaleRingModules V SV) :
      s.app M = proEtaleRingRestrictionPullbackApp f RV SV RU SU aV aU cR cS comm M := by
    simp only [s, mateEquiv_symm_apply, TwoSquare.mk, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.comp_obj,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app,
      Category.id_comp]
    dsimp only [TwoSquare.natTrans, Functor.comp_map]
    simp only [CategoryTheory.Functor.map_id, Category.id_comp]
    unfold proEtaleRingRestrictionPullbackApp
    rfl
  refine ⟨?_, ?_⟩
  · intro M N h
    simpa only [Functor.comp_map, hs] using s.natTrans.naturality h
  · intro M
    have happ : proEtaleRingRestrictionPullbackApp f RV SV RU SU aV aU cR cS comm M =
        (adjR.homEquiv _ _).symm
          ((proEtaleRingRestrictScalars aV).map (adjS.unit.app M) ≫
            d.hom.app ((proEtaleRingModulePullback f SV SU cS).obj M)) := by
      simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
      unfold proEtaleRingRestrictionPullbackApp
      rfl
    have ht := (adjR.homEquiv _ _).apply_symm_apply
      ((proEtaleRingRestrictScalars aV).map (adjS.unit.app M) ≫
        d.hom.app ((proEtaleRingModulePullback f SV SU cS).obj M))
    rw [← happ, Adjunction.homEquiv_unit] at ht
    exact ringModuleMap_isIso f RV SV RU SU aV aU cR cS comm M
      ((proEtaleRingModulePullback f RV RU cR).obj ((proEtaleRingRestrictScalars aV).obj M))
      ((proEtaleRingModulePullback f SV SU cS).obj M)
      (adjR.unit.app ((proEtaleRingRestrictScalars aV).obj M)) (adjS.unit.app M)
      (proEtaleRingRestrictionPullbackApp f RV SV RU SU aV aU cR cS comm M)
      (ringUnitComparison f RV RU cR adjR ((proEtaleRingRestrictScalars aV).obj M))
      (ringUnitComparison f SV SU cS adjS M) ht

/-- The canonical ordinary inverse-image comparison, with its direction reversed.
Source: Stacks, lemma-adjoint-push-pull-modules
(blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
noncomputable def proEtaleRingRestrictionPullbackInv :
    proEtaleRingRestrictScalars aV ⋙ proEtaleRingModulePullback f RV RU cR ⟶
      proEtaleRingModulePullback f SV SU cS ⋙ proEtaleRingRestrictScalars aU where
  app := proEtaleRingRestrictionPullbackApp f RV SV RU SU aV aU cR cS comm
  naturality := (proEtaleRingRestrictionPullbackApp_properties
    f RV SV RU SU aV aU cR cS comm).1

/-- The ordinary comparison is invertible. Source: Stacks, Modules on Sites
(blueprint: lem-weil-pbc-ring-sheaf-change-adjunction).
Proof: each component is invertible by the identity-on-inverse-image calculation
in proEtaleRingRestrictionPullbackApp_properties; naturality gives the inverse. -/
theorem proEtaleRingRestrictionPullbackInv_isIso :
    IsIso (proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm) := by
  have (M : proEtaleRingModules V SV) :
      IsIso ((proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm).app M) :=
    (proEtaleRingRestrictionPullbackApp_properties f RV SV RU SU aV aU cR cS comm).2 M
  exact NatIso.isIso_of_isIso_app _

attribute [local instance] proEtaleRingRestrictionPullbackInv_isIso

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restrictionPullback_mate :
    (mateEquiv (proEtaleRingModuleAdjunction f SV SU cS)
      (proEtaleRingModuleAdjunction f RV RU cR)
      (TwoSquare.mk _ _ _ _
        (proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm))).natTrans =
      (proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm).hom := by
  change (mateEquiv (proEtaleRingModuleAdjunction f SV SU cS)
    (proEtaleRingModuleAdjunction f RV RU cR))
      (TwoSquare.mk _ _ _ _
        (proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm)) =
      TwoSquare.mk _ _ _ _
        (proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm).hom
  rw [← Equiv.eq_symm_apply]
  apply TwoSquare.ext
  intro M
  simp only [mateEquiv_symm_apply, proEtaleRingRestrictionPullbackInv,
    proEtaleRingRestrictionPullbackApp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.leftUnitor_inv_app, Functor.rightUnitor_hom_app, Functor.comp_map,
    Category.id_comp]
  simp only [TwoSquare.mk, CategoryTheory.Functor.map_id]
  dsimp only [TwoSquare.natTrans, Functor.comp_obj]
  simp only [Category.id_comp]
  exact congrArg (fun h ↦ _ ≫ _ ≫ h) (Category.comp_id _).symm

/-- The termwise descended identified-coefficient inverse-image comparison `b`.
Source: Stacks, Tag 0D6D (blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
noncomputable def proEtaleRingRestrictionDerivedPullback :
    proEtaleRingDerivedPullback f SV SU cS ⋙ (proEtaleRingRestrictScalars aU).mapDerivedCategory ≅
      (proEtaleRingRestrictScalars aV).mapDerivedCategory ⋙
        proEtaleRingDerivedPullback f RV RU cR :=
  (Functor.mapDerivedCategoryCompIso (proEtaleRingModulePullback f SV SU cS)
    (proEtaleRingRestrictScalars aU)).symm ≪≫
    Functor.mapDerivedCategoryNatIso
      (asIso (proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm)).symm ≪≫
    Functor.mapDerivedCategoryCompIso (proEtaleRingRestrictScalars aV)
      (proEtaleRingModulePullback f RV RU cR)

/-- The right-derived unit on complexes, including the canonical quotient identifications.
Source: Stacks, Tag 07A5 (blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
noncomputable def proEtaleRingDirectImageDerivedUnit
    (K : CochainComplex (proEtaleRingModules U RU) ℤ) :
    DerivedCategory.Q.obj
        (((proEtaleRingModuleDirectImage f RV RU cR).mapHomologicalComplex (.up ℤ)).obj K) ⟶
      (proEtaleRingDerivedDirectImage f RV RU cR).obj (DerivedCategory.Q.obj K) :=
  (DerivedCategory.quotientCompQhIso _).inv.app _ ≫
    (proEtaleRingModuleDirectImage f RV RU cR).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj K) ≫
    (proEtaleRingDerivedDirectImage f RV RU cR).map
      ((DerivedCategory.quotientCompQhIso _).hom.app K)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The direct-image comparison is the unique comparison compatible with the derived
units and the identity-on-sections underived comparison.
Source: Stacks, Tag 0D6E (blueprint: lem-weil-pbc-ring-sheaf-change-adjunction).
Proof: regard both sides as the derived direct image of the same composite ringed-topos
morphism. The exact vertical direct images are termwise restriction. The composition
comparison supplies an invertible map compatible with the derived units. On a K-injective
complex I over SU and a K-injective resolution j of its RU-restriction, that map is
represented by directImage(j), which is a quasi-isomorphism by the composition theorem.
This does not assume that restriction preserves K-injectivity. The unit normalization
uniquely determines the comparison on K-injectives and hence everywhere by localization. -/
theorem proEtaleRingRestrictionDerivedDirectImage_existsUnique :
    ∃! d : proEtaleRingDerivedDirectImage f SV SU cS ⋙
        (proEtaleRingRestrictScalars aV).mapDerivedCategory ≅
      (proEtaleRingRestrictScalars aU).mapDerivedCategory ⋙
        proEtaleRingDerivedDirectImage f RV RU cR,
      ∀ K : CochainComplex (proEtaleRingModules U SU) ℤ,
        (proEtaleRingRestrictScalars aV).mapDerivedCategory.map
            (proEtaleRingDirectImageDerivedUnit f SV SU cS K) ≫
          d.hom.app (DerivedCategory.Q.obj K) ≫
          (proEtaleRingDerivedDirectImage f RV RU cR).map
            ((proEtaleRingRestrictScalars aU).mapDerivedCategoryFactors.hom.app K) =
        (proEtaleRingRestrictScalars aV).mapDerivedCategoryFactors.hom.app
            (((proEtaleRingModuleDirectImage f SV SU cS).mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map
            ((NatIso.mapHomologicalComplex
              (proEtaleRingRestrictionDirectImage f RV SV RU SU aV aU cR cS comm)
                (.up ℤ)).hom.app K) ≫
          proEtaleRingDirectImageDerivedUnit f RV RU cR
            (((proEtaleRingRestrictScalars aU).mapHomologicalComplex (.up ℤ)).obj K) := by
  sorry

/-- The canonical derived direct-image comparison `d`, determined by its unit normalization.
Source: Stacks, Tag 0D6E (blueprint: lem-weil-pbc-ring-sheaf-change-adjunction). -/
noncomputable def proEtaleRingRestrictionDerivedDirectImage :
    proEtaleRingDerivedDirectImage f SV SU cS ⋙
        (proEtaleRingRestrictScalars aV).mapDerivedCategory ≅
      (proEtaleRingRestrictScalars aU).mapDerivedCategory ⋙
        proEtaleRingDerivedDirectImage f RV RU cR :=
  Classical.choose
    (proEtaleRingRestrictionDerivedDirectImage_existsUnique f RV SV RU SU aV aU cR cS comm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option linter.style.haveILetI false in
/-- Exact restriction reflects derived isomorphisms, and the canonical coefficient
comparisons intertwine the canonical derived adjunctions.
Source: Stacks, Tags 05RT, 0D6D, 0D6E and 07A6
(blueprint: lem-weil-pbc-ring-sheaf-change-adjunction).
Proof: (1) restriction leaves underlying abelian kernels and sheafified cokernels
unchanged, so is exact and conservative. It commutes with cohomology; the unbounded
cohomology criterion therefore implies conservativity after localization.
(2) the inverse-image comparison is identity on the inverse-image abelian sheaf, with
the two scalar actions identified by the coefficient square. Descend it termwise.
(3) the two ringed-topos composites have identical structural maps; exact vertical
restriction identifies their derived direct images with termwise restriction.
(4) the derived direct-image composition theorem gives d, represented on K-injective
I and a K-injective resolution j of its restriction by directImage(j).
(5) represent t by a chain map into I. Its transpose is the ordinary module transpose
followed by the derived unit. After restriction and passage to j its transpose is
directImage(j) composed with that restricted transpose, by naturality of the ordinary
adjunction. The canonical pre-derived adjunction fraction formula then identifies this
with both sides of the displayed equation. Homotopies and canonical resolution
identifications make the equality valid for every derived M, N and t. -/
theorem proEtaleRingSheafChangeAdjunction :
    (proEtaleRingRestrictScalars aU).mapDerivedCategory.ReflectsIsomorphisms ∧
    (proEtaleRingRestrictScalars aV).mapDerivedCategory.ReflectsIsomorphisms ∧
    ∀ (M : DerivedCategory (proEtaleRingModules V SV))
      (N : DerivedCategory (proEtaleRingModules U SU))
      (t : (proEtaleRingDerivedPullback f SV SU cS).obj M ⟶ N),
      (proEtaleRingDerivedAdjunction f RV RU cR).homEquiv _ _
          ((proEtaleRingRestrictionDerivedPullback
              f RV SV RU SU aV aU cR cS comm).inv.app M ≫
            (proEtaleRingRestrictScalars aU).mapDerivedCategory.map t) =
        (proEtaleRingRestrictScalars aV).mapDerivedCategory.map
            ((proEtaleRingDerivedAdjunction f SV SU cS).homEquiv M N t) ≫
          (proEtaleRingRestrictionDerivedDirectImage
            f RV SV RU SU aV aU cR cS comm).hom.app N := by
  letI hU := (proEtaleRingRestrictScalars_properties aU).2.2
  letI hV := (proEtaleRingRestrictScalars_properties aV).2.2
  have hDerivedU :
      (proEtaleRingRestrictScalars aU).mapDerivedCategory.ReflectsIsomorphisms := by
    refine ⟨fun g _ ↦ ?_⟩
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso ((proEtaleRingRestrictScalars aU).map
        ((DerivedCategory.homologyFunctor _ n).map g)) :=
      (NatIso.isIso_map_iff
        ((proEtaleRingRestrictScalars aU).mapDerivedCategoryHomologyFunctorIso n) g).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ (proEtaleRingRestrictScalars aU)
  have hDerivedV :
      (proEtaleRingRestrictScalars aV).mapDerivedCategory.ReflectsIsomorphisms := by
    refine ⟨fun g _ ↦ ?_⟩
    rw [DerivedCategory.isIso_iff]
    intro n
    have : IsIso ((proEtaleRingRestrictScalars aV).map
        ((DerivedCategory.homologyFunctor _ n).map g)) :=
      (NatIso.isIso_map_iff
        ((proEtaleRingRestrictScalars aV).mapDerivedCategoryHomologyFunctorIso n) g).2
        (by rw [Functor.comp_map]; infer_instance)
    exact isIso_of_reflects_iso _ (proEtaleRingRestrictScalars aV)
  refine ⟨hDerivedU, hDerivedV, ?_⟩
  let e := asIso (proEtaleRingRestrictionPullbackInv f RV SV RU SU aV aU cR cS comm)
  let b := (Functor.mapDerivedCategoryCompIso (proEtaleRingRestrictScalars aV)
    (proEtaleRingModulePullback f RV RU cR)).symm ≪≫
      Functor.mapDerivedCategoryNatIso e ≪≫
      Functor.mapDerivedCategoryCompIso (proEtaleRingModulePullback f SV SU cS)
        (proEtaleRingRestrictScalars aU)
  let m := mateEquiv (proEtaleRingDerivedAdjunction f SV SU cS)
    (proEtaleRingDerivedAdjunction f RV RU cR) (TwoSquare.mk _ _ _ _ b.hom)
  have hd : (proEtaleRingRestrictionDerivedDirectImage
      f RV SV RU SU aV aU cR cS comm).hom = m.natTrans := by
    apply derived_comp_ext (proEtaleRingModuleDirectImage f SV SU cS)
      (proEtaleRingRestrictScalars aV)
      ((proEtaleRingRestrictScalars aU).mapDerivedCategory ⋙
        proEtaleRingDerivedDirectImage f RV RU cR)
    intro K
    apply (cancel_mono ((proEtaleRingDerivedDirectImage f RV RU cR).map
      ((proEtaleRingRestrictScalars aU).mapDerivedCategoryFactors.hom.app K))).mp
    have hn := (Classical.choose_spec
      (proEtaleRingRestrictionDerivedDirectImage_existsUnique
        f RV SV RU SU aV aU cR cS comm)).1 K
    have hm := derived_mate_factors (proEtaleRingModuleAdjunction f SV SU cS)
      (proEtaleRingModuleAdjunction f RV RU cR) e K
    dsimp only [e, asIso_hom] at hm
    rw [restrictionPullback_mate f RV SV RU SU aV aU cR cS comm] at hm
    simpa only [proEtaleRingDirectImageDerivedUnit, chainDerivedUnit,
      proEtaleRingRestrictionDerivedDirectImage, proEtaleRingDerivedAdjunction,
      m, b, e, Category.assoc] using hn.trans hm.symm
  intro M N t
  have hb : (proEtaleRingRestrictionDerivedPullback
      f RV SV RU SU aV aU cR cS comm).inv = b.hom := by
    dsimp [proEtaleRingRestrictionDerivedPullback, b]
    rw [Category.assoc]
    rfl
  rw [hb, hd]
  exact mate_adjunct (proEtaleRingDerivedAdjunction f SV SU cS)
    (proEtaleRingDerivedAdjunction f RV RU cR) (TwoSquare.mk _ _ _ _ b.hom) M N t

end AlgebraicGeometry.Scheme
