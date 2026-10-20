/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NA
-/
module

public import Sheaf.AlgebraicGeometry.ChosenCartesianSquare
public import Sheaf.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusAdjunction
import WeilConjectures.CategoryTheory.RightDerivedBaseChangeZeroUnit
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Unbounded exchange agrees with bounded exchange and with degree-zero exchange

Source: blueprint, sec-smooth-purity, sk-prop-sf-kunneth-ordinary,
node lem-kun-unbounded-exchange-agrees; Stacks Project, Tags 07A7 and 05TD(3)
(blueprint: lem-kun-unbounded-exchange-agrees).

The endpoint isomorphisms below are composites of the fixed exact-functor cohomology
comparison, the single-object right-derived comparison, and the degree-zero comparison.
The last two are induced by augmentations into nonnegative injective resolutions.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor



private lemma homology_plus_map
    {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]
    {K L : DerivedCategory.Plus C} (q : K ⟶ L) :
    (DerivedCategory.Plus.homologyFunctor C 0).map q =
      (DerivedCategory.homologyFunctor C 0).map (DerivedCategory.Plus.ι.map q) := rfl

private lemma map_conjugation
    {C D : Type*} [Category* C] [Category* D] (H : C ⥤ D)
    {P U Q V : C} (c : P ≅ U) (d : Q ≅ V) (x : U ⟶ V) (y : P ⟶ Q)
    (h : x = c.inv ≫ y ≫ d.hom) :
    H.map x = (H.mapIso c).inv ≫ H.map y ≫ (H.mapIso d).hom := by
  rw [h, H.map_comp, H.map_comp]
  rfl

private lemma normalize_exchange
    {C : Type*} [Category* C] {P U Q V S T : C}
    (c : P ≅ U) (d : Q ≅ V) (s : U ≅ S) (t : V ≅ T)
    (x : U ⟶ V) (y : P ⟶ Q) (e : S ⟶ T) (p : P ⟶ S) (q : Q ⟶ T)
    (hx : x = c.inv ≫ y ≫ d.hom) (hs : c.hom ≫ s.hom = p)
    (ht : d.hom ≫ t.hom = q) (hy : y ≫ q = p ≫ e) :
    x ≫ t.hom = s.hom ≫ e := by
  apply (cancel_epi c.hom).1
  rw [hx]
  simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [Category.assoc, ht, hy, ← hs, Category.assoc]

private lemma inclusion_exact_map
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    {K L : DerivedCategory.Plus C} (q : K ⟶ L) :
    DerivedCategory.Plus.ι.map (G.mapDerivedCategoryPlus.map q) =
      G.mapDerivedCategory.map (DerivedCategory.Plus.ι.map q) := rfl

private lemma mate_app
    {C₁ C₂ C₃ C₄ : Type*} [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
    {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
    {G : C₂ ⥤ C₄} {G' : C₁ ⥤ C₃}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (θ : G ⋙ L' ⟶ L ⋙ G') (K : C₁) :
    (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ θ)).natTrans.app K =
      adj'.unit.app (G.obj (R.obj K)) ≫ R'.map (θ.app (R.obj K)) ≫
        R'.map (G'.map (adj.counit.app K)) := by
  simp [mateEquiv_apply]

section

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives D]
  [Abelian.HasKInjectiveResolutions D]
  {L : C ⥤ D} {R : D ⥤ C} [L.Additive] [R.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]

private lemma plus_comparison_unit (F : D ⥤ C) [F.Additive]
    (K : HomotopyCategory.Plus D) :
    DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K) ≫
        F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj K) =
      F.rightDerivedFunctorUnit.app K.obj := by
  simpa only [Functor.comp_obj, ObjectProperty.ι_obj,
    Functor.rightDerivedFunctorPlusCompatibility,
    Functor.rightDerivedUnique, Functor.rightDerivedNatIso_hom,
    Functor.rightDerivedFunctorPlusιUnit, Functor.ιRightDerivedFunctorUnit,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.id_app,
    Iso.refl_hom, Category.id_comp] using
    (Functor.rightDerivedNatTrans_app
      (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
      (DerivedCategory.Plus.ι ⋙ F.rightDerivedFunctor)
      F.rightDerivedFunctorPlusιUnit F.ιRightDerivedFunctorUnit
      (HomotopyCategory.Plus.quasiIso D) (𝟙 _) K)

private lemma derived_unit_comparison (adj : L ⊣ R)
    (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map (adj.derivedPlus.unit.app K) ≫
      R.rightDerivedFunctorPlusCompatibility.hom.app (L.mapDerivedCategoryPlus.obj K) =
    adj.mapDerivedCategoryRightDerivedAdjunction.unit.app K.obj := by
  let η : DerivedCategory.Plus.ι ⟶
      L.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι ⋙ R.rightDerivedFunctor :=
    Functor.whiskerRight adj.derivedPlus.unit DerivedCategory.Plus.ι ≫
      Functor.whiskerLeft L.mapDerivedCategoryPlus R.rightDerivedFunctorPlusCompatibility.hom
  let ε : DerivedCategory.Plus.ι ⟶
      L.mapDerivedCategoryPlus ⋙ DerivedCategory.Plus.ι ⋙ R.rightDerivedFunctor :=
    Functor.whiskerLeft DerivedCategory.Plus.ι
      adj.mapDerivedCategoryRightDerivedAdjunction.unit
  have he : η = ε := by
    apply Localization.natTrans_ext DerivedCategory.Plus.Qh
      (HomotopyCategory.Plus.quasiIso C)
    intro N
    dsimp only [η, ε, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatTrans.comp_app]
    apply (cancel_mono (R.rightDerivedFunctor.map
      (L.mapDerivedCategoryFactorsh.hom.app N.obj))).1
    have hn := R.rightDerivedFunctorPlusCompatibility.hom.naturality
      (L.mapDerivedCategoryPlusFactorsh.hom.app N)
    dsimp only [Functor.comp_map] at hn
    have hf : L.mapDerivedCategoryFactorsh.hom.app N.obj =
        DerivedCategory.Plus.ι.map (L.mapDerivedCategoryPlusFactorsh.hom.app N) :=
      (L.ι_map_mapDerivedCategoryPlusFactorsh_hom_app N).symm
    erw [hf]
    erw [Category.assoc, ← hn, ← Functor.map_comp_assoc,
      adj.derivedPlus_unit_app_fac, Functor.map_comp, Category.assoc, plus_comparison_unit]
    have h := (adj.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso C (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
      R.rightDerivedFunctorUnit N.obj
    change adj.mapDerivedCategoryRightDerivedAdjunction.unit.app _ ≫ _ = _ at h
    erw [← hf, h]
    change DerivedCategory.Qh.map ((HomotopyCategory.Plus.ι C).map
      (adj.mapHomotopyCategoryPlus.unit.app N)) ≫ _ = _
    rw [Adjunction.ι_map_mapHomotopyCategoryPlus_unit_app]
    rfl
  exact NatTrans.congr_app he K

private lemma derived_counit_comparison (adj : L ⊣ R)
    (K : DerivedCategory.Plus D) :
    L.mapDerivedCategory.map (R.rightDerivedFunctorPlusCompatibility.hom.app K) ≫
      adj.mapDerivedCategoryRightDerivedAdjunction.counit.app K.obj =
    DerivedCategory.Plus.ι.map (adj.derivedPlus.counit.app K) := by
  apply (adj.mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  have hn := adj.mapDerivedCategoryRightDerivedAdjunction.unit.naturality
    (R.rightDerivedFunctorPlusCompatibility.hom.app K)
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  simp only [Functor.map_comp, ← Category.assoc, Functor.comp_obj, ObjectProperty.ι_obj]
  erw [← hn, Category.assoc,
    adj.mapDerivedCategoryRightDerivedAdjunction.right_triangle_components K.obj,
    Category.comp_id]
  erw [← derived_unit_comparison adj (R.rightDerivedFunctorPlus.obj K)]
  have hc := R.rightDerivedFunctorPlusCompatibility.hom.naturality
    (adj.derivedPlus.counit.app K)
  dsimp only [Functor.comp_map] at hc
  erw [Category.assoc, ← hc, ← Functor.map_comp_assoc]
  simp only [Adjunction.right_triangle_components]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

end

private theorem square_fac
    {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B] [HasDerivedCategory C]
    [HasDerivedCategory D]
    (G : A ⥤ C) (L : A ⥤ B) (L' : C ⥤ D) (H : B ⥤ D)
    [G.Additive] [L.Additive] [L'.Additive] [H.Additive]
    [Limits.PreservesFiniteLimits G] [Limits.PreservesFiniteColimits G]
    [Limits.PreservesFiniteLimits L] [Limits.PreservesFiniteColimits L]
    [Limits.PreservesFiniteLimits L'] [Limits.PreservesFiniteColimits L']
    [Limits.PreservesFiniteLimits H] [Limits.PreservesFiniteColimits H]
    (e : G ⋙ L' ≅ L ⋙ H) (K : HomotopyCategory.Plus A) :
    ((Functor.mapDerivedCategoryPlusCompIso G L').symm ≪≫
      Functor.mapDerivedCategoryPlusNatIso e ≪≫
      Functor.mapDerivedCategoryPlusCompIso L H).hom.app (DerivedCategory.Plus.Qh.obj K) ≫
        H.mapDerivedCategoryPlus.map (L.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        H.mapDerivedCategoryPlusFactorsh.hom.app (L.mapHomotopyCategoryPlus.obj K) =
      L'.mapDerivedCategoryPlus.map (G.mapDerivedCategoryPlusFactorsh.hom.app K) ≫
        L'.mapDerivedCategoryPlusFactorsh.hom.app (G.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map ((NatTrans.mapHomotopyCategoryPlus e.hom).app K) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  rw [Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh,
    Functor.mapDerivedCategoryPlusNatIso_hom_app_factorsh]
  rw [← Functor.mapDerivedCategoryPlusCompIso_hom_app_factorsh G L' K]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]

private lemma plus_homology_inv
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (G : C ⥤ D) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (K : DerivedCategory.Plus C) :
    (G.mapDerivedCategoryPlusHomologyFunctorIso 0).inv.app K =
      (G.mapDerivedCategoryHomologyFunctorIso 0).inv.app K.obj := by
  simp only [Functor.comp_obj, Functor.mapDerivedCategoryPlusHomologyFunctorIso,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_symm, Iso.trans_inv,
    Functor.isoWhiskerRight_inv, Iso.refl_inv, Functor.whiskerRight_id', Category.comp_id,
    Iso.symm_inv, Functor.isoWhiskerLeft_inv, Category.assoc, NatTrans.comp_app,
    ObjectProperty.ι_obj, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp]
  erw [Category.id_comp]

section

variable {B B' C C' : Type*} [Category* B] [Category* B'] [Category* C] [Category* C']
  [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
  [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C] [HasDerivedCategory C']
  [EnoughInjectives B] [EnoughInjectives B']
  {G : B ⥤ C} {G' : B' ⥤ C'} {β : B ⥤ B'} {γ : C ⥤ C'}
  [G.Additive] [G'.Additive] [β.Additive] [γ.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteLimits G']
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]

private theorem plus_basechange_zero (e : G ⋙ γ ⟶ β ⋙ G') (F : B) :
    (DerivedCategory.Plus.homologyFunctor C' 0).map
        ((Functor.rightDerivedFunctorPlusBaseChange e).app
          ((DerivedCategory.Plus.singleFunctor B 0).obj F)) ≫
      (DerivedCategory.Plus.homologyFunctor C' 0).map
        (G'.rightDerivedFunctorPlus.map
          ((β.mapDerivedCategoryPlusSingleFunctor 0).hom.app F)) ≫
      (G'.homologyRightDerivedFunctorPlusObjSingleFunctorIso (β.obj F) 0).hom ≫
      G'.rightDerivedZeroIsoSelf.hom.app (β.obj F) =
    (γ.mapDerivedCategoryPlusHomologyFunctorIso 0).inv.app
        (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj F)) ≫
      γ.map ((G.homologyRightDerivedFunctorPlusObjSingleFunctorIso F 0).hom ≫
        G.rightDerivedZeroIsoSelf.hom.app F) ≫ e.app F := by
  have h := Functor.rightDerivedBaseChange_zero_unit e F
  rw [Functor.rightDerivedBaseChange_app] at h
  dsimp only [Functor.singleFunctorCompRightDerivedFunctorPlusCompHomologyFunctorIso,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app] at h
  have h' := congrArg (fun a ↦ a ≫ G'.rightDerivedZeroIsoSelf.hom.app (β.obj F)) h
  simp only [Category.assoc, Functor.rightDerivedZeroIsoSelf_inv_hom_id_app] at h'
  erw [Category.comp_id] at h'
  apply (cancel_epi ((γ.mapDerivedCategoryPlusHomologyFunctorIso 0).hom.app
    (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj F)))).1
  apply (cancel_epi (γ.map
    ((G.homologyRightDerivedFunctorPlusObjSingleFunctorIso F 0).inv))).1
  apply (cancel_epi (γ.map (G.toRightDerivedZero.app F))).1
  simp only [Iso.hom_inv_id_app_assoc, ← γ.map_comp_assoc,
    Iso.inv_hom_id_assoc, Functor.rightDerivedZeroIsoSelf_inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [← γ.map_comp_assoc] at h'
  convert h' using 1
  rfl

omit [EnoughInjectives B] in
private lemma target_zero_comparison_aux [Abelian.HasKInjectiveResolutions B']
    (F : B) :
    (DerivedCategory.homologyFunctor C' 0).map
        (G'.rightDerivedFunctorPlusCompatibility.hom.app
          (β.mapDerivedCategoryPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj F))) ≫
      (DerivedCategory.homologyFunctor C' 0).map
        (G'.rightDerivedFunctor.map ((β.mapDerivedCategorySingleFunctor 0).hom.app F)) ≫
      (G'.homologyRightDerivedFunctorObjSingleFunctorIso (β.obj F) 0).hom ≫
      G'.rightDerivedZeroIsoSelf.hom.app (β.obj F) =
    (DerivedCategory.Plus.homologyFunctor C' 0).map
        (G'.rightDerivedFunctorPlus.map
          ((β.mapDerivedCategoryPlusSingleFunctor 0).hom.app F)) ≫
      (G'.homologyRightDerivedFunctorPlusObjSingleFunctorIso (β.obj F) 0).hom ≫
      G'.rightDerivedZeroIsoSelf.hom.app (β.obj F) := by
  have hn := G'.rightDerivedFunctorPlusCompatibility.hom.naturality
    ((β.mapDerivedCategoryPlusSingleFunctor 0).hom.app F)
  dsimp only [Functor.comp_map] at hn
  erw [Functor.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app] at hn
  simp only [Functor.homologyRightDerivedFunctorObjSingleFunctorIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  erw [← Functor.map_comp_assoc, ← hn, Functor.map_comp, Category.assoc]
  simp only [Iso.app_inv, Functor.comp_obj, ObjectProperty.ι_obj,
    ← Functor.map_comp_assoc]
  erw [← (DerivedCategory.homologyFunctor C' 0).map_comp_assoc,
    Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rfl

private lemma source_zero_comparison_aux [Abelian.HasKInjectiveResolutions B]
    (F : B) :
    (DerivedCategory.homologyFunctor C' 0).map
        (γ.mapDerivedCategory.map (G.rightDerivedFunctorPlusCompatibility.hom.app
          ((DerivedCategory.Plus.singleFunctor B 0).obj F))) ≫
      (γ.mapDerivedCategoryHomologyFunctorIso 0).inv.app
        (G.rightDerivedFunctor.obj ((DerivedCategory.singleFunctor B 0).obj F)) ≫
      γ.map ((G.homologyRightDerivedFunctorObjSingleFunctorIso F 0).hom ≫
        G.rightDerivedZeroIsoSelf.hom.app F) =
    (γ.mapDerivedCategoryPlusHomologyFunctorIso 0).inv.app
        (G.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj F)) ≫
      γ.map ((G.homologyRightDerivedFunctorPlusObjSingleFunctorIso F 0).hom ≫
        G.rightDerivedZeroIsoSelf.hom.app F) := by
  have hn := (γ.mapDerivedCategoryHomologyFunctorIso 0).inv.naturality
    (G.rightDerivedFunctorPlusCompatibility.hom.app
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F))
  dsimp only [Functor.comp_map] at hn
  simp only [Functor.homologyRightDerivedFunctorObjSingleFunctorIso,
    Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  erw [reassoc_of% hn]
  simp only [Functor.map_comp, Iso.app_inv]
  erw [← Functor.map_comp_assoc,
    ← (DerivedCategory.homologyFunctor _ 0).map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.id_comp, plus_homology_inv]
  rfl

end

private theorem derived_mate_plus_comparison
    {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory C'] [HasDerivedCategory D']
    [EnoughInjectives D] [EnoughInjectives D']
    [Abelian.HasKInjectiveResolutions D] [Abelian.HasKInjectiveResolutions D']
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    {G : C ⥤ C'} {G' : D ⥤ D'}
    [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [G'.Additive]
    [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (adj : L ⊣ R) (adj' : L' ⊣ R')
    (θ : G.mapDerivedCategoryPlus ⋙ L'.mapDerivedCategoryPlus ⟶
      L.mapDerivedCategoryPlus ⋙ G'.mapDerivedCategoryPlus)
    (Θ : G.mapDerivedCategory ⋙ L'.mapDerivedCategory ⟶
      L.mapDerivedCategory ⋙ G'.mapDerivedCategory)
    (hθ : ∀ M, DerivedCategory.Plus.ι.map (θ.app M) = Θ.app M.obj)
    (K : DerivedCategory.Plus D) :
    (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
      adj'.mapDerivedCategoryRightDerivedAdjunction (TwoSquare.mk _ _ _ _ Θ)).natTrans.app
        K.obj =
    G.mapDerivedCategory.map (R.rightDerivedFunctorPlusCompatibility.inv.app K) ≫
      DerivedCategory.Plus.ι.map
        ((mateEquiv adj.derivedPlus adj'.derivedPlus
          (TwoSquare.mk _ _ _ _ θ)).natTrans.app K) ≫
      R'.rightDerivedFunctorPlusCompatibility.hom.app (G'.mapDerivedCategoryPlus.obj K) := by
  apply (cancel_epi (G.mapDerivedCategory.map
    (R.rightDerivedFunctorPlusCompatibility.hom.app K))).1
  simp only [← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hn := adj'.mapDerivedCategoryRightDerivedAdjunction.unit.naturality
    (G.mapDerivedCategory.map (R.rightDerivedFunctorPlusCompatibility.hom.app K))
  have ht := Θ.naturality (R.rightDerivedFunctorPlusCompatibility.hom.app K)
  have hc := derived_counit_comparison adj K
  have hu := derived_unit_comparison adj'
    (G.mapDerivedCategoryPlus.obj (R.rightDerivedFunctorPlus.obj K))
  simp only [Functor.id_map, Functor.comp_map] at hn ht
  simp only [mate_app, Functor.map_comp, Category.assoc]
  erw [reassoc_of% hn]
  simp only [← Functor.map_comp]
  erw [reassoc_of% ht, ← Functor.map_comp G'.mapDerivedCategory, hc]
  erw [← hθ, ← hu]
  have hb := R'.rightDerivedFunctorPlusCompatibility.hom.naturality
    (θ.app (R.rightDerivedFunctorPlus.obj K) ≫
      G'.mapDerivedCategoryPlus.map (adj.derivedPlus.counit.app K))
  dsimp only [Functor.comp_map] at hb
  simpa only [Functor.map_comp, Category.assoc, Functor.id_obj, Functor.comp_obj,
    ObjectProperty.ι_obj, inclusion_exact_map] using
    congrArg (fun a ↦ DerivedCategory.Plus.ι.map
      (adj'.derivedPlus.unit.app
        (G.mapDerivedCategoryPlus.obj (R.rightDerivedFunctorPlus.obj K))) ≫ a) hb.symm

namespace AlgebraicGeometry.Etale

private lemma bounded_basechange_eq
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g) :
    Functor.rightDerivedFunctorPlusBaseChange
      (G := (f)_*[A]) (G' := (f')_*[A]) (β := (g')^*[A]) (γ := (g)^*[A])
      (baseChangeMap A sq) =
      derivedBaseChangeMapPlus A sq := by
  apply derivedBaseChangeMapPlus_ext A sq
  intro N
  have h := NatTrans.congr_app
    (Functor.rightDerivedFunctorPlusBaseChange_fac
      (G := (f)_*[A]) (G' := (f')_*[A]) (β := (g')^*[A]) (γ := (g)^*[A])
      (baseChangeMap A sq)) N
  simpa only [Functor.rightDerivedFunctorPlusBaseChangeAux, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_obj,
    Functor.mapHomotopyCategoryPlusCompIso_refl_hom_app,
    Functor.mapHomotopyCategoryPlusCompIso_refl_inv_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
    Category.assoc] using h

private theorem exact_exchange_plus
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : CommSq g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology A)) :
    (exactDerivedBaseChangeMap A sq).app K.obj =
      (D((g)^*[A])).map (((f)_*[A]).rightDerivedFunctorPlusCompatibility.inv.app K) ≫
        DerivedCategory.Plus.ι.map ((derivedBaseChangeMapPlus A sq).app K) ≫
        ((f')_*[A]).rightDerivedFunctorPlusCompatibility.hom.app
          ((D+((g')^*[A])).obj K) := by
  let θ := (Functor.mapDerivedCategoryPlusCompIso (g)^*[A] (f')^*[A]).symm ≪≫
    Functor.mapDerivedCategoryPlusNatIso (squareUpperStarIso A sq) ≪≫
    Functor.mapDerivedCategoryPlusCompIso (f)^*[A] (g')^*[A]
  have hm : (mateEquiv (upperStarLowerStarAdjunction A f).derivedPlus
      (upperStarLowerStarAdjunction A f').derivedPlus
      (TwoSquare.mk _ _ _ _ θ.hom)).natTrans = derivedBaseChangeMapPlus A sq := by
    apply derivedBaseChangeMapPlus_ext A sq
    intro N
    exact Adjunction.derivedPlus_mateEquiv_app_fac
      (upperStarLowerStarAdjunction A f) (upperStarLowerStarAdjunction A f')
      (TwoSquare.mk _ _ _ _ (squareUpperStarIso A sq).hom)
      (TwoSquare.mk _ _ _ _ θ.hom)
      (square_fac _ _ _ _ (squareUpperStarIso A sq)) N
  have hθ (M : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology A)) :
      DerivedCategory.Plus.ι.map (θ.hom.app M) =
        (exactDerivedSquareUpperStarIso A sq).hom.app M.obj := by
    have hi : DerivedCategory.Plus.ι.map
        ((Functor.mapDerivedCategoryPlusCompIso (g)^*[A] (f')^*[A]).inv.app M) =
        (Functor.mapDerivedCategoryCompIso (g)^*[A] (f')^*[A]).inv.app M.obj := by
      apply (cancel_mono
        ((Functor.mapDerivedCategoryCompIso (g)^*[A] (f')^*[A]).hom.app M.obj)).1
      erw [← Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app,
        ← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
        Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app, Iso.inv_hom_id_app]
      rfl
    simp only [θ, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp,
      Functor.ι_map_mapDerivedCategoryPlusCompIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app, hi]
    rfl
  -- Transport the mate using the fixed direct-image comparison.
  exact derived_mate_plus_comparison (upperStarLowerStarAdjunction A f)
    (upperStarLowerStarAdjunction A f') θ.hom
    (exactDerivedSquareUpperStarIso A sq).hom hθ K |>.trans (by rw [hm])

/-- The canonical source identification in degree zero, induced by the augmentation.
Source: Stacks Project, Tag 05TD(3), and exact inverse image, Tag 0735
(blueprint: lem-kun-unbounded-exchange-agrees). -/
noncomputable def exchangeSourceZeroIso
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (F : Sheaf X.smallEtaleTopology A) :
    (_root_.DerivedCategory.homologyFunctor _ 0).obj
        ((D((g)^*[A])).obj ((R((f)_*[A])).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ≅
      ((g)^*[A]).obj (((f)_*[A]).obj F) :=
  (((g)^*[A]).mapDerivedCategoryHomologyFunctorIso 0).symm.app _ ≪≫
    ((g)^*[A]).mapIso
      (((f)_*[A]).homologyRightDerivedFunctorObjSingleFunctorIso F 0 ≪≫
        ((f)_*[A]).rightDerivedZeroIsoSelf.app F)

/-- The canonical target identification in degree zero, induced by the augmentation.
Source: Stacks Project, Tag 05TD(3), and exact inverse image, Tag 0735
(blueprint: lem-kun-unbounded-exchange-agrees). -/
noncomputable def exchangeTargetZeroIso
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X X' Y' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (F : Sheaf X.smallEtaleTopology A) :
    (_root_.DerivedCategory.homologyFunctor _ 0).obj
        ((R((f')_*[A])).obj ((D((g')^*[A])).obj
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F))) ≅
      ((f')_*[A]).obj (((g')^*[A]).obj F) :=
  (_root_.DerivedCategory.homologyFunctor _ 0).mapIso
      ((R((f')_*[A])).mapIso ((((g')^*[A]).mapDerivedCategorySingleFunctor 0).app F)) ≪≫
    ((f')_*[A]).homologyRightDerivedFunctorObjSingleFunctorIso (((g')^*[A]).obj F) 0 ≪≫
    ((f')_*[A]).rightDerivedZeroIsoSelf.app (((g')^*[A]).obj F)

private lemma target_zero_comparison
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X X' Y' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (F : Sheaf X.smallEtaleTopology A) :
    (DerivedCategory.homologyFunctor _ 0).map
        (((f')_*[A]).rightDerivedFunctorPlusCompatibility.hom.app
          ((D+((g')^*[A])).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ≫
      (exchangeTargetZeroIso A g' f' F).hom =
    (DerivedCategory.Plus.homologyFunctor _ 0).map
        (((f')_*[A]).rightDerivedFunctorPlus.map
          ((((g')^*[A]).mapDerivedCategoryPlusSingleFunctor 0).hom.app F)) ≫
      (((f')_*[A]).homologyRightDerivedFunctorPlusObjSingleFunctorIso
        (((g')^*[A]).obj F) 0).hom ≫
      ((f')_*[A]).rightDerivedZeroIsoSelf.hom.app (((g')^*[A]).obj F)  := by
  simpa only [exchangeTargetZeroIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Category.assoc] using
    (target_zero_comparison_aux (G' := (f')_*[A]) (β := (g')^*[A]) F)

private lemma source_zero_comparison
    (A : Type v) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {X Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y)
    (F : Sheaf X.smallEtaleTopology A) :
    (DerivedCategory.homologyFunctor _ 0).map
        ((D((g)^*[A])).map (((f)_*[A]).rightDerivedFunctorPlusCompatibility.hom.app
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F))) ≫
      (exchangeSourceZeroIso A f g F).hom =
    (((g)^*[A]).mapDerivedCategoryPlusHomologyFunctorIso 0).inv.app
        (((f)_*[A]).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ≫
      ((g)^*[A]).map
        ((((f)_*[A]).homologyRightDerivedFunctorPlusObjSingleFunctorIso F 0).hom ≫
          ((f)_*[A]).rightDerivedZeroIsoSelf.hom.app F)  := by
  simpa only [exchangeSourceZeroIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_hom, Category.assoc] using
    (source_zero_comparison_aux (G := (f)_*[A]) (γ := (g)^*[A]) F)

/-- At integral (abelian) coefficients the unbounded exchange restricts to the bounded
below exchange, under the canonical direct-image and inverse-image comparisons.
Source: blueprint lem-kun-unbounded-exchange-agrees, first paragraph; Stacks, Tag 07A7
(blueprint: lem-kun-unbounded-exchange-agrees).

Proof: Choose a bounded below injective representative I of K. It is K-injective
(lem-weil-pbc-dplus-injective-representative), so both direct images are represented by
u_* I. Uniqueness of right derivation with its unit gives the fixed natural comparison
rightDerivedFunctorPlusCompatibility (lem-weil-pbc-kinjective-total-derived and
lem-weil-pbc-kinjective-hom-derived). Inverse image is the same exact termwise functor
(def-weil-pbc-derived-inverse-image). The termwise adjunction and the derived Hom
bijection into a K-injective identify both units and counits in the two models
(lem-weil-pbc-termwise-adjunction-homotopy, lem-pc-derived-adjoint-functors,
prop-weil-pbc-derived-inverse-image-adjunction). Both square maps are the localized
termwise squareUpperStarIso. Therefore their transposes are the same square map
followed by inverse image of the same counit. Injectivity of the adjunction bijection
(def-weil-pbc-adjunction-mate) identifies the exchanges. -/
theorem exactDerivedBaseChangeMap_agrees_plus
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})) :
    (exactDerivedBaseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app K.obj =
      (D((g)^*[AddCommGrpCat.{u + 1}])).map
        (((f)_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorPlusCompatibility.inv.app K) ≫
      _root_.DerivedCategory.Plus.ι.map
        ((derivedBaseChangeMapPlus AddCommGrpCat.{u + 1} sq.toCommSq).app K) ≫
      ((f')_*[AddCommGrpCat.{u + 1}]).rightDerivedFunctorPlusCompatibility.hom.app
        ((D+((g')^*[AddCommGrpCat.{u + 1}])).obj K) := by
  exact exact_exchange_plus _ sq.toCommSq K

/-- On a sheaf in degree zero, the zeroth cohomology of the unbounded module exchange
is the module mate; after the fixed coefficient comparisons its underlying abelian map
is the underived abelian exchange.
Source: blueprint lem-kun-unbounded-exchange-agrees, second paragraph; Stacks, Tags 07A7
and 05TD(3) (blueprint: lem-kun-unbounded-exchange-agrees).

Proof: Choose nonnegative injective resolutions s:F[0] → I and t:g'⁻¹F[0] → J
(lem-weil-pbc-module-sheaves-enough-injectives). Both are K-injective. Exactness of
inverse image makes g'⁻¹s a quasi-isomorphism. The K-injective Hom bijection gives a
chain map j:g'⁻¹I → J with j g'⁻¹s = t: a possible homotopy has its only component
in J⁻¹ = 0. Apply the module underived mate termwise and then f'_*j to obtain e.
Naturality of the counit and the defining mate identity show that Qe has the same
transpose as exactDerivedBaseChangeMap, hence represents it. Naturality of the module
mate gives e g⁻¹f_*s = f'_*t Ex⁰_F. Left exactness of f_* and f'_* identifies the
zeroth homology of their augmentations with their ordinary direct images
(lem-weil-pbc-left-exact-injective-resolution-degree-zero). Exact inverse image respects
this augmentation comparison (lem-weil-pbc-exact-functor-complex-cohomology). Taking
zeroth homology therefore gives the first equality with precisely the two displayed
canonical endpoint isomorphisms. Finally apply
lem-weil-pbc-module-abelian-underived-exchange to that module mate, inserting the fixed
inverse-image coefficient comparisons and direct-image evaluation identities. This gives
the second equality. This argument asserts no equality in higher degrees. -/
theorem exactDerivedBaseChangeMap_homology_zero
    (Λ : Type (u + 1)) [CommRing Λ]
    {X X' Y Y' : Scheme.{u}}
    {f : X ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X} {g : Y' ⟶ Y}
    (sq : ChosenCartesianSquare g' f' f g)
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (_root_.DerivedCategory.homologyFunctor _ 0).map
        ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ≫
        (exchangeTargetZeroIso (ModuleCat.{u + 1} Λ) g' f' F).hom =
      (exchangeSourceZeroIso (ModuleCat.{u + 1} Λ) f g F).hom ≫
        (baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F ∧
    (moduleAbelianForget Λ Y').map
        ((exchangeSourceZeroIso (ModuleCat.{u + 1} Λ) f g F).inv ≫
          (_root_.DerivedCategory.homologyFunctor _ 0).map
            ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
              ((_root_.DerivedCategory.singleFunctor _ 0).obj F)) ≫
          (exchangeTargetZeroIso (ModuleCat.{u + 1} Λ) g' f' F).hom) ≫
        (moduleAbelianLowerStarIso Λ f').hom.app (((g')^*[ModuleCat.{u + 1} Λ]).obj F) ≫
        ((f')_*[AddCommGrpCat.{u + 1}]).map ((moduleAbelianUpperStarIso Λ g').inv.app F) =
      (moduleAbelianUpperStarIso Λ g).inv.app (((f)_*[ModuleCat.{u + 1} Λ]).obj F) ≫
        ((g)^*[AddCommGrpCat.{u + 1}]).map ((moduleAbelianLowerStarIso Λ f).hom.app F) ≫
        (baseChangeMap AddCommGrpCat.{u + 1} sq.toCommSq).app
          ((moduleAbelianForget Λ X).obj F) := by
  have hz : (DerivedCategory.homologyFunctor _ 0).map
        ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app
          ((DerivedCategory.singleFunctor _ 0).obj F)) ≫
      (exchangeTargetZeroIso (ModuleCat.{u + 1} Λ) g' f' F).hom =
    (exchangeSourceZeroIso (ModuleCat.{u + 1} Λ) f g F).hom ≫
      (baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq).app F := by
    let K := (DerivedCategory.Plus.singleFunctor _ 0).obj F
    let H := DerivedCategory.homologyFunctor
      (Sheaf Y'.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0
    let c := (D((g)^*[ModuleCat.{u + 1} Λ])).mapIso
      (((f)_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app K)
    let d := ((f')_*[ModuleCat.{u + 1} Λ]).rightDerivedFunctorPlusCompatibility.app
      ((D+((g')^*[ModuleCat.{u + 1} Λ])).obj K)
    have hc := map_conjugation H c d _ _
      (exact_exchange_plus (ModuleCat.{u + 1} Λ) sq.toCommSq K)
    apply normalize_exchange (H.mapIso c) (H.mapIso d)
      (exchangeSourceZeroIso (ModuleCat.{u + 1} Λ) f g F)
      (exchangeTargetZeroIso (ModuleCat.{u + 1} Λ) g' f' F) _ _ _ _ _ hc
    · exact source_zero_comparison (ModuleCat.{u + 1} Λ) f g F
    · exact target_zero_comparison (ModuleCat.{u + 1} Λ) g' f' F
    · have hzero := plus_basechange_zero
        (G := (f)_*[ModuleCat.{u + 1} Λ]) (G' := (f')_*[ModuleCat.{u + 1} Λ])
        (β := (g')^*[ModuleCat.{u + 1} Λ]) (γ := (g)^*[ModuleCat.{u + 1} Λ])
        (baseChangeMap (ModuleCat.{u + 1} Λ) sq.toCommSq) F
      rw [bounded_basechange_eq (ModuleCat.{u + 1} Λ) sq.toCommSq] at hzero
      erw [homology_plus_map
        ((derivedBaseChangeMapPlus (ModuleCat.{u + 1} Λ) sq.toCommSq).app K)] at hzero
      exact hzero
  refine ⟨hz, ?_⟩
  rw [hz, Iso.inv_hom_id_assoc]
  exact moduleAbelianUnderivedExchange_compatibility Λ sq.toCommSq F

end AlgebraicGeometry.Etale
