/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusBaseChange
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import all WeilConjectures.CategoryTheory.RightDerivedBaseChangeSingleUnit

/-!
# Exact normalization of derived base change on represented maps

Source: the finite etale-origin transport paragraph of the current blueprint's
`cor-pur-affine-space-zero-section-purity.proof.md`.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
namespace CategoryTheory.Functor
section ExactSingle
variable {C C' : Type*} [Category C] [Category C'] [Abelian C] [Abelian C']
  [HasDerivedCategory C] [HasDerivedCategory C'] [EnoughInjectives C]
private theorem exactSingleUnit_normalization
    (L : C ⥤ C') [L.Additive] [PreservesFiniteLimits L] [PreservesFiniteColimits L]
    (X : C) :
    L.rightDerivedPlusSingleUnit X ≫
      L.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
        ((DerivedCategory.Plus.singleFunctor C 0).obj X) =
    (L.mapDerivedCategoryPlusSingleFunctor 0).inv.app X := by
  have ht := single_exact_transport L X
  simp only [singleTransport_hom, Functor.map_id, Category.id_comp,
    Category.comp_id, single_comparison] at ht
  have hf := congr_app L.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_fac
    ((HomotopyCategory.Plus.singleFunctor C 0).obj X)
  simp only [NatTrans.comp_app, whiskerLeft_app] at hf
  apply (cancel_mono ((L.mapDerivedCategoryPlusSingleFunctor 0).hom.app X)).1
  erw [Iso.inv_hom_id_app]
  simp only [Category.assoc]
  change ((L.mapHomotopyCategoryPlusSingleFunctorQhObjIso 0 X).inv ≫
    L.rightDerivedFunctorPlusUnit.app _ ≫ L.rightDerivedFunctorPlus.map
      (singleTransport C X).hom) ≫ _ ≫ _ = _
  rw [singleTransport_hom, Functor.map_id]
  erw [Category.comp_id]
  simp only [Category.assoc]
  erw [reassoc_of% hf, ht]
  erw [Iso.inv_hom_id_app_assoc, Iso.inv_hom_id]
  rfl

end ExactSingle

section Compatibility
variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D]
  [EnoughInjectives C] [HasKInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
private theorem exact_compat :
    whiskerRight F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom DerivedCategory.Plus.ι ≫
      F.mapDerivedCategoryPlusCompatibility.hom =
    F.rightDerivedFunctorPlusCompatibility.hom ≫
      whiskerLeft DerivedCategory.Plus.ι F.rightDerivedFunctorIsoMapDerivedCategory.hom := by
  apply Functor.rightDerived_ext (F.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)
    F.rightDerivedFunctorPlusιUnit (HomotopyCategory.Plus.quasiIso C)
  ext K
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
  have hp := congr_app F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus_hom_fac K
  simp only [NatTrans.comp_app, whiskerLeft_app] at hp
  have hc : F.rightDerivedFunctorPlusιUnit.app K ≫
      F.rightDerivedFunctorPlusCompatibility.hom.app (DerivedCategory.Plus.Qh.obj K) =
      F.ιRightDerivedFunctorUnit.app K := by
    simp [rightDerivedFunctorPlusCompatibility]
  have hu := congr_app F.rightDerivedFunctorIsoMapDerivedCategory_hom_fac K.obj
  simp only [NatTrans.comp_app, whiskerLeft_app] at hu
  change DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K) ≫
      DerivedCategory.Plus.ι.map
        (F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app _) ≫
      F.mapDerivedCategoryPlusCompatibility.hom.app _ = _
  rw [← DerivedCategory.Plus.ι.map_comp_assoc, hp]
  rw [← Category.assoc, hc]
  change _ = F.rightDerivedFunctorUnit.app K.obj ≫ _
  erw [hu]
  simp only [mapDerivedCategoryPlusCompatibility, Iso.refl_hom, NatTrans.id_app]
  have hf := F.ι_map_mapDerivedCategoryPlusFactorsh_hom_app K
  erw [Category.comp_id]
  apply (cancel_mono (F.mapDerivedCategoryFactorsh.hom.app K.obj)).1
  erw [← hf, ← Functor.map_comp, Iso.inv_hom_id_app, Functor.map_id]
  erw [hf, Iso.inv_hom_id_app]
  rfl

private theorem exact_compat_hom (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map
      (F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app K) =
    F.rightDerivedFunctorPlusCompatibility.hom.app K ≫
      F.rightDerivedFunctorIsoMapDerivedCategory.hom.app K.obj := by
  have h := congr_app (exact_compat F) K
  simp only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
    mapDerivedCategoryPlusCompatibility, Iso.refl_hom, NatTrans.id_app] at h
  erw [Category.comp_id] at h
  exact h

private theorem exact_compat_inv (K : DerivedCategory.Plus C) :
    DerivedCategory.Plus.ι.map
      (F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app K) =
    F.rightDerivedFunctorIsoMapDerivedCategory.inv.app K.obj ≫
      F.rightDerivedFunctorPlusCompatibility.inv.app K := by
  have hi : DerivedCategory.Plus.ι.mapIso
      (F.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.app K) =
      F.rightDerivedFunctorPlusCompatibility.app K ≪≫
        F.rightDerivedFunctorIsoMapDerivedCategory.app K.obj :=
    Iso.ext (exact_compat_hom F K)
  exact congrArg Iso.inv hi

omit [EnoughInjectives C] [HasKInjectiveResolutions C] in
private theorem included_single_inv (Y : C) :
    DerivedCategory.Plus.ι.map ((F.mapDerivedCategoryPlusSingleFunctor 0).inv.app Y) =
      (F.mapDerivedCategorySingleFunctor 0).inv.app Y := by
  have hi : DerivedCategory.Plus.ι.mapIso
      ((F.mapDerivedCategoryPlusSingleFunctor 0).app Y) =
      (F.mapDerivedCategorySingleFunctor 0).app Y :=
    Iso.ext (F.ι_map_mapDerivedCategoryPlusSingleFunctor_hom_app 0 Y)
  exact congrArg Iso.inv hi

omit [EnoughInjectives C] [HasKInjectiveResolutions C] in
private theorem included_exact_map {K L : DerivedCategory.Plus C} (f : K ⟶ L) :
    DerivedCategory.Plus.ι.map (F.mapDerivedCategoryPlus.map f) =
      F.mapDerivedCategory.map (DerivedCategory.Plus.ι.map f) := rfl

end Compatibility

section BaseChange
variable {B B' C C' : Type*} [Category* B] [Category* B'] [Category* C] [Category* C']
  [Abelian B] [Abelian B'] [Abelian C] [Abelian C']
  [HasDerivedCategory B] [HasDerivedCategory B'] [HasDerivedCategory C] [HasDerivedCategory C']
  [EnoughInjectives B] [EnoughInjectives B']
  (G : B ⥤ C) (G' : B' ⥤ C') (β : B ⥤ B') (γ : C ⥤ C')
  [G.Additive] [G'.Additive] [β.Additive] [γ.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
  [PreservesFiniteLimits β] [PreservesFiniteColimits β]
  [PreservesFiniteLimits γ] [PreservesFiniteColimits γ]
private theorem exact_bc_single (e : G ⋙ γ ⟶ β ⋙ G') (Y : B) :
    γ.mapDerivedCategoryPlus.map ((G.mapDerivedCategoryPlusSingleFunctor 0).inv.app Y) ≫
      γ.mapDerivedCategoryPlus.map
        (G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app
          ((DerivedCategory.Plus.singleFunctor B 0).obj Y)) ≫
      (rightDerivedFunctorPlusBaseChange e).app
        ((DerivedCategory.Plus.singleFunctor B 0).obj Y) ≫
      G'.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
        (β.mapDerivedCategoryPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj Y)) =
    (γ.mapDerivedCategoryPlusSingleFunctor 0).hom.app (G.obj Y) ≫
      (DerivedCategory.Plus.singleFunctor C' 0).map (e.app Y) ≫
      (G'.mapDerivedCategoryPlusSingleFunctor 0).inv.app (β.obj Y) ≫
      G'.mapDerivedCategoryPlus.map
        ((β.mapDerivedCategoryPlusSingleFunctor 0).inv.app Y) := by
  have h := rightDerivedBaseChange_single_unit e Y
  have hG := exactSingleUnit_normalization G Y
  have hG' := exactSingleUnit_normalization G' (β.obj Y)
  have hu : G.rightDerivedPlusSingleUnit Y =
      (G.mapDerivedCategoryPlusSingleFunctor 0).inv.app Y ≫
        G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app
          ((DerivedCategory.Plus.singleFunctor B 0).obj Y) := by
    rw [← hG, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [hu, Functor.map_comp] at h
  have hh := congrArg (fun t ↦ t ≫
    G'.rightDerivedFunctorPlus.map ((β.mapDerivedCategoryPlusSingleFunctor 0).inv.app Y) ≫
    G'.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
      (β.mapDerivedCategoryPlus.obj ((DerivedCategory.Plus.singleFunctor B 0).obj Y))) h
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.hom_inv_id_app] at hh
  have hn := G'.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.naturality
    ((β.mapDerivedCategoryPlusSingleFunctor 0).inv.app Y)
  erw [hn, reassoc_of% hG'] at hh
  erw [Functor.map_id, Category.id_comp] at hh
  simpa only [Functor.map_comp, Category.assoc] using hh

private theorem exact_bc_represented (e : G ⋙ γ ⟶ β ⋙ G') (Y : B)
    (K : DerivedCategory.Plus B)
    (b : (DerivedCategory.Plus.singleFunctor B 0).obj Y ⟶ K) :
    (γ.mapDerivedCategoryPlusSingleFunctor 0).inv.app (G.obj Y) ≫
      γ.mapDerivedCategoryPlus.map
        ((G.mapDerivedCategoryPlusSingleFunctor 0).inv.app Y ≫
          G.mapDerivedCategoryPlus.map b) ≫
      γ.mapDerivedCategoryPlus.map
        (G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv.app K) ≫
      (rightDerivedFunctorPlusBaseChange e).app K ≫
      G'.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom.app
        (β.mapDerivedCategoryPlus.obj K) =
    (DerivedCategory.Plus.singleFunctor C' 0).map (e.app Y) ≫
      (G'.mapDerivedCategoryPlusSingleFunctor 0).inv.app (β.obj Y) ≫
      G'.mapDerivedCategoryPlus.map
        ((β.mapDerivedCategoryPlusSingleFunctor 0).inv.app Y ≫
          β.mapDerivedCategoryPlus.map b) := by
  let δ : G.mapDerivedCategoryPlus ⋙ γ.mapDerivedCategoryPlus ⟶
      β.mapDerivedCategoryPlus ⋙ G'.mapDerivedCategoryPlus :=
    whiskerRight G.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.inv
        γ.mapDerivedCategoryPlus ≫
      rightDerivedFunctorPlusBaseChange e ≫
      whiskerLeft β.mapDerivedCategoryPlus
        G'.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus.hom
  have hs :
      (γ.mapDerivedCategoryPlusSingleFunctor 0).inv.app (G.obj Y) ≫
        γ.mapDerivedCategoryPlus.map ((G.mapDerivedCategoryPlusSingleFunctor 0).inv.app Y) ≫
        δ.app ((DerivedCategory.Plus.singleFunctor B 0).obj Y) =
      (DerivedCategory.Plus.singleFunctor C' 0).map (e.app Y) ≫
        (G'.mapDerivedCategoryPlusSingleFunctor 0).inv.app (β.obj Y) ≫
        G'.mapDerivedCategoryPlus.map
          ((β.mapDerivedCategoryPlusSingleFunctor 0).inv.app Y) := by
    dsimp only [δ, NatTrans.comp_app, whiskerRight_app, whiskerLeft_app]
    rw [exact_bc_single G G' β γ e Y]
    rw [Iso.inv_hom_id_app_assoc]
  have hn := δ.naturality b
  dsimp only [Functor.comp_map] at hn
  change _ ≫ _ ≫ δ.app K = _
  simp only [Functor.map_comp, Category.assoc]
  erw [hn, reassoc_of% hs]

variable [HasKInjectiveResolutions B] [HasKInjectiveResolutions B']
/-- Exact single normalization of canonical derived base change on a represented map.

Source: current blueprint, `cor-pur-affine-space-zero-section-purity.proof.md`,
finite etale-origin transport of composition and counits.
(blueprint: lem-pur-exact-base-change-single-normalization).

Proof: the exact-derived unit factorization identifies the single augmentation followed
by the exact-derived comparison with the inverse exact single comparison. Substitute
this in `rightDerivedBaseChange_single_unit`, then use naturality of the exact-derived
comparison to obtain the normalized equation on single objects. Conjugating the
base-change transformation by the exact-derived isomorphisms gives a natural
transformation of exact derived functors; naturality on `b` proves the equation in D+.
Right-derived extensionality identifies the included D+ exact comparison with the
Plus/unbounded comparison followed by the unbounded exact comparison. Include the D+
equation and substitute this compatibility and the included single comparisons. -/
theorem exactBaseChange_represented_unbounded (e : G ⋙ γ ⟶ β ⋙ G') (Y : B)
    (K : DerivedCategory.Plus B)
    (b : (DerivedCategory.Plus.singleFunctor B 0).obj Y ⟶ K) :
    (γ.mapDerivedCategorySingleFunctor 0).inv.app (G.obj Y) ≫
      γ.mapDerivedCategory.map
        ((G.mapDerivedCategorySingleFunctor 0).inv.app Y ≫
          G.mapDerivedCategory.map (DerivedCategory.Plus.ι.map b)) ≫
      γ.mapDerivedCategory.map (G.rightDerivedFunctorIsoMapDerivedCategory.inv.app K.obj) ≫
      γ.mapDerivedCategory.map (G.rightDerivedFunctorPlusCompatibility.inv.app K) ≫
      DerivedCategory.Plus.ι.map ((rightDerivedFunctorPlusBaseChange e).app K) ≫
      G'.rightDerivedFunctorPlusCompatibility.hom.app (β.mapDerivedCategoryPlus.obj K) ≫
      G'.rightDerivedFunctorIsoMapDerivedCategory.hom.app
        (β.mapDerivedCategory.obj K.obj) =
    (DerivedCategory.singleFunctor C' 0).map (e.app Y) ≫
      (G'.mapDerivedCategorySingleFunctor 0).inv.app (β.obj Y) ≫
      G'.mapDerivedCategory.map
        ((β.mapDerivedCategorySingleFunctor 0).inv.app Y ≫
          β.mapDerivedCategory.map (DerivedCategory.Plus.ι.map b)) := by
  have h := congrArg DerivedCategory.Plus.ι.map (exact_bc_represented G G' β γ e Y K b)
  simp only [Functor.map_comp, included_exact_map, included_single_inv,
    exact_compat_inv, exact_compat_hom] at h
  simp only [Functor.map_comp, Category.assoc] at h ⊢
  convert h using 1 <;> rfl
end BaseChange
end CategoryTheory.Functor
